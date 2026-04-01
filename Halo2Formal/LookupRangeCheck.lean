import Mathlib.Tactic

/-!
# Halo 2 LookupRangeCheck Gadget -- Formal Verification

This file formalizes the LookupRangeCheck gadget from Zcash's Halo 2 proving
system, proving both soundness and completeness of:

1. **Running-sum range check**: decomposes a value `v` into `w` base-`b`
   digits and checks each lies in `[0, b)`.  In Halo 2, `b = 2^K` with
   `K = 10`.

2. **Short range check**: for `s < K`, checks `v` is in `[0, 2^s)` by
   verifying both `v` and `v * 2^(K - s)` lie in `[0, 2^K)`.

## Circuit correspondence

The running-sum decomposition in the circuit witnesses values
`z_0, z_1, ..., z_w` where `z_0 = v`.  At each step, the "word"
`z_i - 2^K * z_{i+1}` is constrained via a lookup table to lie in
`{0, 1, ..., 2^K - 1}`.  In strict mode, `z_w = 0` is enforced.

Our `StrictDecomp` structure captures exactly these constraints
over natural numbers.  The short range check uses two lookups plus a
bitshift gate; our theorems verify the underlying arithmetic.

## References

- `halo2_gadgets::utilities::lookup_range_check` (zcash/halo2)
- The Halo 2 Book, section on lookup arguments
- ZIP 224 (Orchard shielded protocol)
-/

set_option autoImplicit false

namespace Halo2Formal.LookupRangeCheck

-- ============================================================================
-- Part 1: Base Decomposition
-- ============================================================================

/-- Evaluate a list of base-`b` digits (least-significant first).

    `evalDigits b [a_0, a_1, ..., a_{n-1}] = a_0 + b*a_1 + b^2*a_2 + ...` -/
def evalDigits (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + b * evalDigits b ds

/-- Decompose `v` into `w` base-`b` digits (least-significant first).

    This mirrors the witness generation in the Halo 2 running-sum gadget:
    each digit is `v % b`, and the quotient `v / b` feeds the next step. -/
def baseDecomp (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | w + 1, v => (v % b) :: baseDecomp b w (v / b)

-- Simp lemmas for unfolding

@[simp] theorem evalDigits_nil {b : ℕ} : evalDigits b [] = 0 := rfl

@[simp] theorem evalDigits_cons {b : ℕ} (d : ℕ) (ds : List ℕ) :
    evalDigits b (d :: ds) = d + b * evalDigits b ds := rfl

@[simp] theorem baseDecomp_zero {b : ℕ} (v : ℕ) :
    baseDecomp b 0 v = [] := rfl

@[simp] theorem baseDecomp_succ {b : ℕ} (w v : ℕ) :
    baseDecomp b (w + 1) v = (v % b) :: baseDecomp b w (v / b) := rfl

/-- The length of `baseDecomp b w v` is exactly `w`. -/
theorem baseDecomp_length (b w v : ℕ) : (baseDecomp b w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [baseDecomp, ih]

/-- Every digit produced by `baseDecomp` is strictly less than `b`. -/
theorem mem_baseDecomp_lt {b : ℕ} (hb : 0 < b) {w v d : ℕ}
    (hd : d ∈ baseDecomp b w v) : d < b := by
  induction w generalizing v with
  | zero => simp at hd
  | succ w ih =>
    simp only [baseDecomp_succ, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt v hb
    · exact ih hd

/-- **Completeness lemma**: evaluating the base decomposition recovers the
    original value, provided `v < b^w`.

    This corresponds to the circuit's running-sum recurrence:
    `z_0 = a_0 + b * z_1 = a_0 + b * (a_1 + b * z_2) = ...` -/
theorem evalDigits_baseDecomp {b : ℕ} (hb : 0 < b) {w v : ℕ}
    (hv : v < b ^ w) : evalDigits b (baseDecomp b w v) = v := by
  induction w generalizing v with
  | zero =>
    simp [baseDecomp] at *
    omega
  | succ w ih =>
    simp only [baseDecomp_succ, evalDigits_cons]
    have hv' : v / b < b ^ w := by
      rw [Nat.div_lt_iff_lt_mul hb]
      rwa [← pow_succ]
    rw [ih hv']
    exact Nat.mod_add_div v b

/-- **Soundness lemma**: if every digit is less than `b`, the evaluated
    sum is strictly less than `b ^ (number of digits)`.

    This is the core argument that lookup-constraining each word to
    `[0, 2^K)` forces the reconstructed value below `2^{K * w}`. -/
theorem evalDigits_lt_pow {b : ℕ} (_ : 0 < b) {ds : List ℕ}
    (hds : ∀ d ∈ ds, d < b) : evalDigits b ds < b ^ ds.length := by
  induction ds with
  | nil => simp [evalDigits]
  | cons d ds ih =>
    simp only [evalDigits_cons, List.length_cons]
    have hd : d < b := hds d List.mem_cons_self
    have hds' : ∀ x ∈ ds, x < b := fun x hx => hds x (List.mem_cons_of_mem d hx)
    have ih' := ih hds'
    rw [pow_succ]
    -- Strategy: d + b*e < b*(e+1) ≤ b*b^n = b^n*b
    calc d + b * evalDigits b ds
        < b + b * evalDigits b ds := by omega
      _ = b * (evalDigits b ds + 1) := by ring
      _ ≤ b * b ^ ds.length := Nat.mul_le_mul_left b (by omega)
      _ = b ^ ds.length * b := by ring

-- ============================================================================
-- Part 2: Running-Sum Range Check
-- ============================================================================

/-- A strict running-sum decomposition of `v` into `w` base-`b` words.

    This captures the Halo 2 constraint system for `LookupRangeCheck`:
    - `words` are the K-bit chunks extracted at each running-sum step
    - `len_eq` ensures exactly `w` decomposition steps
    - `word_bound` encodes the lookup constraint (each word in `[0, b)`)
    - `eval_eq` ties the decomposition back to the original value

    In the circuit, `b = 2^K` and `z_w = 0` (strict mode), which
    together with the running-sum recurrence imply `eval_eq`. -/
structure StrictDecomp (b w v : ℕ) where
  words : List ℕ
  len_eq : words.length = w
  word_bound : ∀ d ∈ words, d < b
  eval_eq : evalDigits b words = v

/-- **Soundness of the running-sum range check.**

    If the circuit accepts (all lookups pass, `z_w = 0`), then `v < b^w`.

    For Halo 2 with `b = 2^K`, `K = 10`: `v < 2^{10w}`. -/
theorem soundness_runsum {b w v : ℕ} (hb : 0 < b)
    (d : StrictDecomp b w v) : v < b ^ w := by
  have h := evalDigits_lt_pow hb d.word_bound
  rwa [d.len_eq, d.eval_eq] at h

/-- **Completeness of the running-sum range check.**

    Every value below `b^w` has a valid decomposition that the circuit
    would accept.  The witness is the standard base-`b` representation. -/
def completeness_runsum {b w v : ℕ} (hb : 0 < b) (hv : v < b ^ w) :
    StrictDecomp b w v where
  words := baseDecomp b w v
  len_eq := baseDecomp_length b w v
  word_bound := fun _ hd => mem_baseDecomp_lt hb hd
  eval_eq := evalDigits_baseDecomp hb hv

-- ============================================================================
-- Part 3: Short Range Check
-- ============================================================================

/-- **Soundness of the short range check.**

    If `e` passes both lookups (`e < 2^K` and `e * 2^{K-s} < 2^K`),
    then `e < 2^s`.

    The argument: `2^K = 2^s * 2^{K-s}`, so the second lookup gives
    `e * 2^{K-s} < 2^s * 2^{K-s}`, and cancelling the positive factor
    `2^{K-s}` yields `e < 2^s`.

    Note: `_he_lookup` (the first lookup) is not needed for the pure
    natural-number argument.  In the actual circuit over a prime field,
    it prevents modular wrap-around; see `halo2_short_no_wrap` below. -/
theorem soundness_short {K s e : ℕ} (hs : s ≤ K)
    (_he_lookup : e < 2 ^ K) (he_shift : e * 2 ^ (K - s) < 2 ^ K) :
    e < 2 ^ s := by
  -- Rewrite 2^K as 2^s * 2^{K-s}
  have hpow : 2 ^ K = 2 ^ s * 2 ^ (K - s) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow] at he_shift
  -- Cancel the common factor 2^{K-s}
  by_contra h
  push Not at h
  have := Nat.mul_le_mul_right (2 ^ (K - s)) h
  linarith

/-- **Completeness of the short range check.**

    If `e < 2^s` and `s ≤ K`, both lookup constraints are satisfiable. -/
theorem completeness_short {K s e : ℕ} (hs : s ≤ K) (he : e < 2 ^ s) :
    e < 2 ^ K ∧ e * 2 ^ (K - s) < 2 ^ K := by
  constructor
  · -- e < 2^s ≤ 2^K since s ≤ K
    exact lt_of_lt_of_le he (Nat.pow_le_pow_right (by omega) hs)
  · -- e * 2^{K-s} < 2^s * 2^{K-s} = 2^K
    calc e * 2 ^ (K - s)
        < 2 ^ s * 2 ^ (K - s) :=
          mul_lt_mul_of_pos_right he (show 0 < 2 ^ (K - s) by positivity)
      _ = 2 ^ K := by rw [← pow_add]; congr 1; omega

-- ============================================================================
-- Part 4: Halo 2 Instantiation (K = 10, Pallas field)
-- ============================================================================

/-- The Halo 2 lookup table bit-width (the Sinsemilla constant). -/
def K : ℕ := 10

/-- The short range check multiplication never wraps in the Pallas field.

    Since `e < 2^K = 1024`, the product `e * 2^{K-s}` is at most
    `1023 * 1024 < 2^{20}`, far below the Pallas characteristic
    `p ~ 2^254`.  This lemma shows the natural-number reasoning in
    `soundness_short` transfers to field elements. -/
theorem halo2_short_no_wrap {p : ℕ} (hp : 2 ^ (2 * K) < p)
    {e : ℕ} (he : e < 2 ^ K) {s : ℕ} (_hs : s ≤ K) :
    e * 2 ^ (K - s) < p :=
  calc e * 2 ^ (K - s)
      < 2 ^ K * 2 ^ (K - s) :=
        mul_lt_mul_of_pos_right he (by positivity)
    _ ≤ 2 ^ K * 2 ^ K :=
        Nat.mul_le_mul_left (2 ^ K) (Nat.pow_le_pow_right (by omega) (Nat.sub_le K s))
    _ = 2 ^ (2 * K) := by rw [← pow_add]; congr 1
    _ < p := hp

/-- The standard Halo 2 range check equivalence.

    The running-sum gadget decomposes into `w` words of `K = 10` bits,
    so the effective range is `[0, (2^10)^w) = [0, 2^{10w})`. -/
theorem halo2_range_equiv (w v : ℕ) :
    v < (2 ^ K) ^ w ↔ v < 2 ^ (K * w) := by
  constructor <;> (intro h; rwa [← pow_mul] at *)

end Halo2Formal.LookupRangeCheck
