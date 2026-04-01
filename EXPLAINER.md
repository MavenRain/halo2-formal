# LookupRangeCheck Gadget: Formal Verification Explainer

## What is LookupRangeCheck?

The LookupRangeCheck gadget is one of five core circuit components in
Zcash's Orchard shielded protocol.  Its job is deceptively simple:
given a field element `v` and a target bit-width `n`, prove that
`0 <= v < 2^n`.  Range checks appear everywhere in Orchard: ensuring
note values fit in 64 bits, constraining Sinsemilla message chunks to
10 bits, and bounding Merkle tree layer indices.

A bug here would be catastrophic.  If an adversary can bypass a range
check, they could forge note values (creating money from nothing) or
break Merkle path verification (spending notes they do not own).

## How the gadget works

### Full range check (running sum)

To check `v < 2^{K*w}` where `K = 10` (the Sinsemilla constant), the
gadget decomposes `v` into `w` "words" of `K` bits each using a
running sum:

```
z_0 = v
z_{i+1} = (z_i - a_i) / 2^K      for i = 0, ..., w-1
z_w = 0                             (strict mode)
```

Each word `a_i = z_i - 2^K * z_{i+1}` is constrained to lie in
`{0, 1, ..., 2^K - 1}` via a lookup table.  This forces:

```
v = a_0 + 2^K * a_1 + 2^{2K} * a_2 + ... + 2^{(w-1)K} * a_{w-1}
```

with each `a_i < 2^K`, so `v < 2^{K*w}`.

### Short range check (sub-word)

For `s < K` bits (e.g., checking a 3-bit value), the gadget uses a
shift-and-lookup trick:

1. Look up `e` in the table (proves `e < 2^K`)
2. Look up `e * 2^{K-s}` in the table (proves `e * 2^{K-s} < 2^K`)

From (2): `e < 2^K / 2^{K-s} = 2^s`.  The first lookup prevents a
modular wrap-around attack: without it, a large field element could
have its shifted value land back in `[0, 2^K)` after wrapping mod `p`.

## What we prove

### Soundness

"If the circuit accepts, the claimed range bound holds."

- **Running sum** (`soundness_runsum`): If a strict decomposition into
  `w` base-`b` words exists (all lookups pass, `z_w = 0`), then
  `v < b^w`.

- **Short check** (`soundness_short`): If both lookups pass, then
  `e < 2^s`.

### Completeness

"Every valid witness can satisfy the circuit constraints."

- **Running sum** (`completeness_runsum`): For any `v < b^w`, the
  standard base-`b` representation provides a valid witness.

- **Short check** (`completeness_short`): For any `e < 2^s` with
  `s <= K`, both lookup constraints hold.

### No-wrap guarantee

`halo2_short_no_wrap` proves that for the Pallas field (characteristic
`p ~ 2^254`), the multiplication `e * 2^{K-s}` never overflows mod `p`,
ensuring the natural-number reasoning applies to actual field elements.

## Proof strategy

The proofs are elementary number theory, which is appropriate: the
gadget's correctness should reduce to basic facts about positional
number systems.

1. We define `evalDigits` (base-`b` evaluation) and `baseDecomp`
   (standard base-`b` decomposition) as recursive functions.

2. Soundness follows from the observation that a sum of `w` terms, each
   less than `b`, weighted by powers of `b`, is less than `b^w`.  The
   key step multiplies the inductive hypothesis by `b` and adds the
   bounded digit.

3. Completeness is constructive: the witness is the standard `mod`/`div`
   decomposition, and correctness follows from `v = (v % b) + b * (v / b)`.

4. The short range check reduces to cancelling a positive factor from
   both sides of an inequality, after rewriting `2^K = 2^s * 2^{K-s}`.

## Connection to the grant

This formalization targets the simplest of the five Halo 2 gadgets named
in the Zcash Community Grants proposal (issue #244):

1. Sinsemilla hash
2. Poseidon/Pow5 chip
3. ECC gadget
4. MerklePath gadget
5. **LookupRangeCheck** (this file)

LookupRangeCheck is the natural starting point because it has no
dependencies on the other gadgets, uses no curve arithmetic or hash
internals, and provides foundational range-checking infrastructure that
the other gadgets rely on.  The techniques demonstrated here (defining
circuit constraint semantics as Lean functions, proving soundness via
induction on the decomposition structure, proving completeness by
constructing witnesses) generalize directly to the remaining gadgets.
