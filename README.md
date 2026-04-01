# halo2-formal

Formal verification of Halo 2 circuit gadgets in Lean 4, targeting the
Zcash Orchard shielded protocol.

## Status

**LookupRangeCheck** gadget: soundness and completeness proved.

See `EXPLAINER.md` for a detailed walkthrough of the gadget, the proof
strategy, and how this connects to the broader formalization effort.

## Structure

```
Halo2Formal/
  LookupRangeCheck.lean   -- Main formalization: definitions and proofs
EXPLAINER.md              -- Non-technical explainer
```

### Main results (`Halo2Formal.LookupRangeCheck`)

| Theorem | Statement |
|---------|-----------|
| `soundness_runsum` | Strict running-sum decomposition implies `v < b^w` |
| `completeness_runsum` | `v < b^w` implies a valid decomposition exists |
| `soundness_short` | Both short-check lookups pass implies `e < 2^s` |
| `completeness_short` | `e < 2^s` implies both lookups pass |
| `halo2_short_no_wrap` | Field multiplication does not wrap for Pallas |

## Building

Requires Lean 4 and Mathlib.  After cloning:

```sh
lake update    # fetch Mathlib (first build takes a while)
lake build
```

If the `lean-toolchain` version does not match Mathlib's current
toolchain, run `lake update` to sync, or manually set `lean-toolchain`
to match the version in Mathlib's repository.

## License

Dual-licensed under MIT OR Apache-2.0 at your option.

## Context

This work supports the Zcash Community Grants proposal
"Formal Verification of Halo 2 in Lean 4"
([ZcashCommunityGrants/zcashcommunitygrants#244](https://github.com/ZcashCommunityGrants/zcashcommunitygrants/issues/244)).
