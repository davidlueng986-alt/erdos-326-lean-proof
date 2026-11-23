# Erdős #326 · JSP-000272 Lean verification

The [Lean project](lean/README.md) proves `Erdos326.erdos_326` without construction hypotheses and certifies the limit `1 / 10000`. It also checks the equivalent cofinite pointwise-sum statement from [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/2207c54d0dbe960de591d280f997b195bf3f6e28/FormalConjectures/ErdosProblems/326.lean). All three audited theorems depend only on `propext`, `Classical.choice`, and `Quot.sound` under Lean 4.36.0 with pinned Mathlib. The sources contain no `sorry`, `admit`, custom `axiom` or `native_decide`.

## Reproduce

Requires `elan`; the toolchain and Mathlib revision are pinned in `lean/`. From `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Erdos326.lean
```

## Relation to the manuscript

The Lean proof follows the construction in [`proof/PROOF.md`](proof/PROOF.md) with these refinements at the stage boundaries: the bin containing the witness target is completed before it is frozen, each final stage cutoff is rounded up to a bin boundary, and deleted endpoints are replaced within their own bins. Additions above the target cannot represent it, so the formal stage invariant does not rely on filler capacity in an arbitrarily short truncated bin.
