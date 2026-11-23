# Erdős Problem 326 · JSP-000272

The entry point is `Erdos326.erdos_326` in [Erdos326/Closure.lean](Erdos326/Closure.lean).
It proves the existence of a minimal asymptotic additive basis of order two
whose strictly increasing enumeration has a nonzero quadratic limit. The companion theorem
`Erdos326.erdos_326_fixed_limit` gives the limit `1 / 10000`.

## Reproduce the verification

The Lean toolchain and all Lake dependencies are pinned. From this directory, use:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Erdos326.lean
```

The three audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
The build was reproduced from a clean project directory with the pinned Mathlib cache.
[Erdos326/Statement.lean](Erdos326/Statement.lean) checks the statement with the
cofinite pointwise-sum predicate from
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/2207c54d0dbe960de591d280f997b195bf3f6e28/FormalConjectures/ErdosProblems/326.lean).

## Construction

The proof develops the two coprime Cassels bases from the
[original manuscript](../proof/PROOF.md). It fills groups of three
quadratic bins and chooses an odd target in an already filled finite background.
The deleted endpoints are replaced within their own bins before the witness and
the remaining bounded number of repairs are inserted. This keeps the running
counts within a uniform additive error. Nested frozen prefixes and the
dovetailing schedule then produce the full infinite basis.

| Source | Verified result |
| --- | --- |
| `Cassels.lean`, `Spacing.lean` | Coverage by nearby blocks and sparsity in each group of three bins |
| `Collateral.lean` | Uniform bound on sums that lose both selected representations |
| `Witness.lean`, `Stage.lean` | Odd target selection, endpoint replacement, and witness-preserving repairs |
| `Bins.lean`, `LocalCount.lean`, `Initial.lean` | Filling, local availability, and initialization |
| `Assembly.lean`, `Reduction.lean` | Infinite assembly, minimality, and the quadratic limit |
| `Closure.lean` | Stage extension with all premises discharged and the unconditional theorem |
