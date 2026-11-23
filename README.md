# Erdős Problem #326 : a minimal asymptotic basis of order 2 with a_k / k^2 -> 1/10000

**Statement.** Does there exist a set A = {a_1 < a_2 < ...} of natural numbers that is a *minimal* asymptotic additive basis of order 2 (every sufficiently large integer is a sum of two elements of A, and no proper subset of A has this property) such that a_k / k^2 tends to a nonzero constant c? Erdős and Graham (1980) conjectured the answer is no. ([Erdős Problem #326](https://erdosproblemaday.com/problem/326); Justin Sun Prize catalog ID `JSP-000272`.)

**Result.** Yes. This repository provides a proof, together with a Lean 4 formalization, that there is an explicit infinite set C' of positive integers with C' + C' = N_{>=2}, C' minimal, and lim c'_k / k^2 = 1/10000 > 0 (in fact c'_k = k^2/10000 + O(k)). This refutes the Erdős–Graham conjecture.

Author: Liang Wan Yiu David

## Construction in brief

1. Two coprime prime-step Cassels bases A^(1), A^(2) (primes from Bertrand's postulate in disjoint dyadic windows), each an exact basis of order 2.
2. Gap and scale bounds showing the union A has consecutive gaps > sqrt(a)/10, far larger than the quadratic bin length near a.
3. A running-count rule on quadratic bins (b_m = floor(m^2 / 10000)) that keeps |C ∩ [0, b_m]| within a bounded excess of m.
4. A stage-by-stage construction: at stage r an odd target N_r is chosen by an averaging argument so that, after removing a bounded set D_r from A, N_r has exactly one representation {x_r, N_r - x_r} in C + C. Every element of C is the witness x_r at infinitely many stages, giving minimality. Collateral holes (at most M_max per stage) are patched without disturbing earlier targets.
5. Shift by +1 to land in the positive integers.

The manuscript is in [`proof/PROOF.md`](proof/PROOF.md).

## Lean formalization

The Lean 4 + Mathlib project in [`lean/`](lean/) proves `Erdos326.erdos_326` (existence of a minimal asymptotic basis of order 2 whose enumeration has a nonzero quadratic limit), the companion `Erdos326.erdos_326_fixed_limit` (limit `1/10000`), and the equivalent cofinite pointwise-sum statement used by [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/2207c54d0dbe960de591d280f997b195bf3f6e28/FormalConjectures/ErdosProblems/326.lean). The three theorems depend only on `propext`, `Classical.choice` and `Quot.sound` under Lean 4.36.0 with a pinned Mathlib revision (see [`lean/README.md`](lean/README.md) and [`VERIFICATION.md`](VERIFICATION.md)). The Lean project is the reference version of the argument; it refines the manuscript's construction at the stage boundaries.

The proof uses Cassels's theorem on prime-step bases ([Nathanson, *Cassels Bases*, Thm. 6](http://www.theoryofnumbers.com/melnathanson/pdfs/nath2010-138.pdf)); its hypotheses are checked in Step 1 of the manuscript and in `Cassels.lean` and `Spacing.lean`.

## Repository layout

| Path | Contents |
| --- | --- |
| `lean/` | Lean 4 + Mathlib formalization of the full result (entry point `Erdos326/Closure.lean`); pinned toolchain and Mathlib |
| `proof/PROOF.md` | Manuscript of the proof |
| `VERIFICATION.md` | Lean verification record and reproduction steps |
| `LICENSE`, this README's license note | MIT (code) / CC BY 4.0 (proof text) |
| `CITATION.cff` | Citation metadata |

## How to reproduce the Lean verification

Requires `elan` (the Lean toolchain is pinned in `lean/lean-toolchain`). From the `lean/` directory:

```bash
lake exe cache get
lake build
lake env lean -DwarningAsError=true Erdos326.lean
```

## Provenance

The Lean formalization was developed with AI assistance

## Licenses

- Lean code (`lean/`): [MIT](LICENSE)
- Proof text and this README (`proof/`, `README.md`): [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/legalcode)

## Citation

See [`CITATION.cff`](CITATION.cff).
