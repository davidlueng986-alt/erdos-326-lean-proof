module

public import Erdos326.Statement

@[expose] public section

open Filter Topology
open scoped Pointwise

namespace Erdos326

/-- Erdős Problem 326 asks whether a minimal asymptotic additive basis of
order two can have a nonzero quadratic limit. Cofinite membership in
`(2 : ℕ) • A` means that every sufficiently large natural is a sum of two
(not necessarily distinct) elements of `A`. Minimality is under inclusion. -/
theorem palomar_erdos_326 :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      Minimal (fun A : Set ℕ => ∀ᶠ n in cofinite, n ∈ (2 : ℕ) • A) (Set.range a) ∧
      ∃ c : ℝ, c ≠ 0 ∧ Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  exact erdos_326_cofinite

end Erdos326
