module

public import Erdos326.Closure
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.Filter.Cofinite

@[expose] public section

open Filter Topology
open scoped Pointwise

namespace Erdos326

/-- Equivalence with the order-two specialization of the definition used by
    Formal Conjectures, expressed with the cofinite filter and pointwise sums. -/
theorem asymptotic_basis_iff_cofinite_sum (A : Set ℕ) :
    IsAsymptoticBasisOrder2 A ↔ ∀ᶠ n in cofinite, n ∈ (2 : ℕ) • A := by
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  simp only [IsAsymptoticBasisOrder2, two_nsmul, Set.mem_add]

/-- Erdős #326 with the Formal Conjectures predicate unfolded. -/
theorem erdos_326_cofinite :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      Minimal (fun A : Set ℕ => ∀ᶠ n in cofinite, n ∈ (2 : ℕ) • A) (Set.range a) ∧
      ∃ c : ℝ, c ≠ 0 ∧ Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  have h : IsAsymptoticBasisOrder2 =
      (fun A : Set ℕ => ∀ᶠ n in cofinite, n ∈ (2 : ℕ) • A) :=
    funext fun A => propext (asymptotic_basis_iff_cofinite_sum A)
  rw [← h]
  exact erdos_326

end Erdos326
