module

public import Erdos326.Reduction
public import Mathlib.Data.Nat.Pairing

@[expose] public section

open Filter Topology

namespace Erdos326

/-- A finite set with certified coverage and counting bounds through a complete bin. -/
structure FinitePrefix (m₀ E : ℕ) where
  index : ℕ
  points : Finset ℕ
  index_ge : m₀ ≤ index
  bounded : ∀ x ∈ points, x ≤ quadBin index
  coverage : ∀ n ≤ quadBin index, ∃ x ∈ points, ∃ y ∈ points, x + y = n
  counts : ∀ j, m₀ ≤ j → j ≤ index →
    j ≤ (points.filter (· ≤ quadBin j)).card ∧
    (points.filter (· ≤ quadBin j)).card ≤ j + E

variable {m₀ E : ℕ}

def FinitePrefix.Extends (p q : FinitePrefix m₀ E) : Prop :=
  p.index < q.index ∧
  ∀ x ≤ quadBin p.index, x ∈ q.points ↔ x ∈ p.points

def FinitePrefix.HasWitness (p : FinitePrefix m₀ E) (a lower : ℕ) : Prop :=
  ∃ n, lower ≤ n ∧ n ≤ quadBin p.index ∧
    ∀ x ∈ p.points, ∀ y ∈ p.points, x + y = n → x = a ∨ y = a

lemma FinitePrefix.zero_mem (p : FinitePrefix m₀ E) : 0 ∈ p.points := by
  obtain ⟨x, hx, y, _, hxy⟩ := p.coverage 0 (Nat.zero_le _)
  rwa [show x = 0 by omega] at hx

lemma FinitePrefix.Extends.subset {p q : FinitePrefix m₀ E} (h : p.Extends q) :
    p.points ⊆ q.points := by
  intro x hx
  exact (h.2 x (p.bounded x hx)).2 hx

lemma quadBin_monotone : Monotone quadBin := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.pow_le_pow_left hij 2)

lemma quadBin_cofinal (x : ℕ) : x ≤ quadBin (10000 * (x + 1)) := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 10000)).2
  nlinarith

private lemma infinite_of_basis {C : Set ℕ} (h : IsAsymptoticBasisOrder2 C) : C.Infinite := by
  intro hfinite
  obtain ⟨B, hB⟩ := Set.finite_iff_bddAbove.mp hfinite
  obtain ⟨N, hN⟩ := h
  obtain ⟨x, hx, y, hy, hxy⟩ := hN (N + 2 * B + 1) (by omega)
  have hxB : x ≤ B := hB hx
  have hyB : y ≤ B := hB hy
  omega

/-- A valid finite extension at every stage suffices to construct the desired infinite set.
    The validity predicate can carry auxiliary invariants specific to the extension proof. -/
theorem exists_of_prefix_extensions (Valid : FinitePrefix m₀ E → Prop)
    (initial : FinitePrefix m₀ E) (hinit : Valid initial)
    (advance : ∀ p, Valid p → ∀ a ∈ p.points, ∃ q, Valid q ∧
      p.Extends q ∧ q.HasWitness a (quadBin p.index + 1)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ Minimal IsAsymptoticBasisOrder2 (Set.range a) ∧
      Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 (1 / 10000 : ℝ)) := by
  classical
  let Active := {p : FinitePrefix m₀ E // Valid p}
  have chooseStep (p : Active) (a : ℕ) :
      ∃ q : Active, p.val.Extends q.val ∧
        (a ∈ p.val.points → q.val.HasWitness a (quadBin p.val.index + 1)) := by
    by_cases ha : a ∈ p.val.points
    · obtain ⟨q, hq, he, hw⟩ := advance p.val p.property a ha
      exact ⟨⟨q, hq⟩, he, fun _ => hw⟩
    · obtain ⟨q, hq, he, _⟩ := advance p.val p.property 0 p.val.zero_mem
      exact ⟨⟨q, hq⟩, he, fun h => (ha h).elim⟩
  let stages : ℕ → Active := fun k =>
    Nat.rec ⟨initial, hinit⟩
      (fun j p => (chooseStep p (Nat.unpair j).1).choose) k
  let p (k : ℕ) : FinitePrefix m₀ E := (stages k).val
  let cutoff (k : ℕ) : ℕ := quadBin (p k).index
  have hstep (k : ℕ) : (p k).Extends (p (k + 1)) ∧
      ((Nat.unpair k).1 ∈ (p k).points →
        (p (k + 1)).HasWitness (Nat.unpair k).1 (cutoff k + 1)) :=
    (chooseStep (stages k) (Nat.unpair k).1).choose_spec
  have hindex : StrictMono (fun k => (p k).index) :=
    strictMono_nat_of_lt_succ fun k => (hstep k).1.1
  have hcut : Monotone cutoff := quadBin_monotone.comp hindex.monotone
  have hlarge (x : ℕ) : x ≤ cutoff (10000 * (x + 1)) :=
    (quadBin_cofinal x).trans (quadBin_monotone (hindex.id_le _))
  have hmono : Monotone (fun k => (p k).points) :=
    monotone_nat_of_le_succ fun k => (hstep k).1.subset
  have hfreeze (i j : ℕ) (hij : i ≤ j) (x : ℕ) (hx : x ≤ cutoff i)
      (hm : x ∈ (p j).points) : x ∈ (p i).points := by
    induction j, hij using Nat.le_induction with
    | base => exact hm
    | succ j hij ih =>
      exact ih (((hstep j).1.2 x (hx.trans (hcut hij))).1 hm)
  let C : Set ℕ := ⋃ k : ℕ, (↑(p k).points : Set ℕ)
  have hmem (x k : ℕ) (hx : x ≤ cutoff k) : x ∈ C ↔ x ∈ (p k).points := by
    constructor
    · intro hxC
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxC
      by_cases hik : i ≤ k
      · exact hmono hik hi
      · exact hfreeze k i (by omega) x hx hi
    · intro hxP
      exact Set.mem_iUnion.mpr ⟨k, hxP⟩
  have hb : IsAsymptoticBasisOrder2 C := by
    refine ⟨0, fun n _ => ?_⟩
    let k := 10000 * (n + 1)
    obtain ⟨x, hx, y, hy, hxy⟩ := (p k).coverage n (hlarge n)
    exact ⟨x, (hmem x k ((p k).bounded x hx)).2 hx,
      y, (hmem y k ((p k).bounded y hy)).2 hy, hxy⟩
  have hi : C.Infinite := infinite_of_basis hb
  have hw : ∀ a ∈ C, ∀ M : ℕ, ∃ n ≥ M,
      ∀ x ∈ C, ∀ y ∈ C, x + y = n → x = a ∨ y = a := by
    intro a ha M
    obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
    let k := Nat.pair a (max i (10000 * (M + 1)))
    have hik : i ≤ k := (le_max_left _ _).trans (Nat.right_le_pair _ _)
    have hMk : 10000 * (M + 1) ≤ k := (le_max_right _ _).trans (Nat.right_le_pair _ _)
    have hk : (Nat.unpair k).1 = a := by simp [k]
    have hak : a ∈ (p k).points := hmono hik hai
    have h := (hstep k).2
    rw [hk] at h
    obtain ⟨n, hl, hu, hn⟩ := h hak
    refine ⟨n, (hlarge M).trans ((hcut hMk).trans (by omega)), ?_⟩
    intro x hx y hy hxy
    have hxc : x ≤ cutoff (k + 1) := by
      change n ≤ cutoff (k + 1) at hu
      omega
    have hyc : y ≤ cutoff (k + 1) := by
      change n ≤ cutoff (k + 1) at hu
      omega
    exact hn x ((hmem x (k + 1) hxc).1 hx) y ((hmem y (k + 1) hyc).1 hy) hxy
  have hcount (j : ℕ) (hj : m₀ ≤ j) :
      j ≤ Nat.count (· ∈ C) (quadBin j + 1) ∧
      Nat.count (· ∈ C) (quadBin j + 1) ≤ j + E := by
    have hjp : j ≤ (p j).index := hindex.id_le j
    have hf : (Finset.range (quadBin j + 1)).filter (· ∈ C) =
        (p j).points.filter (· ≤ quadBin j) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      rw [Nat.lt_succ_iff]
      constructor
      · rintro ⟨hx, hxC⟩
        exact ⟨(hmem x j (hx.trans (quadBin_monotone hjp))).1 hxC, hx⟩
      · rintro ⟨hxP, hx⟩
        exact ⟨hx, (hmem x j (hx.trans (quadBin_monotone hjp))).2 hxP⟩
    rw [Nat.count_eq_card_filter_range, hf]
    exact (p j).counts j hj hjp
  exact exists_of_stage_properties C hi m₀ E hb hw hcount

end Erdos326
