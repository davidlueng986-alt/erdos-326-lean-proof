module

public import Erdos326.Bins

@[expose] public section

open scoped BigOperators

namespace Erdos326

def windowCount (S : Finset ℕ) (u w : ℕ) : ℕ :=
  (S.filter (fun x => u ≤ x ∧ x ≤ u + w)).card

lemma binIndex_monotone : Monotone binIndex := by
  intro u v huv
  apply binIndex_le_iff.2
  exact huv.trans (binIndex_le_iff.1 le_rfl)

private lemma coarseEdge_jump {i j d : ℕ} (hi : 1000 * (d + 1) ≤ i) (hij : i ≤ j) :
    coarseEdge i + (j - i) * d ≤ coarseEdge j := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    have h := coarseEdge_width_ge (i := j) (d := d) (hi.trans hj)
    have hr : (j + 1 - i) * d = (j - i) * d + d := by
      rw [show j + 1 - i = j - i + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [hr]
    omega

private lemma window_bins {u w x J d : ℕ} (hd : 0 < d) (hj : 1000 * (d + 1) ≤ J)
    (hu : u ≤ x) (hw : x ≤ u + w) (hx : coarseEdge J < x) :
    let i := max (binIndex u) (J + 1)
    i ≤ binIndex x ∧ binIndex x ≤ i + w / d + 1 := by
  let i := max (binIndex u) (J + 1)
  have hlo₁ : binIndex u ≤ binIndex x := binIndex_monotone hu
  have hlo₂ : J + 1 ≤ binIndex x := by
    by_contra! h
    exact (not_lt_of_ge (binIndex_le_iff.1 (show binIndex x ≤ J by omega))) hx
  have hlo : i ≤ binIndex x := max_le hlo₁ hlo₂
  refine ⟨hlo, ?_⟩
  by_cases hix : binIndex x ≤ i
  · exact hix.trans ((Nat.le_add_right i (w / d)).trans (Nat.le_add_right _ 1))
  let k := binIndex x - 1
  have hki : i ≤ k := by dsimp [k]; omega
  have hk : binIndex x = k + 1 := by dsimp [k]; omega
  have hstart : 1000 * (d + 1) ≤ i := hj.trans (by dsimp [i]; omega)
  have hlow := coarseEdge_jump hstart hki
  have hxe := (binIndex_succ_iff.1 hk).1
  have he : u ≤ coarseEdge i := binIndex_le_iff.1 (le_max_left _ _)
  have hprod : (k - i) * d ≤ w := by omega
  have hle := (Nat.le_div_iff_mul_le hd).2 hprod
  omega

private lemma tail_window_card {S : Finset ℕ} {J d p u w : ℕ}
    (hd : 0 < d) (hJ : 1000 * (d + 1) ≤ J)
    (hcap : ∀ i > J, (S.filter (fun x => binIndex x = i)).card ≤ p) :
    (S.filter (fun x => u ≤ x ∧ x ≤ u + w ∧ coarseEdge J < x)).card ≤ p * (w / d + 2) := by
  let Tail := S.filter (fun x => u ≤ x ∧ x ≤ u + w ∧ coarseEdge J < x)
  let lo := max (binIndex u) (J + 1)
  let I := Finset.Icc lo (lo + w / d + 1)
  let part (i : ℕ) := S.filter (fun x => binIndex x = i)
  have hsub : Tail ⊆ I.biUnion part := by
    intro x hx
    obtain ⟨hxS, hu, hw, hj⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_biUnion.2 ⟨binIndex x, Finset.mem_Icc.2 (window_bins hd hJ hu hw hj),
      Finset.mem_filter.2 ⟨hxS, rfl⟩⟩
  have hI : I.card = w / d + 2 := by
    change (Finset.Icc lo (lo + w / d + 1)).card = w / d + 2
    rw [Nat.card_Icc]
    generalize w / d = r
    omega
  calc
    _ ≤ (I.biUnion part).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ I, (part i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, p := by
      apply Finset.sum_le_sum
      intro i hi
      have hh : lo ≤ i := (Finset.mem_Icc.1 hi).1
      exact hcap i (by dsimp [lo] at hh; omega)
    _ = _ := by simp [Finset.sum_const, hI, Nat.mul_comm]

/-- A fixed initial prefix and bounded occupancy of long bins give a uniform local count. -/
theorem window_count_le {S : Finset ℕ} {J d p u w : ℕ}
    (hd : 0 < d) (hJ : 1000 * (d + 1) ≤ J)
    (hcap : ∀ i > J, (S.filter (fun x => binIndex x = i)).card ≤ p) :
    windowCount S u w ≤ countThrough S J + p * (w / d + 2) := by
  let H := S.filter (· ≤ coarseEdge J)
  let T := S.filter (fun x => u ≤ x ∧ x ≤ u + w ∧ coarseEdge J < x)
  have hsub : S.filter (fun x => u ≤ x ∧ x ≤ u + w) ⊆ H ∪ T := by
    intro x hx
    obtain ⟨hxS, hu, hw⟩ := Finset.mem_filter.1 hx
    by_cases h : x ≤ coarseEdge J
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hxS, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hxS, hu, hw, by omega⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le H T).trans
    (Nat.add_le_add_left (tail_window_card (u := u) (w := w) hd hJ hcap) _))

/-- A late interval shorter than the guaranteed bin width touches at most two bins. -/
theorem late_window_count_le {S : Finset ℕ} {J d p u w : ℕ}
    (hJ : 1000 * (d + 1) ≤ J) (hcap : ∀ i > J, (S.filter (fun x => binIndex x = i)).card ≤ p)
    (hu : coarseEdge J < u) (hw : w < d) : windowCount S u w ≤ 2 * p := by
  have he : S.filter (fun x => u ≤ x ∧ x ≤ u + w) =
      S.filter (fun x => u ≤ x ∧ x ≤ u + w ∧ coarseEdge J < x) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hx, hux, hxu⟩ => ⟨hx, hux, hxu, hu.trans_le hux⟩,
      fun ⟨hx, hux, hxu, _⟩ => ⟨hx, hux, hxu⟩⟩
  unfold windowCount
  rw [he]
  simpa [Nat.div_eq_of_lt hw, Nat.mul_comm] using
    tail_window_card (u := u) (w := w) (by omega : 0 < d) hJ hcap

private lemma card_reflected_points {S : Finset ℕ} {l W N Q : ℕ}
    (localCount : ∀ u, windowCount S u W ≤ Q) :
    ((Finset.Ico l (l + W)).filter (fun x => x ≤ N ∧ N - x ∈ S)).card ≤ Q := by
  let lower := N - (l + W)
  let src := (Finset.Ico l (l + W)).filter (fun x => x ≤ N ∧ N - x ∈ S)
  have h : src.card ≤ windowCount S lower W := by
    apply Finset.card_le_card_of_injOn (fun x => N - x)
    · intro x hx
      obtain ⟨hb, hxN, hxS⟩ := Finset.mem_filter.1 hx
      have hx' := Finset.mem_Ico.1 hb
      change N - x ∈ S.filter (fun z => lower ≤ z ∧ z ≤ lower + W)
      exact Finset.mem_filter.2 ⟨hxS, by dsimp [lower]; omega, by dsimp [lower]; omega⟩
    · intro x hx y hy heq
      have hxN := (Finset.mem_filter.1 hx).2.1
      have hyN := (Finset.mem_filter.1 hy).2.1
      change N - x = N - y at heq
      omega
  exact h.trans (localCount _)

/-- A long interval contains a fresh replacement avoiding the chosen sum.
    Both the occupied points and their reflected copies are excluded. -/
theorem replacement_in_window (B P : Finset ℕ) (l W N Q : ℕ)
    (localCount : ∀ u, windowCount B u W ≤ Q)
    (hW : 2 * Q + 2 * P.card < W) :
    ∃ w, l ≤ w ∧ w < l + W ∧ w ∉ B ∪ P ∧ ∀ z ∈ B ∪ P, w + z ≠ N := by
  let I := Finset.Ico l (l + W)
  let occB := I.filter (· ∈ B)
  let occP := I.filter (· ∈ P)
  let refB := I.filter (fun x => x ≤ N ∧ N - x ∈ B)
  let refP := I.filter (fun x => x ≤ N ∧ N - x ∈ P)
  let blocked := (occB ∪ occP) ∪ (refB ∪ refP)
  have hb : occB.card ≤ Q := by
    apply (Finset.card_le_card (t := B.filter (fun x => l ≤ x ∧ x ≤ l + W)) ?_).trans (localCount l)
    intro x hx
    obtain ⟨hxI, hxB⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨hxB, (Finset.mem_Ico.1 hxI).1, (Finset.mem_Ico.1 hxI).2.le⟩
  have hp : occP.card ≤ P.card :=
    Finset.card_le_card (fun _ hx => (Finset.mem_filter.1 hx).2)
  have hpb (u : ℕ) : windowCount P u W ≤ P.card := Finset.card_filter_le _ _
  have hbr : refB.card ≤ Q := card_reflected_points localCount
  have hpr : refP.card ≤ P.card := card_reflected_points hpb
  have hblocked : blocked.card ≤ 2 * Q + 2 * P.card := by
    have h₁ := (Finset.card_union_le occB occP).trans (Nat.add_le_add hb hp)
    have h₂ := (Finset.card_union_le refB refP).trans (Nat.add_le_add hbr hpr)
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add h₁ h₂).trans (by omega))
  have hI : I.card = W := by
    change (Finset.Ico l (l + W)).card = W
    rw [Nat.card_Ico]
    omega
  obtain ⟨w, hw, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show blocked.card < I.card by rw [hI]; exact hblocked.trans_lt hW)
  obtain ⟨hwl, hwh⟩ := Finset.mem_Ico.1 hw
  refine ⟨w, hwl, hwh, ?_, ?_⟩
  · intro hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hm (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hw, hx⟩)))
    · exact hm (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hw, hx⟩)))
  · intro z hz he
    have hn : w ≤ N := by omega
    have hz' : N - w = z := by omega
    rcases Finset.mem_union.1 hz with hz | hz
    · exact hm (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hw, hn, hz' ▸ hz⟩)))
    · exact hm (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hw, hn, hz' ▸ hz⟩)))

end Erdos326
