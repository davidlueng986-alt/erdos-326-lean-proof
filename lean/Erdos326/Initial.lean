module

public import Erdos326.Bins

@[expose] public section

namespace Erdos326

def firstBin : ℕ := 20000

private noncomputable def skeletonPrefix (i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Iic (coarseEdge i)).filter (· ∈ skeleton)

private lemma mem_skeletonPrefix {i x : ℕ} :
    x ∈ skeletonPrefix i ↔ x ≤ coarseEdge i ∧ x ∈ skeleton := by
  classical
  simp [skeletonPrefix]

private lemma skeletonPrefix_card (i : ℕ) (hi : 4000 ≤ i) :
    (skeletonPrefix i).card ≤ coarseEdge 4000 + 1 + 2 * (i - 4000) := by
  induction i, hi using Nat.le_induction with
  | base =>
    classical
    simpa [skeletonPrefix] using Finset.card_filter_le (s := Finset.Iic (coarseEdge 4000))
      (· ∈ skeleton)
  | succ i hi ih =>
    let B := skeletonPrefix (i + 1)
    have he : B.card = (skeletonPrefix i).card +
        (B.filter (fun x => binIndex x = i + 1)).card := by
      rw [← countThrough_eq_card (show ∀ x ∈ B, x ≤ coarseEdge (i + 1)
        from fun _ hx => (mem_skeletonPrefix.1 hx).1), countThrough_succ]
      rw [countThrough_of_agree (T := skeletonPrefix i)]
      · rw [countThrough_eq_card (fun _ hx => (mem_skeletonPrefix.1 hx).1)]
      · intro x hx
        change x ∈ skeletonPrefix (i + 1) ↔ x ∈ skeletonPrefix i
        rw [mem_skeletonPrefix, mem_skeletonPrefix]
        have h := hx.trans (coarseEdge_monotone (Nat.le_succ _))
        simp [hx, h]
    have hbin : (B.filter (fun x => binIndex x = i + 1)).card ≤ 2 := by
      apply card_union_in_three_bins_le_two (3 * i) (by omega)
      intro x hx
      obtain ⟨hxB, hxj⟩ := Finset.mem_filter.1 hx
      obtain ⟨hxLo, hxHi⟩ := binIndex_succ_iff.1 hxj
      have hi' : 3 * (i + 1) = 3 * i + 3 := by omega
      exact ⟨(mem_skeletonPrefix.1 hxB).2, hxLo, by simpa only [coarseEdge, hi'] using hxHi⟩
    change B.card ≤ _
    rw [he]
    omega

/-- Start with both skeletons up to a large bin boundary and pad the initial count. -/
theorem initial_prefix (E : ℕ) : Nonempty (StagePrefix firstBin E) := by
  classical
  let A := skeletonPrefix firstBin
  let I := Finset.Iic (coarseEdge firstBin)
  have hA : A.card ≤ 3 * firstBin + 2 := by
    exact (skeletonPrefix_card firstBin (by decide)).trans (by decide)
  have hI : 3 * firstBin + 2 ≤ I.card := by
    change 3 * firstBin + 2 ≤ (Finset.Iic (coarseEdge firstBin)).card
    rw [Nat.card_Iic]
    decide
  have hsub : A ⊆ I := fun _ hx => Finset.mem_Iic.2 (mem_skeletonPrefix.1 hx).1
  have hroom : 3 * firstBin + 2 - A.card ≤ (I \ A).card := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    omega
  obtain ⟨F, hF, hf⟩ := Finset.exists_subset_card_eq hroom
  have hdisj : Disjoint A F := Finset.disjoint_left.2
    (fun _ hx hy => (Finset.mem_sdiff.1 (hF hy)).2 hx)
  let S := A ∪ F
  have hS : ∀ x ∈ S, x ≤ coarseEdge firstBin := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (mem_skeletonPrefix.1 hx).1
    · exact Finset.mem_Iic.1 (Finset.mem_sdiff.1 (hF hx)).1
  have hsk : ∀ x ≤ coarseEdge firstBin, x ∈ skeleton → x ∈ S :=
    fun _ h₁ h₂ => Finset.mem_union_left _ (mem_skeletonPrefix.2 ⟨h₁, h₂⟩)
  have hcard : S.card = 3 * firstBin + 2 := by
    change (A ∪ F).card = _
    rw [Finset.card_union_of_disjoint hdisj, hf]
    omega
  refine ⟨⟨firstBin, S, le_rfl, hS, ?_, ?_, ?_⟩⟩
  · intro n hn
    obtain ⟨x, hx, y, hy, he⟩ := cassels_basis_covers 0 n
    exact ⟨x, hsk x (by omega) (.inl hx), y, hsk y (by omega) (.inl hy), he⟩
  · intro s n _
    let r := casselsPair s n
    have hs : casselsBasis s ⊆ skeleton := by
      fin_cases s
      · exact Set.subset_union_left
      · exact Set.subset_union_right
    exact ⟨fun h => hsk r.x h (hs (mem_casselsBasis.2 ⟨r.i, r.left_mem⟩)),
      fun h => hsk r.y h (hs (mem_casselsBasis.2 ⟨r.j, r.right_mem⟩))⟩
  · intro i hi hij
    rw [le_antisymm hij hi, countThrough_eq_card hS, hcard]
    exact ⟨le_rfl, Nat.le_add_right _ _⟩

end Erdos326
