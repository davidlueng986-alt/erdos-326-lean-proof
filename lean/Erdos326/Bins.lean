module

public import Erdos326.Spacing
public import Erdos326.Stage

@[expose] public section

namespace Erdos326

/-- Group three consecutive quadratic bins, so at most two points are mandatory. -/
def coarseEdge (i : ℕ) : ℕ := quadBin (3 * i)

def countThrough (S : Finset ℕ) (i : ℕ) : ℕ := (S.filter (· ≤ coarseEdge i)).card

lemma coarseEdge_monotone : Monotone coarseEdge :=
  fun _ _ hij => quadBin_monotone (Nat.mul_le_mul_left 3 hij)

lemma coarseEdge_cofinal (x : ℕ) : ∃ i, x ≤ coarseEdge i := by
  let i := 10000 * (x + 1)
  exact ⟨i, (quadBin_cofinal x).trans (quadBin_monotone (show i ≤ 3 * i by omega))⟩

noncomputable def binIndex (x : ℕ) : ℕ := Nat.find (coarseEdge_cofinal x)

lemma binIndex_le_iff {x i : ℕ} : binIndex x ≤ i ↔ x ≤ coarseEdge i := by
  refine ⟨fun h => (Nat.find_spec (coarseEdge_cofinal x)).trans (coarseEdge_monotone h),
    fun h => Nat.find_min' (coarseEdge_cofinal x) h⟩

lemma binIndex_succ_iff {x i : ℕ} :
    binIndex x = i + 1 ↔ coarseEdge i < x ∧ x ≤ coarseEdge (i + 1) := by
  have hlo := not_congr (binIndex_le_iff (x := x) (i := i))
  have hhi := binIndex_le_iff (x := x) (i := i + 1)
  omega

private lemma coarseEdge_width_ge_of {i d : ℕ} (hi : 10000 * (d + 1) ≤ 18 * i + 9) :
    coarseEdge i + d ≤ coarseEdge (i + 1) := by
  have hlo : 10000 * quadBin (3 * i) ≤ (3 * i) ^ 2 := by
    rw [Nat.mul_comm, quadBin]
    exact Nat.div_mul_le_self _ _
  have hhi : (3 * (i + 1)) ^ 2 < 10000 * (quadBin (3 * (i + 1)) + 1) :=
    Nat.lt_mul_div_succ _ (by decide)
  rw [show (3 * (i + 1)) ^ 2 = (3 * i) ^ 2 + 18 * i + 9 by ring] at hhi
  change quadBin (3 * i) + d ≤ quadBin (3 * (i + 1))
  omega

lemma coarseEdge_width_ge {i d : ℕ} (hi : 1000 * (d + 1) ≤ i) :
    coarseEdge i + d ≤ coarseEdge (i + 1) :=
  coarseEdge_width_ge_of (by omega)

lemma quadBin_mul_ge (d m : ℕ) : d ^ 2 * quadBin m ≤ quadBin (d * m) := by
  have h : 10000 * quadBin m ≤ m ^ 2 := by
    rw [Nat.mul_comm, quadBin]
    exact Nat.div_mul_le_self _ _
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 10000)).2
  calc
    _ = d ^ 2 * (10000 * quadBin m) := by ring
    _ ≤ d ^ 2 * m ^ 2 := Nat.mul_le_mul_left _ h
    _ = (d * m) ^ 2 := by rw [mul_pow]

lemma coarseEdge_mul_ge (d i : ℕ) : d ^ 2 * coarseEdge i ≤ coarseEdge (d * i) := by
  unfold coarseEdge
  rw [show 3 * (d * i) = d * (3 * i) by ring]
  exact quadBin_mul_ge d (3 * i)

lemma countThrough_eq_card {S : Finset ℕ} {i : ℕ}
    (h : ∀ x ∈ S, x ≤ coarseEdge i) : countThrough S i = S.card := by
  unfold countThrough
  rw [Finset.filter_eq_self.2 h]

lemma countThrough_of_agree {S T : Finset ℕ} {i : ℕ}
    (h : ∀ x ≤ coarseEdge i, x ∈ S ↔ x ∈ T) : countThrough S i = countThrough T i := by
  unfold countThrough
  congr 1
  ext x
  simp only [Finset.mem_filter]
  by_cases hx : x ≤ coarseEdge i
  · simp [hx, h x hx]
  · simp [hx]

lemma countThrough_succ (S : Finset ℕ) (i : ℕ) :
    countThrough S (i + 1) =
      countThrough S i + (S.filter (fun x => binIndex x = i + 1)).card := by
  let P := S.filter (· ≤ coarseEdge i)
  let Q := S.filter (fun x => binIndex x = i + 1)
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.2
    intro x hx hy
    have hx₁ := (Finset.mem_filter.1 hx).2
    have hy₁ := (binIndex_succ_iff.1 (Finset.mem_filter.1 hy).2).1
    omega
  have he : S.filter (· ≤ coarseEdge (i + 1)) = P ∪ Q := by
    ext x
    simp only [P, Q, Finset.mem_union, Finset.mem_filter, binIndex_succ_iff]
    have hlo : coarseEdge i ≤ coarseEdge (i + 1) := coarseEdge_monotone (by omega)
    by_cases hx : x ≤ coarseEdge i
    · have hy : x ≤ coarseEdge (i + 1) := hx.trans hlo
      simp [hx, hy]
    · have hx' : coarseEdge i < x := by omega
      simp [hx, hx']
  change (S.filter (· ≤ coarseEdge (i + 1))).card = P.card + Q.card
  rw [he, Finset.card_union_of_disjoint hdis]

def skeleton : Set ℕ := casselsBasis 0 ∪ casselsBasis 1

/-- If a future representation uses a point in a frozen range, that point survived. -/
def IntactAfter (S : Finset ℕ) (Y : ℕ) : Prop :=
  ∀ s : Fin 2, ∀ n > Y,
    ((casselsPair s n).x ≤ Y → (casselsPair s n).x ∈ S) ∧
    ((casselsPair s n).y ≤ Y → (casselsPair s n).y ∈ S)

private lemma casselsBasis_subset_skeleton (s : Fin 2) :
    casselsBasis s ⊆ skeleton := by
  fin_cases s
  · exact Set.subset_union_left
  · exact Set.subset_union_right

lemma pair_bounds (s : Fin 2) (n : ℕ) :
    (casselsPair s n).x ≤ n ∧ (casselsPair s n).y ≤ n := by
  have h := (casselsPair s n).sum_eq
  omega

lemma IntactAfter.extend {S B : Finset ℕ} {lo hi : ℕ} (h : IntactAfter S lo)
    (hsub : S ⊆ B) (hnew : ∀ x, lo < x → x ≤ hi → x ∈ skeleton → x ∈ B)
    (s : Fin 2) (n : ℕ) (hn : lo < n) :
    ((casselsPair s n).x ≤ hi → (casselsPair s n).x ∈ B) ∧
    ((casselsPair s n).y ≤ hi → (casselsPair s n).y ∈ B) := by
  have hcopy (x : ℕ) (hx : x ∈ casselsBasis s) (hOld : x ≤ lo → x ∈ S) (hhi : x ≤ hi) : x ∈ B := by
    by_cases hlo : x ≤ lo
    · exact hsub (hOld hlo)
    · exact hnew x (by omega) hhi (casselsBasis_subset_skeleton s hx)
  let r := casselsPair s n
  exact ⟨hcopy r.x (mem_casselsBasis.2 ⟨r.i, r.left_mem⟩) (h s n hn).1,
    hcopy r.y (mem_casselsBasis.2 ⟨r.j, r.right_mem⟩) (h s n hn).2⟩

private lemma fill_one_bin (B : Finset ℕ) (i : ℕ) (hi : 4000 ≤ i)
    (hB : ∀ x ∈ B, x ≤ coarseEdge i) (hcount : 3 * i + 2 ≤ B.card) :
    ∃ T : Finset ℕ,
      (∀ x ∈ T, x ≤ coarseEdge (i + 1)) ∧
      (∀ x ≤ coarseEdge i, x ∈ T ↔ x ∈ B) ∧
      (∀ x, coarseEdge i < x → x ≤ coarseEdge (i + 1) → x ∈ skeleton → x ∈ T) ∧
      T.card ≤ max (3 * (i + 1) + 2) (B.card + 2) ∧
      3 * (i + 1) + 2 ≤ T.card := by
  classical
  let I := Finset.Ioc (coarseEdge i) (coarseEdge (i + 1))
  let G := I.filter (· ∈ skeleton)
  have hG : G.card ≤ 2 := by
    apply card_union_in_three_bins_le_two (3 * i) (by omega)
    intro x hx
    obtain ⟨hix, hs⟩ := Finset.mem_filter.1 hx
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.1 hix
    have he : 3 * (i + 1) = 3 * i + 3 := by omega
    exact ⟨hs, hlo, by simpa only [coarseEdge, he] using hhi⟩
  have hI : 5 ≤ I.card := by
    change 5 ≤ (Finset.Ioc (coarseEdge i) (coarseEdge (i + 1))).card
    rw [Nat.card_Ioc]
    have hbig := coarseEdge_width_ge_of (i := i) (d := 5) (by omega)
    omega
  let need := (3 * (i + 1) + 2) - (B.card + G.card)
  have haveRoom : need ≤ (I \ G).card := by
    have h := Finset.card_sdiff_add_card_eq_card (show G ⊆ I from Finset.filter_subset _ _)
    change (3 * (i + 1) + 2) - (B.card + G.card) ≤ (I \ G).card
    omega
  obtain ⟨F, hF, hcF⟩ := Finset.exists_subset_card_eq haveRoom
  let T := B ∪ (G ∪ F)
  have hGF : Disjoint G F := by
    apply Finset.disjoint_left.2
    exact fun _ hxG hxF => (Finset.mem_sdiff.1 (hF hxF)).2 hxG
  have hinside : G ∪ F ⊆ I := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (Finset.mem_filter.1 hx).1
    · exact (Finset.mem_sdiff.1 (hF hx)).1
  have hdis : Disjoint B (G ∪ F) := by
    apply Finset.disjoint_left.2
    intro x hx hy
    exact (not_lt_of_ge (hB x hx)) (Finset.mem_Ioc.1 (hinside hy)).1
  have he : T.card = B.card + G.card + need := by
    change (B ∪ (G ∪ F)).card = _
    rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hGF, hcF]
    omega
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (hB x hx).trans (coarseEdge_monotone (by omega))
    · exact (Finset.mem_Ioc.1 (hinside hx)).2
  · intro x hx
    refine ⟨fun hm => ?_, fun hm => Finset.mem_union_left _ hm⟩
    rcases Finset.mem_union.1 hm with hm | hm
    · exact hm
    · exact (not_lt_of_ge hx (Finset.mem_Ioc.1 (hinside hm)).1).elim
  · intro x hlo hhi hs
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.2
      ⟨Finset.mem_Ioc.2 ⟨hlo, hhi⟩, hs⟩))
  · rw [he]
    change B.card + G.card + (3 * (i + 1) + 2 - (B.card + G.card)) ≤ _
    omega
  · rw [he]
    change 3 * (i + 1) + 2 ≤ B.card + G.card + (3 * (i + 1) + 2 - (B.card + G.card))
    omega

/-- A stage frozen at the end of a coarse bin. -/
structure StagePrefix (start E : ℕ) where
  index : ℕ
  points : Finset ℕ
  index_ge : start ≤ index
  bounded : ∀ x ∈ points, x ≤ coarseEdge index
  covered : ∀ n ≤ coarseEdge index, Represented points n
  intact : IntactAfter points (coarseEdge index)
  counts : ∀ i, start ≤ i → i ≤ index →
    3 * i + 2 ≤ countThrough points i ∧ countThrough points i ≤ 3 * i + 2 + E

/-- Normal filling keeps the prior prefix, includes the skeleton in the new
    range, and reduces any counting surplus by at least one per coarse bin. -/
theorem extend_normally {start E : ℕ} (hstart : 4000 ≤ start)
    (p : StagePrefix start E) {j : ℕ} (hj : p.index ≤ j) :
    ∃ B : Finset ℕ,
      (∀ x ∈ B, x ≤ coarseEdge j) ∧
      (∀ x ≤ coarseEdge p.index, x ∈ B ↔ x ∈ p.points) ∧
      (∀ x, coarseEdge p.index < x → x ≤ coarseEdge j → x ∈ skeleton → x ∈ B) ∧
      (∀ i, start ≤ i → i ≤ j →
        3 * i + 2 ≤ countThrough B i ∧ countThrough B i ≤ 3 * i + 2 + (E - (i - p.index))) := by
  induction j, hj using Nat.le_induction with
  | base =>
    refine ⟨p.points, p.bounded, fun _ _ => Iff.rfl, ?_, ?_⟩
    · intro x h h'
      exact (not_lt_of_ge h' h).elim
    · intro i hi hi'
      have h := p.counts i hi hi'
      simpa [Nat.sub_eq_zero_of_le hi'] using h
  | succ j h_j ih =>
    obtain ⟨B, hb, hagree, hnew, hc⟩ := ih
    have hj : 4000 ≤ j := hstart.trans (p.index_ge.trans h_j)
    have hjstart := p.index_ge.trans h_j
    have heq := countThrough_eq_card hb
    have hlo : 3 * j + 2 ≤ B.card := heq ▸ (hc j hjstart le_rfl).1
    have hhi : B.card ≤ 3 * j + 2 + (E - (j - p.index)) := heq ▸ (hc j hjstart le_rfl).2
    obtain ⟨T, hTb, hTagree, hTnew, hThi, hTlo⟩ := fill_one_bin B j hj hb hlo
    have hcut := coarseEdge_monotone h_j
    refine ⟨T, hTb, fun x hx => (hTagree x (hx.trans hcut)).trans (hagree x hx), ?_, ?_⟩
    · intro x hx hy hs
      by_cases h : x ≤ coarseEdge j
      · exact (hTagree x h).2 (hnew x hx h hs)
      · exact hTnew x (by omega) hy hs
    · intro i hi hij
      by_cases h : i ≤ j
      · rw [countThrough_of_agree (fun x hx => hTagree x (hx.trans (coarseEdge_monotone h)))]
        exact hc i hi h
      · have h' : i = j + 1 := by omega
        subst i
        rw [countThrough_eq_card hTb]
        exact ⟨hTlo, by omega⟩

end Erdos326
