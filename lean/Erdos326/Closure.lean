module

public import Erdos326.Initial
public import Erdos326.LocalCount

@[expose] public section

open Filter Topology

namespace Erdos326

private lemma card_filter_union_le {B P : Finset ℕ} (test : ℕ → Prop) [DecidablePred test] :
    ((B ∪ P).filter test).card ≤ (B.filter test).card + P.card := by
  rw [Finset.filter_union]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_filter_le _ _) _)

private lemma count_window_mono {S T : Finset ℕ} (h : S ⊆ T) (u w : ℕ) :
    windowCount S u w ≤ windowCount T u w :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

private lemma countThrough_mono {S T : Finset ℕ} (h : S ⊆ T) (i : ℕ) :
    countThrough S i ≤ countThrough T i :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

private lemma count_profile_of_replacement {B D R : Finset ℕ}
    (hD : D ⊆ B) (hR : Disjoint R B)
    (profile : ∀ test : ℕ → Prop, ∀ [DecidablePred test],
      (R.filter (fun x => test (binIndex x))).card = (D.filter (fun x => test (binIndex x))).card)
    (i : ℕ) : countThrough ((B \ D) ∪ R) i = countThrough B i := by
  let test (x : ℕ) := x ≤ coarseEdge i
  have hc := profile (· ≤ i)
  simp only [binIndex_le_iff] at hc
  have he : (B \ D).filter test = B.filter test \ D.filter test := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hdis : Disjoint ((B \ D).filter test) (R.filter test) := by
    apply Finset.disjoint_left.2
    intro x hx hy
    exact Finset.disjoint_left.1 hR (Finset.mem_filter.1 hy).1
      (Finset.mem_sdiff.1 (Finset.mem_filter.1 hx).1).1
  change (((B \ D) ∪ R).filter test).card = (B.filter test).card
  rw [Finset.filter_union, Finset.card_union_of_disjoint hdis, he]
  change _ + (R.filter (· ≤ coarseEdge i)).card = _
  rw [hc]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter _ hD)

private lemma bin_cap {B : Finset ℕ} {j E : ℕ}
    (hB : ∀ x ∈ B, x ≤ coarseEdge j)
    (hcount : ∀ i, firstBin ≤ i → i ≤ j →
      3 * i + 2 ≤ countThrough B i ∧ countThrough B i ≤ 3 * i + 2 + E)
    (i : ℕ) (hi : firstBin < i) :
    (B.filter (fun x => binIndex x = i)).card ≤ E + 3 := by
  by_cases h : i ≤ j
  · let k := i - 1
    have hk : k + 1 = i := by dsimp [k]; omega
    have he := countThrough_succ B k
    rw [hk] at he
    have lo := (hcount k (by dsimp [k]; omega) (by dsimp [k]; omega)).1
    have up := (hcount i (by omega) h).2
    omega
  · have he : B.filter (fun x => binIndex x = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro x hx
      obtain ⟨hxB, hxi⟩ := Finset.mem_filter.1 hx
      have hidx := binIndex_le_iff.2 (hB x hxB)
      omega
    simp [he]

private lemma frozen_under_witness {B D R P : Finset ℕ} {X a N : ℕ}
    (hD : ∀ d ∈ D, X < d) (hR : ∀ w ∈ R, X < w)
    (hP : ∀ w ∈ P, X < w) (hW : X < N - a) :
    ∀ x ≤ X, x ∈ witnessCore B D R a N ∪ P ↔ x ∈ B := by
  intro x hx
  have hd : x ∉ D := fun h => (not_lt_of_ge hx) (hD x h)
  have hr : x ∉ R := fun h => (not_lt_of_ge hx) (hR x h)
  have hp : x ∉ P := fun h => (not_lt_of_ge hx) (hP x h)
  simp [witnessCore, hd, hr, hp, show x ≠ N - a by omega]

private lemma width_enough (p c K : ℕ) :
    let d := 16 * (p + 1)
    let W := d * (4 * (c + 2 * p + K + 1))
    2 * (c + p * (W / d + 2)) + 2 * K < W := by
  dsimp
  rw [Nat.mul_comm (16 * (p + 1)), Nat.mul_div_cancel _ (by omega : 0 < 16 * (p + 1))]
  nlinarith only [show 0 ≤ p * (c + 2 * p + K + 1) by positivity]

/-- The number of repairs permitted after choosing the odd target. -/
def repairBudget : ℕ := 49 * 81921 * 400000 ^ 2

def maxExcess : ℕ := repairBudget + 1

private lemma choose_stage_index (i E J q W H h₀ h₁ : ℕ) :
    ∃ t, i < t ∧ i + E ≤ t ∧ J ≤ t ∧ q ≤ t ∧ 1000 * (W + 1) ≤ t ∧
      10000 * H ≤ t ∧ 10000 * (h₀ + 1) ≤ t ∧ 10000 * (h₁ + 1) ≤ t := by
  refine ⟨i + E + J + q + 1000 * (W + 1) + 10000 * (H + h₀ + h₁ + 1) + 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Construct and certify a complete new stage, including its counting bounds. -/
theorem advance_stage (p : StagePrefix firstBin maxExcess) (a : ℕ) (ha : a ∈ p.points) :
    ∃ q : StagePrefix firstBin maxExcess, ∃ N,
      p.index < q.index ∧
      (∀ x ≤ coarseEdge p.index, x ∈ q.points ↔ x ∈ p.points) ∧
      coarseEdge p.index < N ∧ N ≤ coarseEdge q.index ∧
      AllRepresentationsUse q.points a N := by
  classical
  let cap := maxExcess + 3
  let spacing := 16 * (cap + 1)
  let J := max firstBin (1000 * (spacing + 1))
  let prefixCap := 3 * J + 2 + maxExcess
  let W := spacing * (4 * (prefixCap + 2 * cap + 400000 + 1))
  let Q := prefixCap + cap * (W / spacing + 2)
  let paletteBin := max firstBin (2 * cap + 400000 + repairBudget + 1) + 1
  let paletteWidth := coarseEdge paletteBin
  let shiftStart := 1000 * (paletteWidth + 2) + firstBin
  let shiftCut := coarseEdge shiftStart
  obtain ⟨t, ht₀, htE, hJt, hqt, htW, hshiftT, hscale₀, hscale₁⟩ :=
    choose_stage_index p.index maxExcess J paletteBin W shiftCut (blockStart 0 4) (blockStart 1 4)
  let j := 1000 * t
  let X := coarseEdge t
  let L := coarseEdge (2 * t)
  let Y := coarseEdge j
  have htpos : 0 < t := (Nat.zero_le _).trans_lt ht₀
  have hj : t ≤ j := Nat.le_mul_of_pos_left _ (by decide)
  have htL : t ≤ 2 * t := Nat.le_mul_of_pos_left _ (by decide)
  have hY₀ : coarseEdge p.index ≤ X := coarseEdge_monotone ht₀.le
  have hXLle : X ≤ L := coarseEdge_monotone htL
  have hXL : 2 * X ≤ L := (Nat.mul_le_mul_right X (by decide : 2 ≤ 4)).trans
    (coarseEdge_mul_ge 2 t)
  have hLY : 250000 * L ≤ Y := by
    have he := coarseEdge_mul_ge 500 (2 * t)
    change 250000 * L ≤ coarseEdge (500 * (2 * t)) at he
    rwa [show 500 * (2 * t) = j from (Nat.mul_assoc 500 2 t).symm] at he
  have hL : ∀ s : Fin 2, blockStart s 4 ≤ L := by
    have hb : t ≤ 3 * (2 * t) := htL.trans (Nat.le_mul_of_pos_left _ (by decide))
    intro s
    fin_cases s
    · exact (quadBin_cofinal _).trans (quadBin_monotone (hscale₀.trans hb))
    · exact (quadBin_cofinal _).trans (quadBin_monotone (hscale₁.trans hb))
  obtain ⟨B, hB, hAgree, hNew, hCount⟩ := extend_normally
    (by decide : 4000 ≤ firstBin) p (ht₀.le.trans hj)
  have hCounts (i : ℕ) (hi : firstBin ≤ i) (hij : i ≤ j) :
      3 * i + 2 ≤ countThrough B i ∧ countThrough B i ≤ 3 * i + 2 + maxExcess := by
    obtain ⟨hl, hu⟩ := hCount i hi hij
    exact ⟨hl, hu.trans (Nat.add_le_add_left (Nat.sub_le _ _) _)⟩
  have hExact (i : ℕ) (hi : t ≤ i) (hij : i ≤ j) : countThrough B i = 3 * i + 2 := by
    obtain ⟨hl, hu⟩ := hCount i (p.index_ge.trans (ht₀.le.trans hi)) hij
    omega
  have hold : p.points ⊆ B := fun x hx => (hAgree x (p.bounded x hx)).2 hx
  have haX : a ≤ X := (p.bounded a ha).trans hY₀
  have h0 : 0 ∈ B := by
    obtain ⟨x, hx, y, _, he⟩ := p.covered 0 (Nat.zero_le _)
    rw [show x = 0 by omega] at hx
    exact hold hx
  have hTargetCount : (B.filter (· ≤ 3 * L)).card ≤ 3 * (6 * t) := by
    have h4 : 4 * L ≤ coarseEdge (4 * t) := by
      have he := coarseEdge_mul_ge 2 (2 * t)
      rwa [show 2 * (2 * t) = 4 * t by omega] at he
    have he := hExact (4 * t) (Nat.le_mul_of_pos_left t (by decide))
      (Nat.mul_le_mul_right t (by decide : 4 ≤ 1000))
    have hcard : (B.filter (· ≤ 3 * L)).card ≤ countThrough B (4 * t) := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxB, hxL⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨hxB, hxL.trans (by omega)⟩
    omega
  have hL' : L = quadBin (6 * t) := by
    change quadBin (3 * (2 * t)) = _
    rw [show 3 * (2 * t) = 6 * t by omega]
  have hmin : 200 ≤ 6 * t := by
    have hfirst := p.index_ge
    unfold firstBin at hfirst
    omega
  rw [hL'] at hTargetCount
  obtain ⟨N, hN₀, hN₁, hodd, _hNd⟩ := exists_odd_target B (6 * t) hmin hTargetCount
  rw [← hL'] at hN₀ hN₁
  let D := upperEndpoints B N
  have hNd : D.card < 400000 := _hNd
  have hDsub : D ⊆ B := Finset.filter_subset _ _
  have hD (d : ℕ) (hd : d ∈ D) : L < d ∧ d ≤ N :=
    ⟨upperEndpoints_above hN₀ hd, (Finset.mem_filter.1 hd).2.1⟩
  have hHorizon : 24577 * N ≤ Y := by omega
  have h0D (d : ℕ) (hd : d ∈ D) : X < d := hXLle.trans_lt (hD d hd).1
  have hWcard : 2 * Q + 2 * 400000 < W := width_enough cap prefixCap 400000
  have hCap (i : ℕ) (hi : firstBin < i) :
      (B.filter (fun x => binIndex x = i)).card ≤ cap :=
    bin_cap hB hCounts i hi
  have localCount (u : ℕ) : windowCount B u W ≤ Q := by
    have hlo : 1000 * (spacing + 1) ≤ J := le_max_right _ _
    have hj' : firstBin ≤ J := le_max_left _ _
    have h := window_count_le (u := u) (w := W) (d := spacing)
      (show 0 < spacing by dsimp [spacing]; omega) hlo
      (fun i hi => hCap i (hj'.trans_lt hi))
    exact h.trans (Nat.add_le_add_right (hCounts J hj' (hJt.trans hj)).2 _)
  have available (P : Finset ℕ) (hp : P.card < D.card) (d : ℕ) (hd : d ∈ D) :
      ∃ w, w ∉ B ∪ P ∧ binIndex w = binIndex d ∧ ∀ z ∈ (B \ D) ∪ P, w + z ≠ N := by
    let k := binIndex d - 1
    have hkd : 2 * t < binIndex d := by
      by_contra! he
      exact (not_lt_of_ge (binIndex_le_iff.1 he)) (hD d hd).1
    have hk : 2 * t ≤ k := by dsimp [k]; omega
    have hkEq : binIndex d = k + 1 := by dsimp [k]; omega
    have hw : coarseEdge k + W ≤ coarseEdge (k + 1) :=
      coarseEdge_width_ge (htW.trans (htL.trans hk))
    obtain ⟨w, hlo, hhi, hfree, hsafe⟩ :=
      replacement_in_window B P (coarseEdge k + 1) W N Q localCount (by omega)
    refine ⟨w, hfree, ?_, ?_⟩
    · rw [hkEq, binIndex_succ_iff]
      omega
    · intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · exact hsafe z (Finset.mem_union_left _ (Finset.mem_sdiff.1 hz).1)
      · exact hsafe z (Finset.mem_union_right _ hz)
  obtain ⟨R, hRdis, hRcard, profile, hRfree⟩ :=
    replace_endpoints B D binIndex hodd (not_represented_after_deleting_endpoints B hodd) available
  have hR (w : ℕ) (hw : w ∈ R) : X < w ∧ w ≤ Y := by
    have hpos : 0 < (R.filter (fun x => binIndex x = binIndex w)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨hw, rfl⟩⟩
    have he := profile (· = binIndex w)
    rw [he] at hpos
    obtain ⟨d, hd'⟩ := Finset.card_pos.1 hpos
    obtain ⟨hd, heq⟩ := Finset.mem_filter.1 hd'
    have hlow : 2 * t < binIndex w := by
      rw [← heq]
      by_contra! hh
      exact (not_lt_of_ge (binIndex_le_iff.1 hh)) (hD d hd).1
    have hhigh : binIndex w ≤ j := heq ▸ (binIndex_le_iff.2 (hB d (hDsub hd)))
    have h' : L < w := by
      by_contra! hh
      exact (not_le_of_gt hlow) (binIndex_le_iff.2 hh)
    exact ⟨hXLle.trans_lt h', binIndex_le_iff.1 hhigh⟩
  have hM : 49 * 81921 * D.card ^ 2 ≤ repairBudget := by
    unfold repairBudget
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNd.le 2)
  have hbW : X < N - a := by omega
  let S := witnessCore B D R a N
  have hzB (P : Finset ℕ) (hPb : ∀ w ∈ P, X < w ∧ w ≤ Y) :
      ∀ x ≤ X, x ∈ S ∪ P ↔ x ∈ B :=
    frozen_under_witness h0D (fun x hx => (hR x hx).1) (fun x hx => (hPb x hx).1) hbW
  have hspace : (3 * t + 2) * shiftCut ≤ X := by
    change (3 * t + 2) * shiftCut ≤ (3 * t) ^ 2 / 10000
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 10000)).2
    calc
      _ = (3 * t + 2) * (10000 * shiftCut) := by ring
      _ ≤ (3 * t + 2) * t := Nat.mul_le_mul_left _ hshiftT
      _ ≤ (3 * t) ^ 2 := by nlinarith only [htpos]
  have hShift (P : Finset ℕ) (hPc : P.card < 49 * 81921 * D.card ^ 2)
      (hPb : ∀ w ∈ P, X < w ∧ w ≤ Y) (n : ℕ) (_hlo : 2 * X < n) (hn : n < N) :
      ∃ u ∈ S ∪ P, u ≤ X ∧ u + (N - n) ∉ S ∪ P := by
    let d := N - n
    have hd : 0 < d := Nat.sub_pos_of_lt hn
    by_cases hs : d ≤ shiftCut
    · have hc : countThrough (S ∪ P) t = 3 * t + 2 := by
        rw [countThrough_of_agree (hzB P hPb), hExact t le_rfl hj]
      have hc' : ((S ∪ P).filter (· ≤ X)).card * d ≤ X := by
        change countThrough (S ∪ P) t * d ≤ X
        rw [hc]
        exact (Nat.mul_le_mul_left _ hs).trans hspace
      obtain ⟨u, hu, hux, hum⟩ := shift_avoided_in_prefix (S ∪ P)
        ((hzB P hPb 0 (Nat.zero_le _)).2 h0) hd hc'
      exact ⟨u, hu, by omega, hum⟩
    · let palette := B.filter (· ≤ paletteWidth)
      have hpX : paletteWidth ≤ X := coarseEdge_monotone hqt
      have hpS : palette ⊆ S ∪ P := by
        intro u hu
        obtain ⟨huB, hux⟩ := Finset.mem_filter.1 hu
        exact (hzB P hPb u (hux.trans hpX)).2 huB
      have hlc : windowCount B d paletteWidth ≤ 2 * cap :=
        late_window_count_le (J := shiftStart) (d := paletteWidth + 1)
          (by dsimp [shiftStart]; omega)
          (fun i hi => hCap i (by dsimp [shiftStart] at hi; omega))
          (by omega : shiftCut < d) (by omega)
      have hsub : S ∪ P ⊆ B ∪ R ∪ insert (N - a) P := by
        intro u hu
        rcases Finset.mem_union.1 hu with hu | hu
        · rcases Finset.mem_insert.1 hu with rfl | hu
          · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · rcases Finset.mem_union.1 hu with hu | hu
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.1 hu).1)
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hu)
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hu)
      have hcomp : windowCount (S ∪ P) d paletteWidth ≤
          2 * cap + R.card + (P.card + 1) := calc
        _ ≤ windowCount (B ∪ R ∪ insert (N - a) P) d paletteWidth :=
          count_window_mono hsub _ _
        _ ≤ windowCount (B ∪ R) d paletteWidth + (insert (N - a) P).card :=
          card_filter_union_le _
        _ ≤ _ := Nat.add_le_add
          ((card_filter_union_le (B := B) (P := R) _).trans (Nat.add_le_add_right hlc _))
          (Finset.card_insert_le _ _)
      have hpCard : 3 * paletteBin + 2 ≤ palette.card :=
        (hCounts paletteBin ((le_max_left _ _).trans (Nat.le_succ _)) (hqt.trans hj)).1
      have hrlt : R.card < 400000 := hRcard ▸ hNd
      have hpless : P.card < repairBudget := hPc.trans_le hM
      have hcard : windowCount (S ∪ P) d paletteWidth < palette.card := calc
        _ ≤ 2 * cap + R.card + (P.card + 1) := hcomp
        _ ≤ 2 * cap + 400000 + (repairBudget + 1) :=
          Nat.add_le_add (Nat.add_le_add_left hrlt.le _) (Nat.add_le_add_right hpless.le 1)
        _ < paletteBin := by
          rw [← Nat.add_assoc]
          exact Nat.lt_succ_of_le (le_max_right _ _)
        _ ≤ 3 * paletteBin + 2 := (Nat.le_mul_of_pos_left _ (by decide)).trans (Nat.le_add_right _ _)
        _ ≤ palette.card := hpCard
      obtain ⟨u, hu, hux, hum⟩ := shift_avoided_by_card (S ∪ P) palette hpS
        (fun _ hu => (Finset.mem_filter.1 hu).2) hcard
      exact ⟨u, hu, hux.trans hpX, hum⟩
  have hBg (n : ℕ) (hn : coarseEdge p.index < n) (hnY : n ≤ Y)
      (s : Fin 2) : HasSelectedPair B s n :=
    let h := p.intact.extend hold hNew s n hn
    ⟨h.1 ((pair_bounds s n).1.trans hnY), h.2 ((pair_bounds s n).2.trans hnY)⟩
  obtain ⟨P, hPc, _hPb, hCover, hForced, hBound, hFreeze⟩ :=
    finish_finite_stage B D R hY₀ hXL hN₀ hN₁ hHorizon hL hB hD hR h0 (hold ha) haX
      hodd hRfree (fun n hn => (p.covered n hn).mono hold) hBg hShift
  let T := S ∪ P
  have hAdded : (insert (N - a) P).card ≤ maxExcess :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hPc.trans hM) 1)
  have hT : T = ((B \ D) ∪ R) ∪ insert (N - a) P := by
    ext x
    change x ∈ insert (N - a) ((B \ D) ∪ R) ∪ P ↔
      x ∈ ((B \ D) ∪ R) ∪ insert (N - a) P
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((hx | hx) | hx)
      · exact .inr (.inl hx)
      · exact .inl hx
      · exact .inr (.inr hx)
    · rintro (hx | hx | hx)
      · exact .inl (.inr hx)
      · exact .inl (.inl hx)
      · exact .inr hx
  have hLive (i : ℕ) : countThrough ((B \ D) ∪ R) i = countThrough B i :=
    count_profile_of_replacement hDsub hRdis profile i
  have hTC (i : ℕ) (hi : firstBin ≤ i) (hij : i ≤ j) :
      3 * i + 2 ≤ countThrough T i ∧ countThrough T i ≤ 3 * i + 2 + maxExcess := by
    by_cases hh : i ≤ t
    · rw [countThrough_of_agree (T := B)
        (fun x hx => hFreeze x (hx.trans (coarseEdge_monotone hh)))]
      exact hCounts i hi hij
    · have he := hExact i (not_le.mp hh).le hij
      have he' : countThrough ((B \ D) ∪ R) i = 3 * i + 2 := (hLive i).trans he
      constructor
      · rw [hT, ← he']
        exact countThrough_mono (fun _ hx => Finset.mem_union_left _ hx) i
      · rw [hT]
        exact (card_filter_union_le _).trans (Nat.add_le_add he'.le hAdded)
  have hIntact : IntactAfter T Y := by
    intro s n hn
    have hpair := p.intact.extend hold hNew s n (by omega : coarseEdge p.index < n)
    have htD : ¬ Hits D s n := by
      intro hg
      have hstart := ((blockStart_strictMono s).monotone (by decide : 2 ≤ 4)).trans (hL s)
      exact (not_lt_of_ge ((hit_sum_bounds hstart hD hg).2.trans hHorizon)) hn
    have add (x : ℕ) (hx : x ∈ B) (hnD : x ∉ D) : x ∈ T := by
      rw [hT]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hnD⟩))
    exact ⟨fun h => add _ (hpair.1 h) (fun hx => htD (.inl hx)),
      fun h => add _ (hpair.2 h) (fun hx => htD (.inr hx))⟩
  have hBefore : coarseEdge p.index < N := by omega
  have hAfter : N ≤ Y := by omega
  refine ⟨⟨j, T, p.index_ge.trans (ht₀.le.trans hj), hBound, hCover, hIntact, hTC⟩,
    N, ht₀.trans_le hj, ?_, hBefore, hAfter, hForced⟩
  intro x hx
  exact (hFreeze x (hx.trans hY₀)).trans (hAgree x hx)

private def StagePrefix.toFinePrefix (p : StagePrefix firstBin maxExcess) :
    FinitePrefix (3 * firstBin) (maxExcess + 4) where
  index := 3 * p.index
  points := p.points
  index_ge := Nat.mul_le_mul_left _ p.index_ge
  bounded := p.bounded
  coverage := p.covered
  counts i hi hij := by
    let l := i / 3
    let u := (i + 2) / 3
    have hl : 3 * l ≤ i := by dsimp [l]; omega
    have hu : i ≤ 3 * u := by dsimp [u]; omega
    have hl' : i ≤ 3 * l + 2 := by dsimp [l]; omega
    have hu' : 3 * u + 2 ≤ i + 4 := by dsimp [u]; omega
    have hlo := (p.counts l (by dsimp [l]; omega) (by dsimp [l]; omega)).1
    have hhi := (p.counts u (by dsimp [u]; omega) (by dsimp [u]; omega)).2
    have hcard (a b : ℕ) (h : a ≤ b) :
        (p.points.filter (· ≤ quadBin a)).card ≤ (p.points.filter (· ≤ quadBin b)).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxP, hxb⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨hxP, hxb.trans (quadBin_monotone h)⟩
    change 3 * l + 2 ≤ (p.points.filter (· ≤ quadBin (3 * l))).card at hlo
    change (p.points.filter (· ≤ quadBin (3 * u))).card ≤ 3 * u + 2 + maxExcess at hhi
    exact ⟨hl'.trans (hlo.trans (hcard _ _ hl)),
      (hcard _ _ hu).trans (hhi.trans (by omega))⟩

/-- An affirmative solution to Erdős Problem 326, with limiting constant `1/10000`. -/
theorem erdos_326_fixed_limit :
    ∃ a : ℕ → ℕ, StrictMono a ∧ Minimal IsAsymptoticBasisOrder2 (Set.range a) ∧
      Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 (1 / 10000 : ℝ)) := by
  obtain ⟨initial⟩ := initial_prefix maxExcess
  let Valid (p : FinitePrefix (3 * firstBin) (maxExcess + 4)) :=
    ∃ q : StagePrefix firstBin maxExcess, q.toFinePrefix = p
  apply exists_of_prefix_extensions Valid initial.toFinePrefix ⟨initial, rfl⟩
  intro p hp a ha
  obtain ⟨p', rfl⟩ := hp
  obtain ⟨q, N, hidx, hagree, hN₀, hN₁, hw⟩ := advance_stage p' a ha
  exact ⟨q.toFinePrefix, ⟨q, rfl⟩, ⟨Nat.mul_lt_mul_of_pos_left hidx (by decide), hagree⟩,
    ⟨N, hN₀, hN₁, hw⟩⟩

/-- The original problem statement, using an explicit sum-of-two definition of basis. -/
theorem erdos_326 :
    ∃ a : ℕ → ℕ, StrictMono a ∧ Minimal IsAsymptoticBasisOrder2 (Set.range a) ∧
      ∃ c : ℝ, c ≠ 0 ∧ Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  obtain ⟨a, ha, hm, ht⟩ := erdos_326_fixed_limit
  exact ⟨a, ha, hm, 1 / 10000, by norm_num, ht⟩

end Erdos326
