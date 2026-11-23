module

public import Erdos326.Witness
public import Erdos326.Collateral

@[expose] public section

namespace Erdos326

private lemma upperEndpoints_filter {S : Finset ℕ} {n B : ℕ} (hn : n ≤ B) :
    upperEndpoints (S.filter (· ≤ B)) n = upperEndpoints S n := by
  ext y
  constructor
  · intro hy
    obtain ⟨hy, hyn, hylt, hx⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1, hyn, hylt, (Finset.mem_filter.1 hx).1⟩
  · intro hy
    obtain ⟨hyS, hyn, hylt, hxS⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hyS, hyn.trans hn⟩, hyn, hylt,
      Finset.mem_filter.2 ⟨hxS, (Nat.sub_le _ _).trans hn⟩⟩

/-- In a quadratic-scale window, a bounded number of deletions isolates some odd target. -/
theorem exists_odd_target (S : Finset ℕ) (m : ℕ) (hm : 200 ≤ m)
    (hS : (S.filter (· ≤ 3 * quadBin m)).card ≤ 3 * m) :
    ∃ n, 2 * quadBin m < n ∧ n ≤ 3 * quadBin m ∧ Odd n ∧
      (upperEndpoints S n).card < 400000 := by
  let L := quadBin m
  let f (k : ℕ) := 2 * L + 2 * k + 1
  let targets := (Finset.range (L / 2)).image f
  have hcard : targets.card = L / 2 := by
    exact (Finset.card_image_of_injective _ (show Function.Injective f by
      intro i j h
      dsimp [f] at h
      omega)).trans (Finset.card_range _)
  have hsq : m ^ 2 < 10000 * (L + 1) := Nat.lt_mul_div_succ _ (by decide)
  have hlarge : 4 ≤ L := by
    calc
      4 = quadBin 200 := by decide
      _ ≤ quadBin m := quadBin_monotone hm
  change (S.filter (· ≤ 3 * L)).card ≤ 3 * m at hS
  have hbudget : (S.filter (· ≤ 3 * L)).card ^ 2 < targets.card * 400000 := by
    rw [hcard]
    have hsq' := Nat.pow_le_pow_left hS 2
    rw [show (3 * m) ^ 2 = 9 * m ^ 2 by ring] at hsq'
    omega
  obtain ⟨n, hn, hde⟩ := exists_target_with_few_endpoints _ targets _ hbudget
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hn
  have hk' : k < L / 2 := Finset.mem_range.1 hk
  have hlo : 2 * L < f k := by dsimp [f]; omega
  have hhi : f k ≤ 3 * L := by dsimp [f]; omega
  have hodd : Odd (f k) := Nat.odd_iff.2 (by dsimp [f]; omega)
  rw [upperEndpoints_filter hhi] at hde
  exact ⟨f k, hlo, hhi, hodd, hde⟩

/-- For a small positive shift, a missing successor follows from a finite count.
    The point and its tested successor both lie in the frozen interval. -/
theorem shift_avoided_in_prefix (S : Finset ℕ) {X d : ℕ}
    (h0 : 0 ∈ S) (hd : 0 < d)
    (hspace : (S.filter (· ≤ X)).card * d ≤ X) :
    ∃ u ∈ S, u + d ≤ X ∧ u + d ∉ S := by
  let A := S.filter (· ≤ X)
  have hex : ∃ k, k ≤ A.card ∧ k * d ∉ S := by
    by_contra! h
    have hm : (Finset.range (A.card + 1)).card ≤ A.card := by
      apply Finset.card_le_card_of_injOn (fun k : ℕ => k * d)
      · intro k hk
        have hka : k ≤ A.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        exact Finset.mem_filter.2 ⟨h k hka, (Nat.mul_le_mul_right _ hka).trans hspace⟩
      · intro k _ j _ heq
        exact Nat.eq_of_mul_eq_mul_right hd heq
    simp at hm
  let k := Nat.find hex
  obtain ⟨hk, hkS⟩ := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra! h
    have : k = 0 := by omega
    rw [show Nat.find hex = k from rfl, this, Nat.zero_mul] at hkS
    exact hkS h0
  have hprev : k - 1 < Nat.find hex := by change k - 1 < k; omega
  have hle : (k - 1) ≤ A.card := by change k ≤ A.card at hk; omega
  have hprevS : (k - 1) * d ∈ S := by
    by_contra ha
    exact Nat.find_min hex hprev ⟨hle, ha⟩
  have hn : (k - 1) * d + d = k * d := by
    calc
      _ = ((k - 1) + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
      _ = _ := by rw [Nat.sub_add_cancel hkpos]
  change k ≤ A.card at hk
  change k * d ∉ S at hkS
  exact ⟨(k - 1) * d, hprevS, by rw [hn]; exact (Nat.mul_le_mul_right _ hk).trans hspace,
    by rwa [hn]⟩

/-- If the shifted interval contains fewer points than the palette, some shift is absent. -/
theorem shift_avoided_by_card (S palette : Finset ℕ) {X d : ℕ} (hsub : palette ⊆ S)
    (hsmall : ∀ u ∈ palette, u ≤ X)
    (hcard : (S.filter (fun z => d ≤ z ∧ z ≤ d + X)).card < palette.card) :
    ∃ u ∈ S, u ≤ X ∧ u + d ∉ S := by
  by_contra! h
  have hle : palette.card ≤ (S.filter (fun z => d ≤ z ∧ z ≤ d + X)).card := by
    apply Finset.card_le_card_of_injOn (· + d)
    · intro u hu
      change u + d ∈ (S.filter (fun z => d ≤ z ∧ z ≤ d + X))
      exact Finset.mem_filter.2 ⟨h u (hsub hu) (hsmall u hu), by omega, by
        have hup := hsmall u hu
        omega⟩
    · intro x _ y _ heq
      exact Nat.add_right_cancel heq
  omega

/-- Replace each removed point with a distinct admissible point in the same bin.
    The resulting set has the same bin counts and still omits the target. -/
theorem replace_endpoints (S D : Finset ℕ) (bin : ℕ → ℕ) {N : ℕ}
    (hodd : Odd N) (hempty : ¬ Represented (S \ D) N)
    (available : ∀ P : Finset ℕ, P.card < D.card → ∀ d ∈ D,
      ∃ w, w ∉ S ∪ P ∧ bin w = bin d ∧ ∀ z ∈ (S \ D) ∪ P, w + z ≠ N) :
    ∃ P : Finset ℕ, Disjoint P S ∧ P.card = D.card ∧
      (∀ keep : ℕ → Prop, ∀ [DecidablePred keep],
        (P.filter (fun x => keep (bin x))).card = (D.filter (fun x => keep (bin x))).card) ∧
      ¬ Represented ((S \ D) ∪ P) N := by
  suffices h : ∀ G ⊆ D, ∃ P : Finset ℕ, Disjoint P S ∧ P.card = G.card ∧
      (∀ keep : ℕ → Prop, ∀ [DecidablePred keep],
        (P.filter (fun x => keep (bin x))).card = (G.filter (fun x => keep (bin x))).card) ∧
      ¬ Represented ((S \ D) ∪ P) N from
    h D (fun _ hx => hx)
  intro G
  induction G using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, by simp, rfl, fun _ _ => rfl, by simpa using hempty⟩
  | insert d G hdG ih =>
    intro hGD
    have hdD : d ∈ D := hGD (Finset.mem_insert_self _ _)
    have hG : G ⊆ D := fun _ hx => hGD (Finset.mem_insert_of_mem hx)
    obtain ⟨P, hdisj, hcard, hbins, hn⟩ := ih hG
    have hP : P.card < D.card := by
      have hbound := Finset.card_le_card hGD
      rw [Finset.card_insert_of_notMem hdG] at hbound
      omega
    obtain ⟨w, hw, hbin, hsafe⟩ := available P hP d hdD
    have hwS : w ∉ S := fun h => hw (Finset.mem_union_left _ h)
    have hwP : w ∉ P := fun h => hw (Finset.mem_union_right _ h)
    have hdisj' : Disjoint (insert w P) S := Finset.disjoint_insert_left.2 ⟨hwS, hdisj⟩
    have hcard' : (insert w P).card = (insert d G).card := by
      rw [Finset.card_insert_of_notMem hwP, Finset.card_insert_of_notMem hdG, hcard]
    refine ⟨insert w P, hdisj', hcard', ?_, ?_⟩
    · intro keep _
      have hPj : w ∉ P.filter (fun x => keep (bin x)) := fun h => hwP (Finset.mem_filter.1 h).1
      have hGj : d ∉ G.filter (fun x => keep (bin x)) := fun h => hdG (Finset.mem_filter.1 h).1
      by_cases hj : keep (bin d)
      · have hj' : keep (bin w) := hbin ▸ hj
        simp only [Finset.filter_insert, hj, hj', ite_true]
        rw [Finset.card_insert_of_notMem hPj, Finset.card_insert_of_notMem hGj, hbins keep]
      · have hj' : ¬ keep (bin w) := by rwa [hbin]
        simp only [Finset.filter_insert, hj, hj', ite_false, hbins keep]
    · have he : (S \ D) ∪ insert w P = insert w ((S \ D) ∪ P) := by
        ext z
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [he]
      have hpar := Nat.odd_iff.1 hodd
      rintro ⟨x, hx, y, hy, hxy⟩
      rcases Finset.mem_insert.1 hx with hxe | hx
      · rcases Finset.mem_insert.1 hy with hye | hy
        · omega
        · exact hsafe y hy (by omega)
      · rcases Finset.mem_insert.1 hy with hye | hy
        · exact hsafe x hx (by omega)
        · exact hn ⟨x, hx, y, hy, hxy⟩

/-- The selected representation of `n` is present in the finite set. -/
def HasSelectedPair (B : Finset ℕ) (s : Fin 2) (n : ℕ) : Prop :=
  (casselsPair s n).x ∈ B ∧ (casselsPair s n).y ∈ B

theorem represented_after_deletion {B D : Finset ℕ} {s : Fin 2} {n : ℕ}
    (hp : HasSelectedPair B s n) (hd : ¬ Hits D s n) :
    Represented (B \ D) n := by
  refine ⟨(casselsPair s n).x, Finset.mem_sdiff.2 ⟨hp.1, fun h => hd (.inl h)⟩,
    (casselsPair s n).y, Finset.mem_sdiff.2 ⟨hp.2, fun h => hd (.inr h)⟩, (casselsPair s n).sum_eq⟩

/-- The installed witness and the set retained after the endpoint replacement. -/
def witnessCore (B D R : Finset ℕ) (a N : ℕ) : Finset ℕ :=
  insert (N - a) ((B \ D) ∪ R)

/-- Once the finite background and admissible shifts are supplied, the completed
    stage covers its full range and preserves the chosen witness. -/
theorem finish_finite_stage (B D R : Finset ℕ) {Y₀ X L N Y a : ℕ}
    (hYX : Y₀ ≤ X) (hXL : 2 * X ≤ L) (hN₀ : 2 * L < N) (hN₁ : N ≤ 3 * L)
    (horizon : 24577 * N ≤ Y) (hL : ∀ s : Fin 2, blockStart s 4 ≤ L)
    (hB : ∀ z ∈ B, z ≤ Y) (hD : ∀ d ∈ D, L < d ∧ d ≤ N)
    (hR : ∀ z ∈ R, X < z ∧ z ≤ Y)
    (h0 : 0 ∈ B) (ha : a ∈ B) (haX : a ≤ X) (hodd : Odd N)
    (hNfree : ¬ Represented ((B \ D) ∪ R) N)
    (hPrefix : ∀ n ≤ Y₀, Represented B n)
    (hBackground : ∀ n, Y₀ < n → n ≤ Y → ∀ s, HasSelectedPair B s n)
    (hShift : ∀ P : Finset ℕ, P.card < 49 * 81921 * D.card ^ 2 →
      (∀ w ∈ P, X < w ∧ w ≤ Y) → ∀ n, 2 * X < n → n < N →
      ∃ u ∈ witnessCore B D R a N ∪ P, u ≤ X ∧ u + (N - n) ∉ witnessCore B D R a N ∪ P) :
    ∃ P : Finset ℕ, P.card ≤ 49 * 81921 * D.card ^ 2 ∧ (∀ w ∈ P, X < w ∧ w ≤ Y) ∧
      let T := witnessCore B D R a N ∪ P
      (∀ n ≤ Y, Represented T n) ∧ AllRepresentationsUse T a N ∧
      (∀ z ∈ T, z ≤ Y) ∧ (∀ z ≤ X, z ∈ T ↔ z ∈ B) := by
  classical
  let S := witnessCore B D R a N
  have hsafe (z : ℕ) (hz : z ≤ X) (hzB : z ∈ B) : z ∈ B \ D :=
    Finset.mem_sdiff.2 ⟨hzB, fun hd => by have hl := (hD z hd).1; omega⟩
  have hsub : B \ D ⊆ S :=
    fun _ hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)
  have h₀ : 0 ∈ S := hsub (hsafe 0 (Nat.zero_le _) h0)
  have hN : N ≤ Y := by omega
  have hbW : X < N - a := by omega
  have hW := install_witness (Finset.mem_union_left R (hsafe a haX ha)) (by omega : a ≤ N) hNfree
  let H := (Finset.range (Y + 1)).filter fun n => n ≠ N ∧ Hits D 0 n ∧ Hits D 1 n
  have hHcard : H.card ≤ 49 * 81921 * D.card ^ 2 :=
    collateral_card_le hL hN₁ hD fun n hn => (Finset.mem_filter.1 hn).2.2
  have hH (n : ℕ) (hn : n ∈ H) : 2 * X < n ∧ n ≤ Y ∧ n ≠ N := by
    obtain ⟨hnY, hnN, hhit, _⟩ := Finset.mem_filter.1 hn
    have hm : blockStart 0 2 ≤ L :=
      ((blockStart_strictMono 0).monotone (by decide : 2 ≤ 4)).trans (hL 0)
    have hl := (hit_sum_bounds hm hD hhit).1
    exact ⟨hXL.trans_lt hl, Nat.lt_succ_iff.1 (Finset.mem_range.1 hnY), hnN⟩
  obtain ⟨P, hPc, hPb, hholes, hforced⟩ := repair_holes S H hodd h₀ hW.2 hH
    (fun P hp hb n hn hlt => hShift P (hp.trans_le hHcard) hb n (hH n hn).1 hlt)
  refine ⟨P, hPc.trans hHcard, hPb, ?_, hforced, ?_, ?_⟩
  · intro n hn
    by_cases hn₀ : n ≤ Y₀
    · obtain ⟨x, hx, y, hy, he⟩ := hPrefix n hn₀
      exact ⟨x, Finset.mem_union_left _ (hsub (hsafe x (by omega) hx)),
        y, Finset.mem_union_left _ (hsub (hsafe y (by omega) hy)), he⟩
    by_cases hnN : n = N
    · subst n
      exact hW.1.mono fun _ hx => Finset.mem_union_left _ hx
    by_cases hh : Hits D 0 n ∧ Hits D 1 n
    · exact hholes n (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hnN, hh⟩)
    have survive (s : Fin 2) (hs : ¬ Hits D s n) : Represented (S ∪ P) n :=
      (represented_after_deletion (hBackground n (by omega) hn s) hs).mono
        (fun _ hx => Finset.mem_union_left _ (hsub hx))
    by_cases hz : Hits D 0 n
    · exact survive 1 (fun ho => hh ⟨hz, ho⟩)
    · exact survive 0 hz
  · intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    · rcases Finset.mem_insert.1 hz with rfl | hz
      · exact (Nat.sub_le _ _).trans hN
      · rcases Finset.mem_union.1 hz with hb | hr
        · exact hB z (Finset.mem_sdiff.1 hb).1
        · exact (hR z hr).2
    · exact (hPb z hz).2
  · intro z hz
    constructor
    · intro hzt
      rcases Finset.mem_union.1 hzt with hzs | hzp
      · rcases Finset.mem_insert.1 hzs with he | hz'
        · omega
        · rcases Finset.mem_union.1 hz' with hb | hr
          · exact (Finset.mem_sdiff.1 hb).1
          · exact (not_lt_of_ge hz (hR z hr).1).elim
      · exact (not_lt_of_ge hz (hPb z hzp).1).elim
    · exact fun hzb => Finset.mem_union_left _ (hsub (hsafe z hz hzb))

end Erdos326
