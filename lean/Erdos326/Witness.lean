module

public import Erdos326.Assembly
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

open scoped BigOperators

namespace Erdos326

def Represented (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, x + y = n

def AllRepresentationsUse (S : Finset ℕ) (a n : ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x + y = n → x = a ∨ y = a

lemma Represented.mono {S T : Finset ℕ} {n : ℕ} (h : Represented S n) (hST : S ⊆ T) :
    Represented T n := by
  obtain ⟨x, hx, y, hy, he⟩ := h
  exact ⟨x, hST hx, y, hST hy, he⟩

/-- Each unordered non-diagonal representation contributes its larger summand. -/
def upperEndpoints (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  S.filter fun y => y ≤ n ∧ n - y < y ∧ n - y ∈ S

lemma upperEndpoints_above {S : Finset ℕ} {L n y : ℕ}
    (h : 2 * L < n) (hy : y ∈ upperEndpoints S n) : L < y := by
  obtain ⟨_, hle, hlt, _⟩ := Finset.mem_filter.1 hy
  omega

/-- Averaging over a finite set of targets bounds the number of deletions
    needed to annihilate the representations of at least one target. -/
theorem exists_target_with_few_endpoints (S targets : Finset ℕ) (budget : ℕ)
    (hbudget : S.card ^ 2 < targets.card * budget) :
    ∃ n ∈ targets, (upperEndpoints S n).card < budget := by
  let family := targets.sigma (upperEndpoints S)
  have hcard : family.card ≤ (S ×ˢ S).card := by
    apply Finset.card_le_card_of_injOn
      (fun z : Σ _ : ℕ, ℕ => (z.1 - z.2, z.2))
    · intro z hz
      obtain ⟨_, hzm⟩ := Finset.mem_sigma.1 hz
      obtain ⟨hv, _, _, hu⟩ := Finset.mem_filter.1 hzm
      exact Finset.mem_product.2 ⟨hu, hv⟩
    · rintro ⟨n, y⟩ hz ⟨m, v⟩ hw heq
      have hyn := (Finset.mem_filter.1 (Finset.mem_sigma.1 hz).2).2.1
      have hvm := (Finset.mem_filter.1 (Finset.mem_sigma.1 hw).2).2.1
      change (n - y, y) = (m - v, v) at heq
      injection heq with hsub hsum
      have hn : n = m := by
        change y ≤ n at hyn
        change v ≤ m at hvm
        omega
      subst m
      subst v
      rfl
  by_contra! h
  have hsum : targets.card * budget ≤ family.card := calc
    _ = ∑ n ∈ targets, budget := by simp [Finset.sum_const]
    _ ≤ ∑ n ∈ targets, (upperEndpoints S n).card := Finset.sum_le_sum h
    _ = _ := (Finset.card_sigma _ _).symm
  rw [Finset.card_product, ← sq] at hcard
  omega

/-- For an odd target the larger summands suffice, since there are no diagonal sums. -/
theorem not_represented_after_deleting_endpoints (S : Finset ℕ) {n : ℕ} (hn : Odd n) :
    ¬ Represented (S \ upperEndpoints S n) n := by
  have hpar := Nat.odd_iff.1 hn
  rintro ⟨x, hx, y, hy, hxy⟩
  obtain ⟨hxS, hxD⟩ := Finset.mem_sdiff.1 hx
  obtain ⟨hyS, hyD⟩ := Finset.mem_sdiff.1 hy
  by_cases h : x < y
  · exact hyD (Finset.mem_filter.2 ⟨hyS, by omega, by omega, by rwa [show n - y = x by omega]⟩)
  · exact hxD (Finset.mem_filter.2 ⟨hxS, by omega, by omega, by rwa [show n - x = y by omega]⟩)

theorem install_witness {S : Finset ℕ} {a n : ℕ} (ha : a ∈ S) (han : a ≤ n)
    (hs : ¬ Represented S n) :
    Represented (insert (n - a) S) n ∧ AllRepresentationsUse (insert (n - a) S) a n := by
  refine ⟨⟨a, Finset.mem_insert_of_mem ha, n - a, Finset.mem_insert_self _ _, by omega⟩, ?_⟩
  intro x hx y hy he
  rcases Finset.mem_insert.1 hx with h | hx
  · exact .inr (by omega)
  rcases Finset.mem_insert.1 hy with h | hy
  · exact .inl (by omega)
  · exact (hs ⟨x, hx, y, hy, he⟩).elim

/-- A non-diagonal new summand whose complement is absent preserves a witness. -/
lemma retain_witness_after_insert {S : Finset ℕ} {a N w : ℕ} (hodd : Odd N)
    (h : AllRepresentationsUse S a N) (hmiss : ∀ x ∈ S, w + x ≠ N) :
    AllRepresentationsUse (insert w S) a N := by
  have hpar := Nat.odd_iff.1 hodd
  intro x hx y hy hsum
  rcases Finset.mem_insert.1 hx with hxe | hx
  · rcases Finset.mem_insert.1 hy with hye | hy
    · omega
    · exact (hmiss y hy (by omega)).elim
  · rcases Finset.mem_insert.1 hy with hye | hy
    · exact (hmiss x hx (by omega)).elim
    · exact h x hx y hy hsum

/-- Repair one hole by inserting a point above the previously frozen prefix. -/
theorem repair_one_hole (S : Finset ℕ) {a N n X : ℕ} (hodd : Odd N) (h0 : 0 ∈ S)
    (hforced : AllRepresentationsUse S a N) (hn : 2 * X < n) (hne : n ≠ N)
    (havoid : n < N → ∃ u ∈ S, u ≤ X ∧ u + (N - n) ∉ S) :
    ∃ w, X < w ∧ w ≤ n ∧
      Represented (insert w S) n ∧ AllRepresentationsUse (insert w S) a N := by
  by_cases h : n < N
  · obtain ⟨u, hu, hux, hum⟩ := havoid h
    let w := n - u
    refine ⟨w, by dsimp [w]; omega, Nat.sub_le _ _,
      ⟨u, Finset.mem_insert_of_mem hu, w, Finset.mem_insert_self _ _, by dsimp [w]; omega⟩, ?_⟩
    apply retain_witness_after_insert hodd hforced
    intro x hx he
    have hxe : x = u + (N - n) := by dsimp [w] at he; omega
    exact hum (hxe ▸ hx)
  · refine ⟨n, by omega, le_rfl,
      ⟨0, Finset.mem_insert_of_mem h0, n, Finset.mem_insert_self _ _, by simp⟩, ?_⟩
    apply retain_witness_after_insert hodd hforced
    intro x _
    omega

/-- Repair a finite family of holes using at most one new point per hole.
    It suffices to have an available shift for each hole below the witness target,
    uniformly over the additions already made. -/
theorem repair_holes (S H : Finset ℕ) {a N X Y : ℕ}
    (hodd : Odd N) (h0 : 0 ∈ S) (hforced : AllRepresentationsUse S a N)
    (hH : ∀ n ∈ H, 2 * X < n ∧ n ≤ Y ∧ n ≠ N)
    (havoid : ∀ P : Finset ℕ, P.card < H.card → (∀ w ∈ P, X < w ∧ w ≤ Y) →
      ∀ n ∈ H, n < N → ∃ u ∈ S ∪ P, u ≤ X ∧ u + (N - n) ∉ S ∪ P) :
    ∃ P : Finset ℕ, P.card ≤ H.card ∧ (∀ w ∈ P, X < w ∧ w ≤ Y) ∧
      (∀ n ∈ H, Represented (S ∪ P) n) ∧ AllRepresentationsUse (S ∪ P) a N := by
  suffices h : ∀ G ⊆ H, ∃ P : Finset ℕ,
      P.card ≤ G.card ∧ (∀ w ∈ P, X < w ∧ w ≤ Y) ∧
      (∀ n ∈ G, Represented (S ∪ P) n) ∧ AllRepresentationsUse (S ∪ P) a N from
    h H (fun _ hx => hx)
  intro G
  induction G using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, by simp, by simp, by simp, by simpa using hforced⟩
  | insert n G hnG ih =>
    intro hGH
    have hnH : n ∈ H := hGH (Finset.mem_insert_self _ _)
    have hsub : G ⊆ H := fun _ hx => hGH (Finset.mem_insert_of_mem hx)
    obtain ⟨P, hpG, hpB, hpCov, hpForce⟩ := ih hsub
    have hcards : G.card + 1 ≤ H.card := by
      rw [← Finset.card_insert_of_notMem hnG]
      exact Finset.card_le_card hGH
    have hPlt : P.card < H.card := by omega
    obtain ⟨w, hwX, hwn, hRep, hForce⟩ := repair_one_hole (S ∪ P) hodd
      (Finset.mem_union_left _ h0) hpForce (hH n hnH).1 (hH n hnH).2.2
      (havoid P hPlt hpB n hnH)
    have he : insert w (S ∪ P) = S ∪ insert w P := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto
    rw [he] at hRep hForce
    refine ⟨insert w P, ?_, ?_, ?_, hForce⟩
    · rw [Finset.card_insert_of_notMem hnG]
      exact (Finset.card_insert_le w P).trans (Nat.add_le_add_right hpG 1)
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨hwX, hwn.trans (hH n hnH).2.1⟩
      · exact hpB z hz
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hRep
      · exact (hpCov z hz).mono (by
          intro v hv
          rcases Finset.mem_union.1 hv with hv | hv
          · exact Finset.mem_union_left _ hv
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hv))

end Erdos326
