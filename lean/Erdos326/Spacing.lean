module

public import Erdos326.Cassels
public import Erdos326.Assembly

@[expose] public section

namespace Erdos326

private lemma half_open_block {s : Fin 2} {x : ℕ} (hx : x ∈ casselsBasis s) :
    ∃ i, x ∈ casselsBlock s i ∧ x < blockStart s (i + 1) := by
  obtain ⟨i, hi⟩ := mem_casselsBasis.1 hx
  have hle := (mem_casselsBlock_bounds hi).2
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact ⟨i, hi, hlt⟩
  · refine ⟨i + 1, ⟨0, Nat.zero_le _, by simpa using heq⟩, ?_⟩
    rw [heq]
    exact blockStart_strictMono s (by omega)

private lemma blockStart_le_step_squared (s : Fin 2) {i : ℕ} (hi : 0 < i) :
    blockStart s (i + 1) ≤ 96 * qSeq s i ^ 2 := by
  have h := (qSeq_bounds_of_pos s hi).1.le
  calc
    _ ≤ 6 * scale s ^ 2 * 16 ^ (i + 1) := blockStart_le s _
    _ = 96 * (scale s * 4 ^ i) ^ 2 := by
      rw [pow_succ, show (16 : ℕ) = 4 * 4 by decide, mul_pow]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)

/-- Distinct terms of the same Cassels basis are separated at the square-root scale. -/
theorem cassels_gap {s : Fin 2} {x y : ℕ}
    (hx : x ∈ casselsBasis s) (hy : y ∈ casselsBasis s)
    (hx₀ : blockStart s 1 ≤ x) (hxy : x < y) :
    x < 96 * (y - x) ^ 2 := by
  obtain ⟨i, hix, hxi⟩ := half_open_block hx
  obtain ⟨j, hjy, hyj⟩ := half_open_block hy
  have hi : 0 < i := by
    by_contra! h
    have hi0 : i = 0 := by omega
    subst i
    exact (not_lt_of_ge hx₀) (show x < blockStart s 1 from hxi)
  have hij : i ≤ j := by
    by_contra! h
    have hstart := (blockStart_strictMono s).monotone (show j + 1 ≤ i by omega)
    exact (not_lt_of_ge ((mem_casselsBlock_bounds hix).1.trans' (hyj.le.trans hstart))) hxy
  have hgap : qSeq s i ≤ y - x := by
    rcases lt_or_eq_of_le hij with hlt | rfl
    · obtain ⟨t, ht, hxt⟩ := hix
      have htt : t < blockSize s i := by
        by_contra! h
        have heq : t = blockSize s i := by omega
        rw [heq, ← blockWidth, ← blockStart_succ] at hxt
        omega
      have hm := Nat.mul_le_mul_right (qSeq s i) (Nat.succ_le_of_lt htt)
      rw [Nat.succ_mul, ← blockWidth] at hm
      have hs : blockStart s (i + 1) ≤ blockStart s j :=
        (blockStart_strictMono s).monotone (Nat.succ_le_of_lt hlt)
      have hs' := (mem_casselsBlock_bounds hjy).1
      have he := blockStart_succ s i
      omega
    · obtain ⟨t, _, hxt⟩ := hix
      obtain ⟨u, _, hyu⟩ := hjy
      have htu : t + 1 ≤ u := by
        by_contra! h
        have hm := Nat.mul_le_mul_right (qSeq s i) (show u ≤ t by omega)
        omega
      have hm := Nat.mul_le_mul_right (qSeq s i) htu
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
  exact hxi.trans_le ((blockStart_le_step_squared s hi).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgap 2)))

private lemma close_within_three_bins {m x y : ℕ} (hm : 10009 ≤ m)
    (hx : quadBin m < x) (hy : y ≤ quadBin (m + 3)) :
    100 * (y - x) ^ 2 ≤ x := by
  have hlo : m ^ 2 < 10000 * (quadBin m + 1) := Nat.lt_mul_div_succ _ (by decide)
  have hhi : 10000 * quadBin (m + 3) ≤ (m + 3) ^ 2 := by
    rw [Nat.mul_comm, quadBin]
    exact Nat.div_mul_le_self _ _
  by_cases hxy : x ≤ y
  · have hquad : (m + 3) ^ 2 = m ^ 2 + 6 * m + 9 := by ring
    rw [hquad] at hhi
    have hΔ : 10000 * (y - x) ≤ 7 * m := by omega
    have hpow := Nat.pow_le_pow_left hΔ 2
    have hx' : m ^ 2 < 10000 * x := by omega
    nlinarith only [hpow, hx']
  · simp [Nat.sub_eq_zero_of_le (by omega : y ≤ x)]

/-- After the initial bins, three consecutive quadratic bins contain at most one
    element of either individual Cassels basis. -/
theorem card_basis_in_three_bins_le_one (s : Fin 2) (m : ℕ) (hm : 10009 ≤ m)
    (F : Finset ℕ)
    (hF : ∀ x ∈ F, x ∈ casselsBasis s ∧ quadBin m < x ∧ x ≤ quadBin (m + 3)) :
    F.card ≤ 1 := by
  have hstart : blockStart s 1 ≤ quadBin m := by
    have h := (blockSize_bounds s 0).2
    have hs : blockStart s 1 = blockSize s 0 := by
      change 0 + blockSize s 0 * 1 = _
      omega
    have hb : 10000 ≤ quadBin m :=
      (show 10000 ≤ quadBin 10000 by decide).trans (quadBin_monotone (by omega))
    rw [hs]
    rcases scale_cases s with h₀ | h₀ <;> rw [h₀] at h <;> norm_num at h <;> omega
  have impossible (x y : ℕ) (hx : x ∈ F) (hy : y ∈ F) (hxy : x < y) : False := by
    obtain ⟨hxB, hxlo, _⟩ := hF x hx
    obtain ⟨hyB, _, hyhi⟩ := hF y hy
    have hgap := cassels_gap hxB hyB (hstart.trans hxlo.le) hxy
    have hclose := close_within_three_bins hm hxlo hyhi
    omega
  apply Finset.card_le_one.2
  intro x hx y hy
  rcases lt_trichotomy x y with h | h | h
  · exact (impossible x y hx hy h).elim
  · exact h
  · exact (impossible y x hy hx h).elim

/-- Both bases together contribute at most two points per group of three bins. -/
theorem card_union_in_three_bins_le_two (m : ℕ) (hm : 10009 ≤ m)
    (F : Finset ℕ)
    (hF : ∀ x ∈ F, x ∈ casselsBasis 0 ∪ casselsBasis 1 ∧
      quadBin m < x ∧ x ≤ quadBin (m + 3)) :
    F.card ≤ 2 := by
  classical
  let F₀ := F.filter (· ∈ casselsBasis 0)
  let F₁ := F.filter (· ∈ casselsBasis 1)
  have hc (s : Fin 2) : (F.filter (· ∈ casselsBasis s)).card ≤ 1 := by
    apply card_basis_in_three_bins_le_one s m hm
    intro x hx
    obtain ⟨hxF, hxB⟩ := Finset.mem_filter.1 hx
    exact ⟨hxB, (hF x hxF).2⟩
  have hsub : F ⊆ F₀ ∪ F₁ := by
    intro x hx
    rcases (hF x hx).1 with h | h
    · exact Finset.mem_union.2 (.inl (Finset.mem_filter.2 ⟨hx, h⟩))
    · exact Finset.mem_union.2 (.inr (Finset.mem_filter.2 ⟨hx, h⟩))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le F₀ F₁).trans
    (Nat.add_le_add (hc 0) (hc 1)))

end Erdos326
