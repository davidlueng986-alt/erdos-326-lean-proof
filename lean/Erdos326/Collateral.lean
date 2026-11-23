module

public import Erdos326.Cassels
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

open scoped BigOperators

namespace Erdos326

/-- The selected representation records the block of each summand. -/
structure CasselsPair (s : Fin 2) (n : ℕ) where
  i : ℕ
  j : ℕ
  x : ℕ
  y : ℕ
  idx_le : i ≤ j
  idx_close : j ≤ i + 2
  left_mem : x ∈ casselsBlock s i
  right_mem : y ∈ casselsBlock s j
  sum_eq : x + y = n

theorem nonempty_casselsPair (s : Fin 2) (n : ℕ) : Nonempty (CasselsPair s n) := by
  obtain ⟨i, j, hi, hj, x, hx, y, hy, hxy⟩ := cassels_nearby_representation s n
  exact ⟨⟨i, j, x, y, hi, hj, hx, hy, hxy⟩⟩

noncomputable def casselsPair (s : Fin 2) (n : ℕ) : CasselsPair s n :=
  Classical.choice (nonempty_casselsPair s n)

def Hits (D : Finset ℕ) (s : Fin 2) (n : ℕ) : Prop :=
  (casselsPair s n).x ∈ D ∨ (casselsPair s n).y ∈ D

private lemma hit_witness {D : Finset ℕ} {s : Fin 2} {n : ℕ}
    (h : Hits D s n) :
    ∃ d ∈ D, ∃ i j, ∃ z ∈ casselsBlock s j,
      d ∈ casselsBlock s i ∧ j ≤ i + 2 ∧ i ≤ j + 2 ∧ d + z = n := by
  let r := casselsPair s n
  rcases h with hx | hy
  · exact ⟨r.x, hx, r.i, r.j, r.y, r.right_mem, r.left_mem, r.idx_close,
      r.idx_le.trans (Nat.le_add_right _ _), r.sum_eq⟩
  · exact ⟨r.y, hy, r.j, r.i, r.x, r.left_mem, r.right_mem,
      r.idx_le.trans (Nat.le_add_right _ _), r.idx_close, (Nat.add_comm _ _).trans r.sum_eq⟩

private lemma ge_index_of_mem_above {s : Fin 2} {i d k : ℕ}
    (hd : d ∈ casselsBlock s i) (hk : blockStart s k < d) : k ≤ i := by
  by_contra! h
  exact (not_lt_of_ge ((mem_casselsBlock_bounds hd).2.trans
    ((blockStart_strictMono s).monotone (Nat.succ_le_of_lt h)))) hk

/-- A deletion in `(L,U]` can only destroy the chosen representation in a bounded larger range. -/
theorem hit_sum_bounds {D : Finset ℕ} {s : Fin 2} {n L U : ℕ}
    (hL : blockStart s 2 ≤ L) (hD : ∀ d ∈ D, L < d ∧ d ≤ U)
    (h : Hits D s n) : L < n ∧ n ≤ 24577 * U := by
  obtain ⟨d, hdD, i, j, z, hz, hd, hj, _, hsum⟩ := hit_witness h
  obtain ⟨hdl, hdu⟩ := hD d hdD
  have hi := ge_index_of_mem_above hd (hL.trans_lt hdl)
  have hscale := (le_blockStart s hi).trans (mem_casselsBlock_bounds hd).1
  have hzle : z ≤ 24576 * d := calc
    z ≤ blockStart s (j + 1) := (mem_casselsBlock_bounds hz).2
    _ ≤ blockStart s (i + 3) := (blockStart_strictMono s).monotone (by omega)
    _ ≤ 6 * scale s ^ 2 * 16 ^ (i + 3) := blockStart_le s _
    _ = 24576 * (scale s ^ 2 * 16 ^ i) := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hscale
  omega

/-- The intersection of two translated bounded progressions with coprime steps. -/
theorem card_of_coprime_progressions {F : Finset ℕ} {a b p q M N : ℕ}
    (hp : 0 < p) (hc : p.Coprime q)
    (hF : ∀ n ∈ F, ∃ t ≤ M, ∃ u ≤ N, n = a + t * p ∧ n = b + u * q) :
    F.card ≤ M / q + 1 := by
  let coord (n : ℕ) := (n - a) / p
  have hcoord (n : ℕ) (hn : n ∈ F) :
      n = a + coord n * p ∧ coord n ≤ M ∧ n ≡ b [MOD q] := by
    obtain ⟨t, ht, u, _, hna, hnb⟩ := hF n hn
    have hsub : n - a = t * p := by omega
    have heq : coord n = t := by
      rw [show coord n = (n - a) / p by rfl, hsub, Nat.mul_div_cancel _ hp]
    refine ⟨by rwa [heq], by rwa [heq], ?_⟩
    rw [hnb]
    have hd : q ∣ u * q := ⟨u, Nat.mul_comm _ _⟩
    simpa only [Nat.add_zero] using (Nat.modEq_zero_iff_dvd.2 hd).add_left b
  rw [← Finset.card_range (M / q + 1)]
  apply Finset.card_le_card_of_injOn (fun n => coord n / q)
  · intro n hn
    have hh := Nat.div_le_div_right (c := q) (hcoord n hn).2.1
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hh)
  · intro n hn m hm heq
    obtain ⟨hna, _, hnb⟩ := hcoord n hn
    obtain ⟨hma, _, hmb⟩ := hcoord m hm
    have hmod := hnb.trans hmb.symm
    rw [hna, hma] at hmod
    have hrem := Nat.ModEq.cancel_right_of_coprime hc.symm
      (Nat.ModEq.add_left_cancel' a hmod)
    have hcEq : coord n = coord m := by
      change coord n / q = coord m / q at heq
      change coord n % q = coord m % q at hrem
      calc
        coord n = coord n % q + q * (coord n / q) := (Nat.mod_add_div _ _).symm
        _ = coord m % q + q * (coord m / q) := by rw [heq, hrem]
        _ = coord m := Nat.mod_add_div _ _
    rw [hna, hma, hcEq]

private lemma block_indices_close {s t : Fin 2} {i j d e : ℕ}
    (hi : 2 ≤ i) (hd : d ∈ casselsBlock s i) (he : e ∈ casselsBlock t j)
    (hratio : d ≤ 3 * e) : i ≤ j + 2 := by
  by_contra! hlarge
  have hlo := (le_blockStart s hi).trans (mem_casselsBlock_bounds hd).1
  have hhi := (mem_casselsBlock_bounds he).2.trans (blockStart_le t (j + 1))
  have hs : 9 ≤ scale s ^ 2 := by rcases scale_cases s with h | h <;> rw [h] <;> decide
  have ht : scale t ^ 2 ≤ 36 := by rcases scale_cases t with h | h <;> rw [h] <;> decide
  have hpow : (16 : ℕ) ^ (j + 1) * 256 ≤ 16 ^ i := by
    rw [show (256 : ℕ) = 16 ^ 2 by decide, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hd' : 2304 * 16 ^ (j + 1) ≤ d := calc
    _ = 9 * (16 ^ (j + 1) * 256) := by ring
    _ ≤ scale s ^ 2 * 16 ^ i := Nat.mul_le_mul hs hpow
    _ ≤ d := hlo
  have he' : e ≤ 216 * 16 ^ (j + 1) := calc
    e ≤ 6 * scale t ^ 2 * 16 ^ (j + 1) := hhi
    _ ≤ 216 * 16 ^ (j + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 ht)
  have hpos : 0 < (16 : ℕ) ^ (j + 1) := by positivity
  omega

private lemma blockSize_div_le {i j : ℕ} (hj : 0 < j) (hij : i ≤ j + 6) :
    blockSize 0 i / qSeq 1 j ≤ 81920 := by
  have hi := (blockSize_bounds 0 i).2
  have hq := (qSeq_bounds_of_pos 1 hj).1
  have hz : scale 0 = 3 := by decide
  have ho : scale 1 = 6 := by decide
  rw [hz] at hi
  rw [ho] at hq
  have hm : blockSize 0 i ≤ 81920 * qSeq 1 j := calc
    _ ≤ 120 * 4 ^ i := hi
    _ ≤ 120 * 4 ^ (j + 6) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hij)
    _ = 81920 * (6 * 4 ^ j) := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hq.le
  calc
    _ ≤ (81920 * qSeq 1 j) / qSeq 1 j := Nat.div_le_div_right hm
    _ = _ := Nat.mul_div_cancel _ (qSeq_pos 1 j)

/-- A bounded deletion set disables both selected representations at only a bounded
    number of integers. The bound is uniform in the numerical location of the stage. -/
theorem collateral_card_le {D H : Finset ℕ} {L U : ℕ}
    (hL : ∀ s : Fin 2, blockStart s 4 ≤ L) (hU : U ≤ 3 * L)
    (hD : ∀ d ∈ D, L < d ∧ d ≤ U)
    (hH : ∀ n ∈ H, Hits D 0 n ∧ Hits D 1 n) :
    H.card ≤ 49 * 81921 * D.card ^ 2 := by
  classical
  let active (i : ℕ) := ∃ s : Fin 2, ∃ d, L < d ∧ d ≤ U ∧ d ∈ casselsBlock s i
  by_cases hex : ∃ i, active i
  · let lo := Nat.find hex
    obtain ⟨s₀, d₀, hd₀l, _, hd₀⟩ := Nat.find_spec hex
    have hlo : 4 ≤ lo := ge_index_of_mem_above hd₀ ((hL s₀).trans_lt hd₀l)
    have active_bounds {i : ℕ} (hi : active i) : lo ≤ i ∧ i ≤ lo + 2 := by
      have hl := Nat.find_min' hex hi
      obtain ⟨s, d, hdl, hdu, hd⟩ := hi
      have hi4 : 4 ≤ i := ge_index_of_mem_above hd ((hL s).trans_lt hdl)
      exact ⟨hl, block_indices_close (by omega) hd hd₀ (by omega)⟩
    let I : Finset ℕ := Finset.Icc (lo - 2) (lo + 4)
    let keys := (D ×ˢ D) ×ˢ (I ×ˢ I)
    let slice (key : (ℕ × ℕ) × (ℕ × ℕ)) := H.filter fun n =>
      (∃ x ∈ casselsBlock 0 key.2.1, key.1.1 + x = n) ∧
      (∃ y ∈ casselsBlock 1 key.2.2, key.1.2 + y = n)
    have hcover : H ⊆ keys.biUnion slice := by
      intro n hn
      obtain ⟨h₀, h₁⟩ := hH n hn
      obtain ⟨d, hdd, i, j, x, hx, hd, hj, hi, hdx⟩ := hit_witness h₀
      obtain ⟨e, hee, k, l, y, hy, he, hl, hk, hey⟩ := hit_witness h₁
      obtain ⟨hdi, hid⟩ := active_bounds ⟨0, d, (hD d hdd).1, (hD d hdd).2, hd⟩
      obtain ⟨hek, hke⟩ := active_bounds ⟨1, e, (hD e hee).1, (hD e hee).2, he⟩
      have hjI : j ∈ I := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hlI : l ∈ I := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      exact Finset.mem_biUnion.2 ⟨((d, e), (j, l)),
        Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hdd, hee⟩, Finset.mem_product.2 ⟨hjI, hlI⟩⟩,
        Finset.mem_filter.2 ⟨hn, ⟨x, hx, hdx⟩, ⟨y, hy, hey⟩⟩⟩
    have hslice (key : (ℕ × ℕ) × (ℕ × ℕ)) (hk : key ∈ keys) : (slice key).card ≤ 81921 := by
      rcases key with ⟨⟨d, e⟩, ⟨i, j⟩⟩
      obtain ⟨hiI, hjI⟩ := Finset.mem_product.1 (Finset.mem_product.1 hk).2
      have hi : lo - 2 ≤ i ∧ i ≤ lo + 4 := Finset.mem_Icc.1 hiI
      have hj : lo - 2 ≤ j ∧ j ≤ lo + 4 := Finset.mem_Icc.1 hjI
      have hlocal (n : ℕ) (hn : n ∈ slice ((d, e), (i, j))) :
          ∃ t ≤ blockSize 0 i, ∃ u ≤ blockSize 1 j,
            n = (d + blockStart 0 i) + t * qSeq 0 i ∧
            n = (e + blockStart 1 j) + u * qSeq 1 j := by
        obtain ⟨⟨x, ⟨t, ht, rfl⟩, hx⟩, ⟨y, ⟨u, hu, rfl⟩, hy⟩⟩ :=
          (Finset.mem_filter.1 hn).2
        change d + (blockStart 0 i + t * qSeq 0 i) = n at hx
        change e + (blockStart 1 j + u * qSeq 1 j) = n at hy
        exact ⟨t, ht, u, hu, by omega, by omega⟩
      have h := card_of_coprime_progressions (qSeq_pos 0 i)
        (qSeq_coprime_cross i j) hlocal
      have hr := blockSize_div_le (i := i) (j := j) (by omega) (by omega)
      omega
    have hI : I.card = 7 := by
      change (Finset.Icc (lo - 2) (lo + 4)).card = 7
      rw [Nat.card_Icc]
      omega
    calc
      H.card ≤ (keys.biUnion slice).card := Finset.card_le_card hcover
      _ ≤ ∑ key ∈ keys, (slice key).card := Finset.card_biUnion_le
      _ ≤ ∑ key ∈ keys, (81921 : ℕ) := Finset.sum_le_sum hslice
      _ = 49 * 81921 * D.card ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [keys, Finset.card_product, hI, Nat.cast_id]
        ring
  · have hempty : H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro n hn
      obtain ⟨d, hdd, i, _, _, _, hd, _, _, _⟩ := hit_witness (hH n hn).1
      exact hex ⟨i, 0, d, (hD d hdd).1, (hD d hdd).2, hd⟩
    simp [hempty]

end Erdos326
