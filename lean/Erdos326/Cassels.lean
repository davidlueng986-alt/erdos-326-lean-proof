module

public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Erdos326

noncomputable section

def primeBase (s : Fin 2) (i : ℕ) : ℕ :=
  (if s = 0 then 3 else 6) * 4 ^ (i + 1)

lemma primeBase_ne_zero (s : Fin 2) (i : ℕ) : primeBase s i ≠ 0 := by
  unfold primeBase
  split <;> positivity

noncomputable def qSeq (s : Fin 2) : ℕ → ℕ
  | 0 => 1
  | i + 1 => Classical.choose (Nat.bertrand (primeBase s i) (primeBase_ne_zero s i))

lemma qSeq_prime (s : Fin 2) (i : ℕ) : Nat.Prime (qSeq s (i + 1)) :=
  (Classical.choose_spec (Nat.bertrand (primeBase s i) (primeBase_ne_zero s i))).1

lemma qSeq_bounds (s : Fin 2) (i : ℕ) :
    (if s = 0 then 3 else 6) * 4 ^ (i + 1) < qSeq s (i + 1) ∧
    qSeq s (i + 1) ≤ 2 * ((if s = 0 then 3 else 6) * 4 ^ (i + 1)) :=
  (Classical.choose_spec (Nat.bertrand (primeBase s i) (primeBase_ne_zero s i))).2

/-- All prime steps across both sequences `qSeq 0` and `qSeq 1` are pairwise distinct,
    hence pairwise coprime. -/
lemma qSeq_coprime_cross (i j : ℕ) : Nat.Coprime (qSeq 0 i) (qSeq 1 j) := by
  cases i with
  | zero => simp [qSeq]
  | succ i =>
    cases j with
    | zero => simp [qSeq]
    | succ j =>
      have hp0 := qSeq_prime 0 i
      have hp1 := qSeq_prime 1 j
      have hne : qSeq 0 (i + 1) ≠ qSeq 1 (j + 1) := by
        have hb0 := qSeq_bounds 0 i
        have hb1 := qSeq_bounds 1 j
        simp only [ite_true] at hb0
        simp only [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at hb1
        rcases lt_trichotomy i j with hij | rfl | hji
        · have hpow : 4 ^ (i + 1) * 4 ≤ 4 ^ (j + 1) := by
            have : i + 2 ≤ j + 1 := by omega
            calc 4 ^ (i + 1) * 4 = 4 ^ (i + 2) := by ring
            _ ≤ 4 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) this
          omega
        · omega
        · have hpow : 4 ^ (j + 1) * 4 ≤ 4 ^ (i + 1) := by
            have : j + 2 ≤ i + 1 := by omega
            calc 4 ^ (j + 1) * 4 = 4 ^ (j + 2) := by ring
            _ ≤ 4 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) this
          omega
      exact (Nat.coprime_primes hp0 hp1).2 hne

/-- The prime step of either sequence lies in a short interval at each scale. -/
def scale (s : Fin 2) : ℕ := if s = 0 then 3 else 6

lemma scale_cases (s : Fin 2) : scale s = 3 ∨ scale s = 6 := by
  unfold scale
  split <;> simp

lemma scale_pos (s : Fin 2) : 0 < scale s := by
  rcases scale_cases s with h | h <;> omega

lemma qSeq_bounds_of_pos (s : Fin 2) {i : ℕ} (hi : 0 < i) :
    scale s * 4 ^ i < qSeq s i ∧ qSeq s i ≤ 2 * (scale s * 4 ^ i) := by
  cases i with
  | zero => omega
  | succ i => simpa only [scale] using qSeq_bounds s i

lemma qSeq_pos (s : Fin 2) (i : ℕ) : 0 < qSeq s i := by
  cases i with
  | zero =>
    change 0 < 1
    decide
  | succ i => exact (qSeq_prime s i).pos

lemma qSeq_strictMono (s : Fin 2) : StrictMono (qSeq s) := by
  apply strictMono_nat_of_lt_succ
  intro i
  cases i with
  | zero => exact (qSeq_prime s 0).one_lt
  | succ i =>
    have h := (qSeq_bounds_of_pos s (i := i + 1) (by omega)).2
    have h' := (qSeq_bounds_of_pos s (i := i + 1 + 1) (by omega)).1
    rw [pow_succ (4 : ℕ) (i + 1), ← mul_assoc] at h'
    omega

lemma qSeq_coprime (s : Fin 2) {i j : ℕ} (hij : i ≠ j) :
    (qSeq s i).Coprime (qSeq s j) := by
  cases i with
  | zero => simp [qSeq]
  | succ i =>
    cases j with
    | zero => simp [qSeq]
    | succ j =>
      exact (Nat.coprime_primes (qSeq_prime s i) (qSeq_prime s j)).2
        (fun h => hij ((qSeq_strictMono s).injective h))

/-- Highest coefficient in block `i`. -/
def blockSize (s : Fin 2) (i : ℕ) : ℕ := qSeq s (i + 1) + qSeq s (i + 2)

def blockWidth (s : Fin 2) (i : ℕ) : ℕ := blockSize s i * qSeq s i

/-- The first and last terms of block `i` are `blockStart s i` and `blockStart s (i + 1)`. -/
def blockStart (s : Fin 2) : ℕ → ℕ
  | 0 => 0
  | i + 1 => blockStart s i + blockWidth s i

@[simp] lemma blockStart_zero (s : Fin 2) : blockStart s 0 = 0 := rfl

lemma blockStart_succ (s : Fin 2) (i : ℕ) :
    blockStart s (i + 1) = blockStart s i + blockWidth s i := rfl

lemma blockWidth_pos (s : Fin 2) (i : ℕ) : 0 < blockWidth s i := by
  unfold blockWidth blockSize
  exact Nat.mul_pos (Nat.add_pos_left (qSeq_pos s _) _) (qSeq_pos s _)

lemma blockStart_strictMono (s : Fin 2) : StrictMono (blockStart s) :=
  strictMono_nat_of_lt_succ fun i => by
    rw [blockStart_succ]
    exact Nat.lt_add_of_pos_right (blockWidth_pos s i)

lemma blockSize_bounds (s : Fin 2) (i : ℕ) :
    20 * scale s * 4 ^ i < blockSize s i ∧
    blockSize s i ≤ 40 * scale s * 4 ^ i := by
  have h1 := qSeq_bounds_of_pos s (i := i + 1) (by omega)
  have h2 := qSeq_bounds_of_pos s (i := i + 2) (by omega)
  have hr1 : (4 : ℕ) ^ (i + 1) = 4 ^ i * 4 := pow_succ 4 i
  have hr2 : (4 : ℕ) ^ (i + 2) = 4 ^ i * 16 := by
    rw [pow_add]
    norm_num
  rw [hr1, ← mul_assoc] at h1
  rw [hr2, ← mul_assoc] at h2
  unfold blockSize
  constructor
  · calc
      _ = scale s * 4 ^ i * 4 + scale s * 4 ^ i * 16 := by ring
      _ < _ := Nat.add_lt_add h1.1 h2.1
  · calc
      _ ≤ 2 * (scale s * 4 ^ i * 4) + 2 * (scale s * 4 ^ i * 16) :=
        Nat.add_le_add h1.2 h2.2
      _ = _ := by ring

lemma blockWidth_bounds (s : Fin 2) {i : ℕ} (hi : 0 < i) :
    20 * scale s ^ 2 * 16 ^ i < blockWidth s i ∧
    blockWidth s i ≤ 80 * scale s ^ 2 * 16 ^ i := by
  have hq := qSeq_bounds_of_pos s hi
  have hm := blockSize_bounds s i
  unfold blockWidth
  constructor
  · calc
      _ = (20 * scale s * 4 ^ i) * (scale s * 4 ^ i) := by
        rw [show (16 : ℕ) = 4 * 4 by decide, mul_pow]
        ring
      _ < _ := Nat.mul_lt_mul_of_lt_of_le hm.1 hq.1.le (qSeq_pos s i)
  · calc
      _ ≤ (40 * scale s * 4 ^ i) * (2 * (scale s * 4 ^ i)) :=
        Nat.mul_le_mul hm.2 hq.2
      _ = _ := by
        rw [show (16 : ℕ) = 4 * 4 by decide, mul_pow]
        ring

lemma blockWidth_growth (s : Fin 2) (i : ℕ) :
    4 * blockWidth s i ≤ blockWidth s (i + 1) := by
  cases i with
  | zero =>
    have h0 := (blockSize_bounds s 0).2
    have h1 := (blockWidth_bounds s (i := 1) (by decide)).1
    change 4 * (blockSize s 0 * 1) ≤ blockWidth s 1
    rcases scale_cases s with h | h <;> rw [h] at h0 h1 <;> norm_num at h0 h1 <;> omega
  | succ i =>
    have h := (blockWidth_bounds s (i := i + 1) (by omega)).2
    have h' := (blockWidth_bounds s (i := i + 1 + 1) (by omega)).1
    rw [pow_succ (16 : ℕ) (i + 1), ← mul_assoc] at h'
    calc
      _ ≤ 4 * (80 * scale s ^ 2 * 16 ^ (i + 1)) := Nat.mul_le_mul_left 4 h
      _ = 20 * scale s ^ 2 * 16 ^ (i + 1) * 16 := by ring
      _ ≤ _ := h'.le

lemma blockStart_le (s : Fin 2) (i : ℕ) : blockStart s i ≤ 6 * scale s ^ 2 * 16 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hw : blockWidth s i ≤ 80 * scale s ^ 2 * 16 ^ i := by
      by_cases hi : 0 < i
      · exact (blockWidth_bounds s hi).2
      · have hi' : i = 0 := by omega
        subst i
        have hs := (blockSize_bounds s 0).2
        change blockSize s 0 * 1 ≤ 80 * scale s ^ 2 * 16 ^ 0
        rcases scale_cases s with h | h <;> rw [h] at hs ⊢ <;> norm_num at hs ⊢ <;> omega
    rw [blockStart_succ, pow_succ]
    calc
      _ ≤ 6 * scale s ^ 2 * 16 ^ i + 80 * scale s ^ 2 * 16 ^ i := Nat.add_le_add ih hw
      _ = 86 * (scale s ^ 2 * 16 ^ i) := by ring
      _ ≤ 96 * (scale s ^ 2 * 16 ^ i) := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by ring

lemma le_blockStart (s : Fin 2) {i : ℕ} (hi : 2 ≤ i) :
    scale s ^ 2 * 16 ^ i ≤ blockStart s i := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
  have h := (blockWidth_bounds s (i := i) (by omega)).1
  change scale s ^ 2 * 16 ^ (i + 1) ≤ blockStart s (i + 1)
  rw [blockStart_succ, pow_succ]
  calc
    _ = 16 * (scale s ^ 2 * 16 ^ i) := by ring
    _ ≤ 20 * (scale s ^ 2 * 16 ^ i) := Nat.mul_le_mul_right _ (by decide)
    _ = 20 * scale s ^ 2 * 16 ^ i := by ring
    _ ≤ _ := h.le.trans (Nat.le_add_left _ _)

/-- A Cassels block, including its shared endpoint with the next block. -/
def casselsBlock (s : Fin 2) (i : ℕ) : Set ℕ :=
  {x | ∃ t ≤ blockSize s i, x = blockStart s i + t * qSeq s i}

def casselsBasis (s : Fin 2) : Set ℕ := ⋃ i, casselsBlock s i

lemma mem_casselsBasis {s : Fin 2} {x : ℕ} :
    x ∈ casselsBasis s ↔ ∃ i, x ∈ casselsBlock s i :=
  Set.mem_iUnion

lemma mem_casselsBlock_bounds {s : Fin 2} {i x : ℕ} (hx : x ∈ casselsBlock s i) :
    blockStart s i ≤ x ∧ x ≤ blockStart s (i + 1) := by
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [blockStart_succ, blockWidth]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _

/-- An interval of exactly `q` coefficient choices can realize any residue. -/
private lemma residue_window (p q b n lo : ℕ) (hpq : p.Coprime q) (hq : 0 < q) :
    ∃ t, lo ≤ t ∧ t < lo + q ∧ b + t * p ≡ n [MOD q] := by
  let _ : NeZero q := ⟨hq.ne'⟩
  let u := ZMod.unitOfCoprime p hpq
  let z : ZMod q := ((n : ZMod q) - b - lo * p) * ↑u⁻¹
  refine ⟨lo + z.val, Nat.le_add_right _ _, Nat.add_lt_add_left (ZMod.val_lt z) _, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).1
  have hu : (p : ZMod q) = ↑u := (ZMod.coe_unitOfCoprime p hpq).symm
  have hz : z * (p : ZMod q) = (n : ZMod q) - b - lo * p := by
    rw [hu, show z = ((n : ZMod q) - b - lo * p) * ↑u⁻¹ by rfl, mul_assoc, ← Units.val_mul]
    simp [← hu]
  push_cast
  rw [ZMod.natCast_zmod_val]
  calc
    _ = (b : ZMod q) + lo * p + z * p := by ring
    _ = _ := by rw [hz]; ring

/-- Fill the second progression after matching the residue with the first. -/
private lemma block_sum_of_window (s : Fin 2) (i j lo n : ℕ)
    (hc : (qSeq s i).Coprime (qSeq s j))
    (hwin : ∀ t, lo ≤ t → t < lo + qSeq s j →
      t ≤ blockSize s i ∧
      blockStart s i + blockStart s j + t * qSeq s i ≤ n ∧
      n ≤ blockStart s i + blockStart s j + t * qSeq s i + blockWidth s j) :
    ∃ x ∈ casselsBlock s i, ∃ y ∈ casselsBlock s j, x + y = n := by
  obtain ⟨t, htl, htu, htmod⟩ := residue_window
    (qSeq s i) (qSeq s j) (blockStart s i + blockStart s j) n lo hc (qSeq_pos s j)
  obtain ⟨ht, hl, hu⟩ := hwin t htl htu
  obtain ⟨v, hv⟩ := (Nat.modEq_iff_dvd' hl).1 htmod
  have hpv : v * qSeq s j ≤ blockSize s j * qSeq s j := by
    rw [mul_comm v, ← hv, ← blockWidth]
    omega
  refine ⟨blockStart s i + t * qSeq s i, ⟨t, ht, rfl⟩,
    blockStart s j + v * qSeq s j,
    ⟨v, Nat.le_of_mul_le_mul_right hpv (qSeq_pos s j), rfl⟩, ?_⟩
  rw [mul_comm v]
  omega

/-- The two coverage intervals used at each Cassels scale overlap. -/
lemma cassels_cover_interval (s : Fin 2) (i n : ℕ)
    (hlo : 2 * blockStart s (i + 1) ≤ n)
    (hhi : n ≤ 2 * blockStart s (i + 2)) :
    ∃ j, i ≤ j ∧ j ≤ i + 2 ∧
      ∃ x ∈ casselsBlock s i, ∃ y ∈ casselsBlock s j, x + y = n := by
  have hsize : blockSize s i = qSeq s (i + 1) + qSeq s (i + 2) := rfl
  have hstart₁ := blockStart_succ s i
  have hstart₂ : blockStart s (i + 2) = blockStart s (i + 1) + blockWidth s (i + 1) :=
    blockStart_succ s (i + 1)
  by_cases hn : n ≤ blockStart s i + blockStart s (i + 2) +
      (qSeq s (i + 2) + 1) * qSeq s i
  · refine ⟨i + 1, by omega, by omega, ?_⟩
    apply block_sum_of_window s i (i + 1) (qSeq s (i + 2) + 1) n
      (qSeq_coprime s (by omega))
    intro t htlo hthi
    have ht : t ≤ blockSize s i := by omega
    have hmul₁ := Nat.mul_le_mul_right (qSeq s i) ht
    have hmul₂ := Nat.mul_le_mul_right (qSeq s i) htlo
    rw [← blockWidth] at hmul₁
    exact ⟨ht, by omega, by omega⟩
  · refine ⟨i + 2, by omega, by omega, ?_⟩
    apply block_sum_of_window s i (i + 2) 0 n (qSeq_coprime s (by omega))
    intro t _ hthi
    have ht : t ≤ blockSize s i := by omega
    have hmul := Nat.mul_le_mul_right (qSeq s i)
      (show t ≤ qSeq s (i + 2) + 1 by omega)
    have hg₁ := blockWidth_growth s i
    have hg₂ : 4 * blockWidth s (i + 1) ≤ blockWidth s (i + 2) :=
      blockWidth_growth s (i + 1)
    exact ⟨ht, by omega, by omega⟩

/-- Every integer is a sum of two terms in blocks at distance at most two. -/
theorem cassels_nearby_representation (s : Fin 2) (n : ℕ) :
    ∃ i j, i ≤ j ∧ j ≤ i + 2 ∧
      ∃ x ∈ casselsBlock s i, ∃ y ∈ casselsBlock s j, x + y = n := by
  by_cases hn : n ≤ 2 * blockStart s 1
  · have hstart : blockStart s 1 = blockSize s 0 := by
      change 0 + blockSize s 0 * 1 = _
      omega
    rw [hstart] at hn
    refine ⟨0, 0, le_rfl, by decide, min n (blockSize s 0), ?_,
      n - min n (blockSize s 0), ?_, ?_⟩
    · refine ⟨min n (blockSize s 0), min_le_right _ _, ?_⟩
      change _ = 0 + _ * 1
      omega
    · refine ⟨n - min n (blockSize s 0), ?_, ?_⟩
      · omega
      · change _ = 0 + _ * 1
        omega
    · omega
  · have hex : ∃ j, n < 2 * blockStart s j := by
      have h : n + 1 ≤ blockStart s (n + 1) := (blockStart_strictMono s).id_le (n + 1)
      exact ⟨n + 1, by omega⟩
    let j := Nat.find hex
    have hj : n < 2 * blockStart s j := Nat.find_spec hex
    have h2 : 2 ≤ j := by
      by_contra! hl
      have h := (blockStart_strictMono s).monotone (show j ≤ 1 by omega)
      omega
    let i := j - 2
    have hir : i + 2 = j := by dsimp [i]; omega
    have hlt := Nat.find_min hex (show i + 1 < j by omega)
    obtain ⟨k, hik, hki, x, hx, y, hy, hxy⟩ :=
      cassels_cover_interval s i n (Nat.le_of_not_gt hlt) (by simpa only [hir] using hj.le)
    exact ⟨i, k, hik, hki, x, hx, y, hy, hxy⟩

theorem cassels_basis_covers (s : Fin 2) (n : ℕ) :
    ∃ x ∈ casselsBasis s, ∃ y ∈ casselsBasis s, x + y = n := by
  obtain ⟨i, j, _, _, x, hx, y, hy, hxy⟩ := cassels_nearby_representation s n
  exact ⟨x, mem_casselsBasis.2 ⟨i, hx⟩, y, mem_casselsBasis.2 ⟨j, hy⟩, hxy⟩

end

end Erdos326
