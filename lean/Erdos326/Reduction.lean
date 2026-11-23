module

/- Supporting lemmas for Erdős #326. The existence of the constructed basis is not proved here. -/

public import Mathlib.Data.Nat.Nth
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Tactic

open scoped BigOperators
open Filter Topology

@[expose] public section

namespace Erdos326

/-- A set `S ⊆ ℕ` is an asymptotic additive basis of order 2 if every sufficiently large
    natural number is the sum of two (not necessarily distinct) elements of `S`. -/
def IsAsymptoticBasisOrder2 (S : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ a ∈ S, ∃ b ∈ S, a + b = n

/-- Minimality: `S` is an asymptotic basis of order 2, and no proper subset of `S` is. -/
def IsMinimalAsymptoticBasisOrder2 (S : Set ℕ) : Prop :=
  IsAsymptoticBasisOrder2 S ∧
    ∀ a ∈ S, ¬ IsAsymptoticBasisOrder2 (S \ {a})

/-- Equivalent witness characterization of minimality: every element `a ∈ S` has infinitely
    many sums `N ∈ S + S` with no representation in `(S \ {a}) + (S \ {a})`. -/
lemma minimal_of_infinitely_many_witnesses (S : Set ℕ)
    (hbasis : IsAsymptoticBasisOrder2 S)
    (hwit : ∀ a ∈ S, ∀ M : ℕ, ∃ N ≥ M,
      (∀ x ∈ S, ∀ y ∈ S, x + y = N → x = a ∨ y = a)) :
    IsMinimalAsymptoticBasisOrder2 S := by
  refine ⟨hbasis, ?_⟩
  intro a ha hsub
  rcases hsub with ⟨N₀, hN₀⟩
  rcases hwit a ha N₀ with ⟨N, hN, huniq⟩
  rcases hN₀ N hN with ⟨x, hx, y, hy, hxy⟩
  rcases huniq x hx.1 y hy.1 hxy with rfl | rfl
  · exact hx.2 rfl
  · exact hy.2 rfl

/-- Shifting a minimal asymptotic basis of order 2 in `ℕ` by `+1` yields a minimal
    asymptotic basis of order 2 consisting strictly of positive integers. -/
def shiftOne (S : Set ℕ) : Set ℕ := (· + 1) '' S

lemma shiftOne_pos (S : Set ℕ) : ∀ x ∈ shiftOne S, 0 < x := by
  rintro x ⟨a, _, rfl⟩
  exact Nat.succ_pos a

lemma shiftOne_minimal (S : Set ℕ) (hS : IsMinimalAsymptoticBasisOrder2 S) :
    IsMinimalAsymptoticBasisOrder2 (shiftOne S) := by
  rcases hS with ⟨⟨N₀, hbasis⟩, hmin⟩
  refine ⟨⟨N₀ + 2, ?_⟩, ?_⟩
  · intro n hn
    have hge : n - 2 ≥ N₀ := by omega
    rcases hbasis (n - 2) hge with ⟨a, ha, b, hb, hab⟩
    refine ⟨a + 1, ⟨a, ha, rfl⟩, b + 1, ⟨b, hb, rfl⟩, ?_⟩
    omega
  · rintro _ ⟨a, ha, rfl⟩ ⟨N₁, hsub⟩
    apply hmin a ha
    refine ⟨N₁, ?_⟩
    intro n hn
    have hge : n + 2 ≥ N₁ := by omega
    rcases hsub (n + 2) hge with ⟨x, ⟨⟨a', ha', rfl⟩, hxne⟩, y, ⟨⟨b', hb', rfl⟩, hyne⟩, hxy⟩
    refine ⟨a', ⟨ha', ?_⟩, b', ⟨hb', ?_⟩, ?_⟩
    · intro heq; subst heq; exact hxne rfl
    · intro heq; subst heq; exact hyne rfl
    · change a' + 1 + (b' + 1) = n + 2 at hxy
      omega

/-- Quadratic bin boundary `b m = ⌊m^2 / 10000⌋`. -/
def quadBin (m : ℕ) : ℕ := m ^ 2 / 10000

private lemma quadBin_bounds (m : ℕ) :
    (m : ℝ) ^ 2 / 10000 - 1 ≤ (quadBin m : ℝ) ∧
    (quadBin m : ℝ) ≤ (m : ℝ) ^ 2 / 10000 := by
  have hlo : m ^ 2 < 10000 * (quadBin m + 1) :=
    Nat.lt_mul_div_succ _ (by decide)
  have hhi : quadBin m * 10000 ≤ m ^ 2 :=
    Nat.div_mul_le_self _ _
  constructor
  · have h : (m : ℝ) ^ 2 < 10000 * ((quadBin m : ℝ) + 1) := by exact_mod_cast hlo
    linarith
  · have h : (quadBin m : ℝ) * 10000 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hhi
    linarith

private lemma tendsto_ratio (d : ℝ) :
    Tendsto (fun k : ℕ => ((k : ℝ) + d) / (k : ℝ)) atTop (𝓝 1) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := d)).div_atTop hcast)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp

/-- A bounded error in the running count implies the normalized enumeration has a limit. -/
lemma quadratic_limit_of_bin_count (C : Set ℕ) (hinf : C.Infinite)
    [DecidablePred (· ∈ C)] (m₀ E : ℕ)
    (hcount : ∀ m ≥ m₀,
      m ≤ Nat.count (· ∈ C) (quadBin m + 1) ∧
      Nat.count (· ∈ C) (quadBin m + 1) ≤ m + E) :
    Tendsto (fun k : ℕ => (Nat.nth (· ∈ C) k : ℝ) / (k : ℝ) ^ 2)
      atTop (𝓝 ((1 : ℝ) / 10000)) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have herror : Tendsto (fun k : ℕ => 1 / (k : ℝ) ^ 2) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop (hcast.atTop_pow₀ (by decide : (2 : ℕ) ≠ 0))
  have hlo := (((tendsto_ratio (-(E : ℝ) - 1)).pow 2).div_const 10000).sub herror
  have hhi := ((tendsto_ratio 1).pow 2).div_const 10000
  simp only [one_pow, sub_zero] at hlo hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (m₀ + E + 2)] with k hk
    have hpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hp := (hcount (k - (E + 1)) (by omega)).2
    have hindex : quadBin (k - (E + 1)) + 1 ≤ Nat.nth (· ∈ C) k :=
      (Nat.count_le_iff_le_nth (p := (· ∈ C)) hinf).mp (by omega)
    have hcastSub : ((k - (E + 1) : ℕ) : ℝ) = (k : ℝ) + (-(E : ℝ) - 1) := by
      rw [Nat.cast_sub (show E + 1 ≤ k by omega), Nat.cast_add, Nat.cast_one]
      ring
    have hb := (quadBin_bounds (k - (E + 1))).1
    rw [hcastSub] at hb
    have hindex' : (quadBin (k - (E + 1)) : ℝ) ≤ (Nat.nth (· ∈ C) k : ℝ) := by
      exact_mod_cast (Nat.le_of_succ_le hindex)
    calc
      _ = (((k : ℝ) + (-(E : ℝ) - 1)) ^ 2 / 10000 - 1) / (k : ℝ) ^ 2 := by
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (hb.trans hindex') (by positivity)
  · filter_upwards [eventually_ge_atTop (m₀ + 1)] with k hk
    have hpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hp := (hcount (k + 1) (by omega)).1
    have hindex : Nat.nth (· ∈ C) k < quadBin (k + 1) + 1 :=
      (Nat.lt_nth_iff_count_lt (p := (· ∈ C)) hinf).mp (by omega)
    have hindex' : (Nat.nth (· ∈ C) k : ℝ) ≤ (quadBin (k + 1) : ℝ) := by
      exact_mod_cast (Nat.lt_succ_iff.mp hindex)
    have hb := (quadBin_bounds (k + 1)).2
    push_cast at hb
    calc
      _ ≤ (((k : ℝ) + 1) ^ 2 / 10000) / (k : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (hindex'.trans hb) (by positivity)
      _ = _ := by field_simp

private lemma basis_mono {S T : Set ℕ} (h : S ⊆ T) :
    IsAsymptoticBasisOrder2 S → IsAsymptoticBasisOrder2 T := by
  rintro ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨a, ha, b, hb, hab⟩
  exact ⟨a, h ha, b, h hb, hab⟩

/-- A basis with unbounded indispensable sums and the stated bin counts gives
    an affirmative answer. The construction supplying these hypotheses is separate. -/
theorem exists_of_stage_properties (C : Set ℕ) (hinf : C.Infinite)
    [DecidablePred (· ∈ C)] (m₀ E : ℕ)
    (hbasis : IsAsymptoticBasisOrder2 C)
    (hwit : ∀ a ∈ C, ∀ M : ℕ, ∃ N ≥ M,
      ∀ x ∈ C, ∀ y ∈ C, x + y = N → x = a ∨ y = a)
    (hcount : ∀ m ≥ m₀,
      m ≤ Nat.count (· ∈ C) (quadBin m + 1) ∧
      Nat.count (· ∈ C) (quadBin m + 1) ≤ m + E) :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      Minimal IsAsymptoticBasisOrder2 (Set.range a) ∧
      Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 (1 / 10000 : ℝ)) := by
  have hrange : Set.range (Nat.nth (· ∈ C)) = C := Nat.range_nth_of_infinite hinf
  refine ⟨Nat.nth (· ∈ C), Nat.nth_strictMono hinf, ?_,
    quadratic_limit_of_bin_count C hinf m₀ E hcount⟩
  rw [hrange]
  refine ⟨hbasis, ?_⟩
  intro T hT hTC a ha
  by_contra haT
  have hsub : T ⊆ C \ {a} := by
    intro t ht
    refine ⟨hTC ht, ?_⟩
    rw [Set.mem_singleton_iff]
    exact fun heq => haT (heq ▸ ht)
  exact (minimal_of_infinitely_many_witnesses C hbasis hwit).2 a ha (basis_mono hsub hT)

end Erdos326

