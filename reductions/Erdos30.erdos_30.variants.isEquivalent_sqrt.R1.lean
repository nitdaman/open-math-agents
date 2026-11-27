import FormalConjectures.ErdosProblems.«30»
import Mathlib.Tactic

-- Reduction Erdos30.erdos_30.variants.isEquivalent_sqrt.R1 of Erdős Problem 30 — isEquivalent sqrt
-- Credit: @malikfassi
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- h(N) ~ √N is a lower bound and an upper bound glued together:
--   H1  the lower bound h(N) ≥ (1 - ε) √N for large N (the statement of the Singer variant of
--       this problem, itself reduced to primes in short intervals and a dense Sidon set per prime);
--   H2  Lindström's upper bound h(N) ≤ √N + N^(1/4) + 1 for every N (the statement of the
--       Lindström variant of this problem, which has a merged proof in this repository).
-- `main` only needs that N^(1/4) + 1 ≤ c √N once N^(1/4) ≥ max 1 (2 / c).

namespace OMA.R_Erdos30_erdos_30_variants_isEquivalent_sqrt_R1

def H1 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, (1 - ε) * (N : ℝ).sqrt ≤ (Erdos30.h N : ℝ)

def H2 : Prop :=
  ∀ N : ℕ, (Erdos30.h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

theorem main : H1 → H2 → type_of% @Erdos30.erdos_30.variants.isEquivalent_sqrt := by
  intro h1 h2
  rw [Asymptotics.IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  have hlow := h1 c hc
  have hbig : ∀ᶠ N : ℕ in Filter.atTop, max 1 (2 / c) ^ 4 ≤ (N : ℝ) := by
    rw [Filter.eventually_atTop]
    exact ⟨⌈max 1 (2 / c) ^ 4⌉₊, fun N hN => (Nat.le_ceil _).trans (by exact_mod_cast hN)⟩
  filter_upwards [hlow, hbig] with N hN1 hN2
  have hup := h2 N
  have hT1 : (1 : ℝ) ≤ max 1 (2 / c) := le_max_left _ _
  have hT2 : 2 / c ≤ max 1 (2 / c) := le_max_right _ _
  have hT0 : (0 : ℝ) ≤ max 1 (2 / c) := le_trans zero_le_one hT1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN2
  have htT : max 1 (2 / c) ≤ (N : ℝ) ^ (4⁻¹ : ℝ) := by
    have h4 : ((max 1 (2 / c)) ^ 4 : ℝ) ^ (4⁻¹ : ℝ) = max 1 (2 / c) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
      norm_num
    calc max 1 (2 / c) = ((max 1 (2 / c)) ^ 4 : ℝ) ^ (4⁻¹ : ℝ) := h4.symm
      _ ≤ (N : ℝ) ^ (4⁻¹ : ℝ) := Real.rpow_le_rpow (by positivity) hN2 (by norm_num)
  have htt : (N : ℝ) ^ (4⁻¹ : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) = (N : ℝ).sqrt := by
    rw [← Real.rpow_add hNpos, Real.sqrt_eq_rpow]
    norm_num
  have ht1 : (1 : ℝ) ≤ (N : ℝ) ^ (4⁻¹ : ℝ) := hT1.trans htT
  have hct : 2 ≤ c * (N : ℝ) ^ (4⁻¹ : ℝ) := by
    have h2c : 2 / c ≤ (N : ℝ) ^ (4⁻¹ : ℝ) := hT2.trans htT
    rw [div_le_iff₀ hc] at h2c
    linarith
  have hkey : (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ c * ((N : ℝ) ^ (4⁻¹ : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ)) := by
    nlinarith
  rw [htt] at hkey
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_le]
  constructor
  · linarith
  · linarith

end OMA.R_Erdos30_erdos_30_variants_isEquivalent_sqrt_R1
