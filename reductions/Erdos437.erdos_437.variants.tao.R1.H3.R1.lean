import OMAReductions.R_Erdos437_erdos_437_variants_tao_R1
import Mathlib

/-!
Tao's argument for Erdős 437 uses two theorems about the Dickman function:
Hildebrand's approximation for smooth numbers and de Bruijn's logarithmic
asymptotic for the continuous function. At this cutoff even a factor-two
arithmetic approximation suffices. The proof below computes the limiting
exponent, including its constant, and converts the strict prime threshold
to Mathlib's natural-ceiling convention.

References: T. Tao, A result of Bui–Pratt–Zaharescu, and Erdős problem 437
(2024). The integral characterization also appears in Formal Conjectures'
statement of Erdős 1184.
-/

namespace OMA.R_Erdos437_erdos_437_variants_tao_R1_H3_R1

open Filter Real
open scoped Topology

/-- Hildebrand's estimate, restricted to the required curve and coarse relative bounds. -/
def H1 : Prop :=
  ∃ ρ : ℝ → ℝ,
    (ContinuousOn ρ (Set.Ici 0) ∧ (∀ u ∈ Set.Icc (0 : ℝ) 1, ρ u = 1) ∧
      ∀ u : ℝ, 1 ≤ u → u * ρ u = ∫ z in (u - 1)..u, ρ z) ∧
    ∀ᶠ x : ℕ in atTop,
      let b := log (x : ℝ)
      let Y := exp ((√(2 : ℝ))⁻¹ * √(b * log b))
      let u := √(2 * b / log b)
      let count := ((Finset.Icc 1 x).filter
        (fun n => ∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) < Y)).card
      (x : ℝ) * ρ u / 2 ≤ count ∧ (count : ℝ) ≤ 2 * ((x : ℝ) * ρ u)

/-- Logarithmic decay of the positive solution of the Dickman integral equation. -/
def H2 : Prop :=
  ∀ ρ : ℝ → ℝ,
    (ContinuousOn ρ (Set.Ici 0) ∧ (∀ u ∈ Set.Icc (0 : ℝ) 1, ρ u = 1) ∧
      ∀ u : ℝ, 1 ≤ u → u * ρ u = ∫ z in (u - 1)..u, ρ z) →
    (∀ᶠ u : ℝ in atTop, 0 < ρ u) ∧
      Tendsto (fun u => log (ρ u) / (u * log u)) atTop (𝓝 (-1 : ℝ))

lemma strict_cutoff (x : ℕ) (Y : ℝ) :
    (Finset.Icc 1 x).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) < Y) =
      x.smoothNumbersUpTo ⌈Y⌉₊ := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_smoothNumbersUpTo,
    Nat.mem_smoothNumbers_iff_primeFactors_subset]
  constructor
  · rintro ⟨⟨hn, hx⟩, h⟩
    exact ⟨hx, by omega, fun p hp =>
      Nat.mem_primesBelow.mpr ⟨Nat.lt_ceil.mpr (h p hp), Nat.prime_of_mem_primeFactors hp⟩⟩
  · rintro ⟨hx, hn, h⟩
    exact ⟨⟨by omega, hx⟩, fun p hp => Nat.lt_ceil.mp (Nat.mem_primesBelow.mp (h hp)).1⟩

lemma cutoff_identity {b : ℝ} (hb : 1 < b) :
    let a := log b
    let t := √(b * a)
    let u := √(2 * b / a)
    u * log u / t = √2 / 2 * (log 2 / a + 1 - log a / a) := by
  dsimp only
  have ha : 0 < log b := log_pos hb
  have bpos : 0 < b := lt_trans zero_lt_one hb
  have ht : 0 < √(b * log b) := sqrt_pos.mpr (mul_pos bpos ha)
  have hur : 0 < 2 * b / log b := by positivity
  have e : √(2 * b / log b) * log b = √2 * √(b * log b) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, sq_sqrt hur.le, sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      sq_sqrt (mul_nonneg bpos.le ha.le)]
    field_simp
  rw [log_sqrt hur.le, log_div (by positivity) ha.ne', log_mul (by norm_num) bpos.ne']
  field_simp [ht.ne', ha.ne']
  linear_combination (log 2 + log b - log (log b)) * e

theorem main : H1 → H2 → OMA.R_Erdos437_erdos_437_variants_tao_R1.H3 := by
  rintro ⟨ρ, hρ, hcount⟩ hDecay δ hδ
  obtain ⟨hpos, hd⟩ := hDecay ρ hρ
  let b (x : ℕ) := log (x : ℝ)
  let a (x : ℕ) := log (b x)
  let t (x : ℕ) := √(b x * a x)
  let u (x : ℕ) := √(2 * b x / a x)
  let c := (√(2 : ℝ))⁻¹
  have hb : Tendsto b atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha : Tendsto a atTop atTop := tendsto_log_atTop.comp hb
  have ht : Tendsto t atTop atTop := tendsto_sqrt_atTop.comp (hb.atTop_mul_atTop₀ ha)
  have ratio : Tendsto (fun x => a x / b x) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hb, ?_⟩
    filter_upwards [hb.eventually_gt_atTop 0, ha.eventually_gt_atTop 0] with x h1 h2
    exact div_pos h2 h1
  have hu : Tendsto u atTop atTop := by
    apply tendsto_sqrt_atTop.comp
    have hba : Tendsto (fun x => b x / a x) atTop atTop := by
      simpa [Function.comp_def] using tendsto_inv_nhdsGT_zero.comp ratio
    simpa [Function.comp_def, mul_div_assoc] using hba.const_mul_atTop (by norm_num : (0:ℝ) < 2)
  have hc0 : Tendsto (fun x => log (2 : ℝ) / a x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop ha
  have hc1 : Tendsto (fun x => log (a x) / a x) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ha
  have cs : √(2 : ℝ) / 2 = c := by
    dsimp [c]
    field_simp
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hnorm : Tendsto (fun x => u x * log (u x) / t x) atTop (𝓝 c) := by
    have hh := (((hc0.add_const 1).sub hc1).const_mul (√(2 : ℝ) / 2))
    apply (show Tendsto (fun x => √(2 : ℝ) / 2 *
      (log 2 / a x + 1 - log (a x) / a x)) atTop (𝓝 c) by simpa [cs] using hh).congr'
    filter_upwards [hb.eventually_gt_atTop 1] with x hx
    exact (cutoff_identity hx).symm
  have limit : Tendsto (fun x => log (ρ (u x)) / t x) atTop (𝓝 (-c)) := by
    apply (show Tendsto (fun x => log (ρ (u x)) / (u x * log (u x)) *
      (u x * log (u x) / t x)) atTop (𝓝 (-c)) by simpa using (hd.comp hu).mul hnorm).congr'
    filter_upwards [hu.eventually_gt_atTop 1] with x hx
    field_simp [(log_pos hx).ne', (lt_trans zero_lt_one hx).ne']
  have hlog2 : Tendsto (fun x => log (2 : ℝ) / t x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
  have lower := (limit.sub hlog2).eventually_const_lt (show -(c + δ) < -c - 0 by linarith)
  have upper := (limit.add hlog2).eventually_lt_const (show -c + 0 < -(c - δ) by linarith)
  filter_upwards [hcount, hu.eventually hpos, ht.eventually_gt_atTop 0, lower, upper] with
    x hx hρx htpos hlo hhi
  let Y := exp (c * t x)
  change (x : ℝ) * ρ (u x) / 2 ≤ _ ∧ _ ≤ 2 * ((x : ℝ) * ρ (u x)) at hx
  rw [strict_cutoff] at hx
  change (x : ℝ) * exp (-(c + δ) * t x) ≤ (x.smoothNumbersUpTo ⌈Y⌉₊).card ∧
    ((x.smoothNumbersUpTo ⌈Y⌉₊).card : ℝ) ≤ x * exp (-(c - δ) * t x)
  have hlow : -(c + δ) * t x ≤ log (ρ (u x)) - log 2 := by
    apply (le_div_iff₀ htpos).mp
    simpa [sub_div] using hlo.le
  have hhigh : log (ρ (u x)) + log 2 ≤ -(c - δ) * t x := by
    apply (div_le_iff₀ htpos).mp
    simpa [add_div] using hhi.le
  have elo := exp_le_exp.mpr hlow
  have ehi := exp_le_exp.mpr hhigh
  rw [exp_sub, exp_log hρx, exp_log (by norm_num : (0:ℝ) < 2)] at elo
  rw [exp_add, exp_log hρx, exp_log (by norm_num : (0:ℝ) < 2)] at ehi
  constructor
  · exact le_trans (by simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left elo (Nat.cast_nonneg x)) hx.1
  · exact le_trans hx.2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left ehi (Nat.cast_nonneg x))

end OMA.R_Erdos437_erdos_437_variants_tao_R1_H3_R1
