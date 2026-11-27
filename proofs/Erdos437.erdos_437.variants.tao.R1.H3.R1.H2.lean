import OMAReductions.R_Erdos437_erdos_437_variants_tao_R1_H3_R1
import Mathlib

/-! Logarithmic decay of the Dickman function via two exponential comparison functions. Formalization by @Halldon. -/

namespace DickmanDecay

open Filter Real MeasureTheory Set
open scoped Topology

lemma box_integrable {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {v : ℝ} (hv : 1 ≤ v) :
    IntervalIntegrable f volume (v - 1) v :=
  ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    (hf.mono fun z hz => show 0 ≤ z by linarith [hz.1])

-- A positive maximum above the barrier cannot be maintained by averaging over a
-- unit interval and dividing by v > 1.
lemma compare {f g : ℝ → ℝ} {A X : ℝ} (hf : ContinuousOn f (Ici 0))
    (hg : ContinuousOn g (Ici 0)) (hA : 1 ≤ A) (hX : 0 ≤ X)
    (initial : ∀ z ∈ Icc 0 A, f z ≤ g z)
    (step : ∀ v, A < v → v ≤ X →
      v * (f v - g v) ≤ (∫ t in (v - 1)..v, f t) - ∫ t in (v - 1)..v, g t) :
    f X ≤ g X := by
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hX)
    (show ContinuousOn (f - g) (Icc 0 X) from (hf.sub hg).mono fun z hz => hz.1)
  by_contra! hXbad
  have hpos : 0 < f v - g v := (sub_pos.mpr hXbad).trans_le
    (isMaxOn_iff.mp hmax X ⟨hX, le_rfl⟩)
  have hAv : A < v := lt_of_not_ge fun h => (not_le_of_gt hpos) (sub_nonpos.mpr (initial v ⟨hv.1, h⟩))
  have hv1 : 1 ≤ v := le_trans hA hAv.le
  have hstep := step v hAv hv.2
  rw [← intervalIntegral.integral_sub (box_integrable hf hv1) (box_integrable hg hv1)] at hstep
  have hbound := intervalIntegral.integral_mono_on (by linarith : v - 1 ≤ v)
    (box_integrable (hf.sub hg) hv1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f v - g v) volume (v-1) v)
    (fun t ht => isMaxOn_iff.mp hmax t ⟨by linarith [ht.1], ht.2.trans hv.2⟩)
  have hval : v * (f v - g v) ≤ f v - g v := by simpa using hstep.trans hbound
  nlinarith [mul_pos (by linarith : 0 < v - 1) hpos]

lemma exp_integral (k v : ℝ) (hk : 0 < k) :
    (∫ z in (v-1)..v, exp (-k*z)) = ((exp k - 1)/k) * exp (-k*v) := by
  rw [intervalIntegral.integral_comp_mul_left exp (neg_ne_zero.mpr hk.ne'), integral_exp]
  rw [show -k*(v-1) = -k*v+k by ring, exp_add]
  simp only [smul_eq_mul]
  field_simp
  ring

lemma below_one {ρ : ℝ → ℝ} (hc : ContinuousOn ρ (Ici 0))
    (hi : ∀ u ∈ Icc 0 1, ρ u = 1)
    (he : ∀ v, 1 ≤ v → v * ρ v = ∫ z in (v-1)..v, ρ z)
    {X : ℝ} (hX : 0 ≤ X) : ρ X ≤ 1 := by
  apply compare (g := fun _ => 1) hc continuousOn_const (A := 1) le_rfl hX
    (fun z hz => (hi z hz).le)
  intro v hv hvX
  rw [← he v hv.le]
  simp
  nlinarith

lemma quantitative {ρ : ℝ → ℝ} (hc : ContinuousOn ρ (Ici 0))
    (hi : ∀ u ∈ Icc 0 1, ρ u = 1)
    (he : ∀ v, 1 ≤ v → v * ρ v = ∫ z in (v-1)..v, ρ z)
    {X : ℝ} (hX : 1 ≤ X) (hL : 4 ≤ log X) :
    0 < ρ X ∧
      -(1 + 2 * (log (log X) / log X)) ≤ log (ρ X) / (X * log X) ∧
      log (ρ X) / (X * log X) ≤ -1 + 1 / log X := by
  let L := log X
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hLp : 0 < L := by dsimp [L]; linarith
  have hLL : 0 ≤ log L := log_nonneg (by dsimp [L]; linarith)
  let k := L + 2 * log L
  have hkp : 0 < k := by dsimp [k]; positivity
  have ek : exp k = X * L ^ 2 := by
    rw [show k = log X + (log L + log L) by dsimp [k,L]; ring, exp_add, exp_add,
      exp_log hXp, exp_log hLp, pow_two]
  have kbound : X ≤ (exp k-1)/k := by
    rw [le_div_iff₀ hkp, ek]
    have lk : k ≤ 3 * L := by dsimp [k]; linarith [log_le_sub_one_of_pos hLp]
    have l4 : 4 ≤ L := hL
    have lbig : 3 * L ≤ L ^ 2 - 1 := by nlinarith [mul_self_nonneg (L-3)]
    calc
      X*k ≤ X*(L^2-1) := mul_le_mul_of_nonneg_left (lk.trans lbig) hXp.le
      _ ≤ X*L^2-1 := by nlinarith
  have lo : exp (-k*X) ≤ ρ X := by
    apply compare (f := fun t => exp (-k*t)) (by fun_prop) hc (A := 1) le_rfl hXp.le
    · intro z hz
      rw [hi z hz]
      exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkp.le) hz.1)
    · intro v hv hvX
      rw [exp_integral k v hkp, ← he v hv.le]
      nlinarith [mul_le_mul_of_nonneg_right (hvX.trans kbound) (exp_pos (-k*v)).le]
  have hρ := (exp_pos _).trans_le lo
  let A := X/L
  have hA : 1 ≤ A := (le_div_iff₀ hLp).mpr (by
    dsimp [L]
    linarith [log_le_sub_one_of_pos hXp])
  let C := exp (L * A)
  have up : ρ X ≤ C * exp (-L*X) := by
    apply compare hc (g := fun t => C * exp (-L*t)) (by fun_prop) hA hXp.le
    · intro z hz
      apply (below_one hc hi he hz.1).trans
      change 1 ≤ exp (L*A) * exp (-L*z)
      rw [← exp_add, one_le_exp_iff]
      nlinarith [mul_nonneg hLp.le (sub_nonneg.mpr hz.2)]
    · intro v hv hvX
      rw [intervalIntegral.integral_const_mul, exp_integral L v hLp, exp_log hXp, ← he v (hA.trans hv.le)]
      have small : (X-1)/L ≤ v := (div_le_div_of_nonneg_right (by linarith) hLp.le).trans hv.le
      have hC : 0 ≤ C := (exp_pos _).le
      nlinarith only [mul_le_mul_of_nonneg_right small (mul_nonneg hC (exp_pos (-L*v)).le)]
  refine ⟨hρ, ?_, ?_⟩
  · apply (le_div_iff₀ (mul_pos hXp hLp)).mpr
    have hlo := log_le_log (exp_pos _) lo
    rw [log_exp] at hlo
    change -(1 + 2 * (log L / L)) * (X * L) ≤ _
    calc
      _ = -k * X := by dsimp [k]; field_simp
      _ ≤ _ := hlo
  · apply (div_le_iff₀ (mul_pos hXp hLp)).mpr
    have hup := log_le_log hρ up
    change log (ρ X) ≤ log (exp (L*A) * exp (-L*X)) at hup
    rw [← exp_add, log_exp] at hup
    calc
      log (ρ X) ≤ L*A + -L*X := hup
      _ = (-1 + 1/L)*(X*L) := by dsimp [A]; field_simp; ring

theorem analytic_child (ρ : ℝ → ℝ)
    (data : ContinuousOn ρ (Ici 0) ∧ (∀ u ∈ Icc (0 : ℝ) 1, ρ u = 1) ∧
      ∀ u : ℝ, 1 ≤ u → u * ρ u = ∫ z in (u - 1)..u, ρ z) :
    (∀ᶠ u : ℝ in atTop, 0 < ρ u) ∧
      Tendsto (fun u => log (ρ u) / (u * log u)) atTop (𝓝 (-1 : ℝ)) := by
  have h := (eventually_ge_atTop (1 : ℝ)).and (tendsto_log_atTop.eventually_ge_atTop 4)
  have hb := h.mono fun u hu => quantitative data.1 data.2.1 data.2.2 hu.1 hu.2
  refine ⟨hb.mono fun _ hu => hu.1, ?_⟩
  have hL : Tendsto (fun u : ℝ => log (log u) / log u) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_atTop
  have hI : Tendsto (fun u : ℝ => 1 / log u) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_log_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _ _ (hb.mono fun _ hu => hu.2.1)
    (hb.mono fun _ hu => hu.2.2)
  · simpa using ((hL.const_mul 2).const_add 1).neg
  · simpa using hI.const_add (-1)

end DickmanDecay

theorem OMA.solution : OMA.R_Erdos437_erdos_437_variants_tao_R1_H3_R1.H2 := DickmanDecay.analytic_child
