import OMAReductions.R_EllipticCurveRank_RatEllipticCurve_card_heightLE_div_pow_five_div_six_tensto_R1

/-! # A square-root bound on singular Weierstrass pairs -/
-- Credit: @steveDOTdigital

open Filter Set
open scoped Topology
namespace OMA.SingularCurves
theorem negligible : OMA.R_EllipticCurveRank_RatEllipticCurve_card_heightLE_div_pow_five_div_six_tensto_R1.H2 := by
  classical
  let S (H : ℕ) := {z : ℤ × ℤ | (max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)) ∧
      4*z.1^3+27*z.2^2 = 0}
  have count (H : ℕ) : (S H).ncard ≤ 2*H.sqrt+1 := by
    let J := Finset.Icc (-(H.sqrt : ℤ)) (H.sqrt : ℤ)
    have bound : (S H).ncard ≤ (J : Set ℤ).ncard := by
      apply Set.ncard_le_ncard_of_injOn Prod.snd
      · rintro ⟨a,b⟩ hh
        have h := (max_le_iff.mp hh.1.1).2
        change 27*b.natAbs^2 ≤ H at h
        have hs : b.natAbs ≤ H.sqrt := Nat.le_sqrt'.mpr (by omega)
        change b ∈ Finset.Icc _ _
        rw [Finset.mem_Icc]; omega
      · rintro ⟨a,b⟩ hab ⟨c,e⟩ hce eq
        change b = e at eq; subst e
        have h₁ : 4*a^3+27*b^2=0 := hab.2
        have h₂ : 4*c^3+27*b^2=0 := hce.2
        have h₃ : a^3=c^3 := by linarith
        obtain rfl := (show Odd 3 by decide).pow_injective h₃
        rfl
    rw [Set.ncard_coe_finset,Int.card_Icc] at bound
    omega
  change Tendsto (fun H : ℕ => ((S H).ncard : ℝ) / (H : ℝ)^(5/6 : ℝ)) atTop (𝓝 0)
  have hlim : Tendsto (fun H : ℕ => (3 : ℝ)*(H : ℝ)^(-(1/3 : ℝ))) atTop (𝓝 0) := by
    simpa using (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/3)).comp
      tendsto_natCast_atTop_atTop).const_mul (3 : ℝ))
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => by positivity) _ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with H hH
  have hx : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hx' : (0 : ℝ) < H := by linarith
  have hs := Real.nat_sqrt_le_real_sqrt (a := H)
  have hsq : (1 : ℝ) ≤ Real.sqrt H := by simpa using Real.sqrt_le_sqrt hx
  have hcc : ((S H).ncard : ℝ) ≤ 2*(H.sqrt : ℝ)+1 := by exact_mod_cast count H
  calc
    _ ≤ 3*Real.sqrt H / (H : ℝ)^(5/6 : ℝ) := by gcongr; linarith
    _ = _ := by
      rw [Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hx']
      norm_num
end OMA.SingularCurves

theorem OMA.solution : OMA.R_EllipticCurveRank_RatEllipticCurve_card_heightLE_div_pow_five_div_six_tensto_R1.H2 := OMA.SingularCurves.negligible
