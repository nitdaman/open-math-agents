import FormalConjectures.Wikipedia.EllipticCurveRank

/-! # Counting reduced coefficient pairs and removing the singular ones -/
-- Credit: @steveDOTdigital
namespace OMA.R_EllipticCurveRank_RatEllipticCurve_card_heightLE_div_pow_five_div_six_tensto_R1
open EllipticCurveRank EllipticCurveRank.RatEllipticCurve Filter Set
open scoped Topology

-- The lattice-point sieve for the simultaneous fourth- and sixth-power exclusions.
def H1 : Prop := Tendsto (fun H : ℕ =>
    (({z : ℤ × ℤ | max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)}.ncard : ℝ) / (H : ℝ)^(5/6 : ℝ)))
    atTop (𝓝 (2^(4/3 : ℝ)*3^(-3/2 : ℝ)/(riemannZeta 10).re))

-- The zero-discriminant locus is negligible on the volume scale.
def H2 : Prop := Tendsto (fun H : ℕ =>
    (({z : ℤ × ℤ | (max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)) ∧
      4*z.1^3+27*z.2^2 = 0}.ncard : ℝ) / (H : ℝ)^(5/6 : ℝ))) atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @EllipticCurveRank.RatEllipticCurve.card_heightLE_div_pow_five_div_six_tensto := by
  classical
  intro sieve negligible
  let R (H : ℕ) := {z : ℤ × ℤ | max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)}
  let T (H : ℕ) := {z : ℤ × ℤ | z ∈ R H ∧ 4*z.1^3+27*z.2^2 = 0}
  have hfin (H : ℕ) : (R H).Finite := by
    apply ((Set.finite_Icc (-(H : ℤ)) H).prod (Set.finite_Icc (-(H : ℤ)) H)).subset
    rintro ⟨a,b⟩ h
    obtain ⟨hh,_⟩ := h
    obtain ⟨ha,hb⟩ := max_le_iff.mp hh
    change 4*a.natAbs^3 ≤ H at ha
    change 27*b.natAbs^2 ≤ H at hb
    have ha' : a.natAbs ≤ H := by have := Nat.le_self_pow (by decide : 3 ≠ 0) a.natAbs; omega
    have hb' : b.natAbs ≤ H := by have := Nat.le_self_pow (by decide : 2 ≠ 0) b.natAbs; omega
    change (-(H : ℤ) ≤ a ∧ a ≤ H) ∧ (-(H : ℤ) ≤ b ∧ b ≤ H)
    omega
  have hcard (H : ℕ) : (heightLE H).ncard = (R H \ T H).ncard := by
    refine Set.ncard_congr' {toFun := fun E => ?_, invFun := fun z => ?_, left_inv := ?_, right_inv := ?_}
    · refine ⟨(E.val.A,E.val.B),⟨E.property,E.val.reduced⟩,?_⟩
      exact fun h => E.val.Δ_ne_zero h.2
    · obtain ⟨⟨a,b⟩,hz⟩ := z
      exact ⟨⟨a,b,hz.1.2,fun e => hz.2 ⟨hz.1,e⟩⟩,hz.1.1⟩
    · rintro ⟨⟨a,b,hr,hn⟩,hh⟩; rfl
    · rintro ⟨⟨a,b⟩,h⟩; rfl
  have hl := (show Tendsto (fun H : ℕ => ((R H).ncard : ℝ)/(H : ℝ)^(5/6 : ℝ)) _ _ from sieve).sub
    (show Tendsto (fun H : ℕ => ((T H).ncard : ℝ)/(H : ℝ)^(5/6 : ℝ)) _ _ from negligible)
  rw [sub_zero] at hl
  apply hl.congr'
  filter_upwards with H
  rw [hcard, ← sub_div]
  have h := Set.ncard_sdiff_add_ncard_of_subset (show T H ⊆ R H from fun _ h => h.1) (hfin H)
  have eqr : (((R H \ T H).ncard : ℕ) : ℝ) + (T H).ncard = (R H).ncard := by exact_mod_cast h
  congr 1
  linarith

end OMA.R_EllipticCurveRank_RatEllipticCurve_card_heightLE_div_pow_five_div_six_tensto_R1
