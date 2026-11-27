import FormalConjectures.Wikipedia.ChowlaLiouvilleConjecture

/-!
Proof of the one-point Liouville average $\frac{1}{N} \sum_{n=1}^N \lambda(n) \to 0$
(equivalent to the Prime Number Theorem), via the Dirichlet series identity
$L(\lambda, s) = \zeta(2s)/\zeta(s)$, analytic continuation across $\operatorname{Re}(s) \ge 1$
using `riemannZeta_ne_zero_of_one_le_re`, a rectangular Newman Tauberian argument, and
Kronecker's lemma.
-/

-- Problem: One-Point Liouville Average
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ChowlaLiouvilleConjecture.lean:69 (declaration ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.one_point)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped BigOperators Topology ComplexOrder Interval
open Complex Filter MeasureTheory Set

namespace ChowlaOnePointProof

/-! ### Section 1: Arithmetic identity `λ * ζ = 1_sq` and Dirichlet series `L(λ, s) = ζ(2s)/ζ(s)` -/

private lemma coprime_isSquare_mul_iff {m n : ℕ} (hc : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  constructor
  · rintro ⟨k, hk⟩
    have hk0 : k ≠ 0 := by
      intro h
      rw [h, mul_zero] at hk
      exact mul_ne_zero hm hn hk
    set a := m.gcd k
    set b := n.gcd k
    have ha_pos : 0 < a := Nat.gcd_pos_of_pos_left k (Nat.pos_of_ne_zero hm)
    have ha_dvd_m : a ∣ m := Nat.gcd_dvd_left m k
    have ha_dvd_k : a ∣ k := Nat.gcd_dvd_right m k
    have hb_dvd_n : b ∣ n := Nat.gcd_dvd_left n k
    have hb_dvd_k : b ∣ k := Nat.gcd_dvd_right n k
    have ha_cop_b : a.Coprime b := (hc.coprime_dvd_left ha_dvd_m).coprime_dvd_right hb_dvd_n
    have hab_dvd_k : a * b ∣ k := ha_cop_b.mul_dvd_of_dvd_of_dvd ha_dvd_k hb_dvd_k
    have hk_dvd_ab : k ∣ a * b := by
      have hcop' : (m / a).Coprime (k / a) := Nat.coprime_div_gcd_div_gcd ha_pos
      have hm_eq : m = a * (m / a) := (Nat.mul_div_cancel' ha_dvd_m).symm
      have hk_eq : k = a * (k / a) := (Nat.mul_div_cancel' ha_dvd_k).symm
      have hdvd1 : k ∣ m * n := ⟨k, hk⟩
      rw [hk_eq, hm_eq, mul_assoc] at hdvd1
      have hdvd2 : k / a ∣ m / a * n := (mul_dvd_mul_iff_left ha_pos.ne').mp hdvd1
      have hdvd_n : k / a ∣ n := hcop'.symm.dvd_of_dvd_mul_left hdvd2
      have hdvd_k : k / a ∣ k := ⟨a, by rw [mul_comm]; exact hk_eq⟩
      have hdvd_b : k / a ∣ b := Nat.dvd_gcd hdvd_n hdvd_k
      rw [hk_eq]
      exact mul_dvd_mul_left a hdvd_b
    have hk_eq_ab : k = a * b := Nat.dvd_antisymm hk_dvd_ab hab_dvd_k
    have hmn_eq : m * n = (a * a) * (b * b) := by
      rw [hk, hk_eq_ab]; ring
    have haa_cop_n : (a * a).Coprime n :=
      (hc.coprime_dvd_left ha_dvd_m).mul_left (hc.coprime_dvd_left ha_dvd_m)
    have hm_cop_bb : m.Coprime (b * b) :=
      (hc.coprime_dvd_right hb_dvd_n).mul_right (hc.coprime_dvd_right hb_dvd_n)
    have hm_eq_aa : m = a * a := Nat.dvd_antisymm
      (hm_cop_bb.dvd_of_dvd_mul_right ⟨n, hmn_eq.symm⟩)
      (haa_cop_n.dvd_of_dvd_mul_right ⟨b * b, hmn_eq⟩)
    have hn_eq_bb : n = b * b := by
      rw [hm_eq_aa] at hmn_eq
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hm_eq_aa ▸ hm)) hmn_eq
    exact ⟨⟨a, hm_eq_aa⟩, ⟨b, hn_eq_bb⟩⟩
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    exact ⟨a * b, by ring⟩

private def sqArith : ArithmeticFunction ℤ where
  toFun n := if n ≠ 0 ∧ IsSquare n then 1 else 0
  map_zero' := by simp

private lemma isMultiplicative_sqArith : sqArith.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [sqArith]
  · intro m n hc
    by_cases hm : m = 0
    · simp [hm, sqArith]
    by_cases hn : n = 0
    · simp [hn, sqArith]
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    simp only [sqArith, ArithmeticFunction.coe_mk, hm, hn, hmn, ne_eq, not_false_eq_true,
      true_and, coprime_isSquare_mul_iff hc hm hn]
    by_cases h1 : IsSquare m <;> by_cases h2 : IsSquare n <;> simp [h1, h2]

private lemma sum_neg_one_pow (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j) = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have h1 : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using hk
      rw [if_pos hk, if_neg h1, pow_succ, hk.neg_one_pow]
      ring
    · have h1 : Even (k + 1) := by rwa [Nat.even_add_one, Nat.not_even_iff_odd]
      rw [if_neg (Nat.not_even_iff_odd.mpr hk), if_pos h1, pow_succ, hk.neg_one_pow]
      ring

private lemma isSquare_prime_pow_iff {p k : ℕ} (hp : p.Prime) : IsSquare (p ^ k) ↔ Even k := by
  constructor
  · rintro ⟨m, hm⟩
    have hm0 : m ≠ 0 := by
      intro h; rw [h, mul_zero] at hm; exact pow_ne_zero k hp.ne_zero hm
    have hcf : ArithmeticFunction.cardFactors (p ^ k) =
        ArithmeticFunction.cardFactors (m * m) := congrArg _ hm
    rw [ArithmeticFunction.cardFactors_apply_prime_pow hp,
      ArithmeticFunction.cardFactors_mul hm0 hm0] at hcf
    exact ⟨ArithmeticFunction.cardFactors m, hcf⟩
  · rintro ⟨r, rfl⟩
    exact ⟨p ^ r, by rw [pow_add]⟩

private lemma liouville_mul_zeta_eq_sqArith :
    ArithmeticFunction.liouville * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) = sqArith := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (ArithmeticFunction.isMultiplicative_liouville.mul ArithmeticFunction.isMultiplicative_zeta.natCast)
    _ isMultiplicative_sqArith]
  intro p k hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y =>
    ArithmeticFunction.liouville x * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) y))]
  have hsum : (∑ d ∈ (p ^ k).divisors,
      ArithmeticFunction.liouville d * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) (p ^ k / d)) =
      ∑ d ∈ (p ^ k).divisors, ArithmeticFunction.liouville d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hne : p ^ k / d ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨(Nat.pos_of_mem_divisors hd).ne', Nat.le_of_dvd (pow_pos hp.pos k) (Nat.dvd_of_mem_divisors hd)⟩
    simp [ArithmeticFunction.zeta_apply, hne]
  rw [hsum, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : (∑ j ∈ Finset.range (k + 1), ArithmeticFunction.liouville (p ^ j)) =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ArithmeticFunction.liouville_apply (pow_ne_zero j hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp]
  rw [hterm, sum_neg_one_pow]
  simp [sqArith, hp.ne_zero, isSquare_prime_pow_iff hp]

private def lamC : ℕ → ℂ := fun n => (ArithmeticFunction.liouville n : ℂ)

private lemma norm_lamC_le_one (n : ℕ) : ‖lamC n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [lamC, hn]
  · simp [lamC, ArithmeticFunction.liouville_apply hn]

private lemma LSeriesSummable_lamC {s : ℂ} (hs : 1 < s.re) : LSeriesSummable lamC s := by
  have h1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  refine Summable.of_norm_bounded h1.norm fun n => ?_
  by_cases hn : n = 0
  · simp [LSeries.term, hn]
  · simp only [LSeries.term_of_ne_zero hn, norm_div, Pi.one_apply, norm_one]
    exact div_le_div_of_nonneg_right (norm_lamC_le_one n) (norm_nonneg _)

private lemma LSeries_sqArith_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (sqArith n : ℂ)) s = riemannZeta (2 * s) := by
  have h2s : 1 < (2 * s).re := by simp; linarith
  rw [← LSeries_one_eq_riemannZeta h2s]
  unfold LSeries
  have hterm : ∀ m : ℕ, LSeries.term (fun n => (sqArith n : ℂ)) s (m ^ 2) =
      LSeries.term 1 (2 * s) m := by
    intro m
    by_cases hm : m = 0
    · simp [hm, LSeries.term]
    · have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
      have hsq : IsSquare (m ^ 2) := ⟨m, sq m⟩
      simp only [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hm2,
        Pi.one_apply, sqArith, ArithmeticFunction.coe_mk, hm2, hsq, ne_eq,
        not_false_eq_true, and_self, ↓reduceIte, Int.cast_one]
      congr 1
      rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul m 2 s]
      norm_num
  have htsum : (∑' m : ℕ, LSeries.term (fun n => (sqArith n : ℂ)) s (m ^ 2)) =
      ∑' n : ℕ, LSeries.term (fun n => (sqArith n : ℂ)) s n := by
    refine Function.Injective.tsum_eq (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) fun n hn => ?_
    by_contra hnot
    apply hn
    by_cases hn0 : n = 0
    · simp [LSeries.term, hn0]
    · have hnsq : ¬ IsSquare n := by
        rintro ⟨m, rfl⟩
        exact hnot ⟨m, by ring⟩
      simp [sqArith, hn0, hnsq]
  rw [← htsum]
  exact tsum_congr hterm

private lemma LSeries_lamC_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries lamC s = riemannZeta (2 * s) / riemannZeta s := by
  have hconv := LSeries_convolution' (LSeriesSummable_lamC hs) (LSeriesSummable_one_iff.mpr hs)
  have hfun : (LSeries.convolution lamC (1 : ℕ → ℂ)) = fun n => (sqArith n : ℂ) := by
    ext n
    rw [LSeries.convolution_def]
    have h := congrArg (fun f : ArithmeticFunction ℤ => (f n : ℂ)) liouville_mul_zeta_eq_sqArith
    rw [ArithmeticFunction.mul_apply, Int.cast_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 : p.2 ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hp).2 |> fun hn =>
      right_ne_zero_of_mul (by rwa [(Nat.mem_divisorsAntidiagonal.mp hp).1])
    simp [lamC, ArithmeticFunction.zeta_apply, hp2]
  rw [hfun, LSeries_sqArith_eq_riemannZeta hs, LSeries_one_eq_riemannZeta hs] at hconv
  exact eq_div_of_mul_eq (riemannZeta_ne_zero_of_one_lt_re hs) hconv.symm

/-! ### Section 2: Analytic continuation of `G(z) = ζ(2(1+z))/ζ(1+z)` past `Re(z) ≥ 0` -/

private noncomputable def zetaMulSubOne (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s

private lemma differentiable_zetaMulSubOne : Differentiable ℂ zetaMulSubOne := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨?_, ?_⟩
  · intro s hs
    have hs1 : s ≠ 1 := by simpa using hs
    have heq : zetaMulSubOne =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with w hw
      simp [zetaMulSubOne, hw]
    exact (((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)).congr_of_eventuallyEq
      heq).differentiableWithinAt
  · have htend : Tendsto zetaMulSubOne (𝓝[≠] 1) (𝓝 1) := by
      refine riemannZeta_residue_one.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw1 : w ≠ 1 := hw
      simp [zetaMulSubOne, hw1]
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨ρ, hρ, hball⟩ := (Metric.tendsto_nhdsWithin_nhds.mp htend) ε hε
    refine ⟨ρ, hρ, fun w hw => ?_⟩
    have hval : zetaMulSubOne 1 = 1 := by simp [zetaMulSubOne]
    rw [hval]
    by_cases hw1 : w = 1
    · rw [hw1, hval, dist_self]; exact hε
    · exact hball hw1 hw

private noncomputable def G (z : ℂ) : ℂ :=
  (z * riemannZeta (2 * (1 + z))) / zetaMulSubOne (1 + z)

private lemma G_zero : G 0 = 0 := by
  simp [G, zetaMulSubOne]

private lemma G_eq_LSeries {z : ℂ} (hz : 0 < z.re) : G z = LSeries lamC (1 + z) := by
  have hre : 1 < (1 + z).re := by simp; linarith
  have hz0 : z ≠ 0 := by intro h; rw [h, zero_re] at hz; linarith
  have h1z : 1 + z ≠ 1 := by intro h; exact hz0 (by linear_combination h)
  rw [LSeries_lamC_eq hre, G, zetaMulSubOne, if_neg h1z]
  have hsub : 1 + z - 1 = z := by ring
  rw [hsub, mul_div_mul_left _ _ hz0]

private def Udom : Set ℂ :=
  {z | -(1 / 2 : ℝ) < z.re ∧ zetaMulSubOne (1 + z) ≠ 0}

private lemma isOpen_Udom : IsOpen Udom := by
  refine IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re) ?_
  exact isOpen_ne.preimage (differentiable_zetaMulSubOne.continuous.comp (continuous_const.add continuous_id))

private lemma halfPlane_subset_Udom : {z : ℂ | 0 ≤ z.re} ⊆ Udom := by
  intro z hz
  change 0 ≤ z.re at hz
  refine ⟨by linarith, ?_⟩
  by_cases hz0 : z = 0
  · simp [hz0, zetaMulSubOne]
  · have h1z : 1 + z ≠ 1 := by intro h; exact hz0 (by linear_combination h)
    rw [zetaMulSubOne, if_neg h1z, show 1 + z - 1 = z by ring]
    exact mul_ne_zero hz0 (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))

private lemma differentiableOn_G_Udom : DifferentiableOn ℂ G Udom := by
  intro z hz
  have h2ne1 : 2 * (1 + z) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hz.1]
  have hnum : DifferentiableAt ℂ (fun w => w * riemannZeta (2 * (1 + w))) z :=
    differentiableAt_id.mul ((differentiableAt_riemannZeta h2ne1).comp z
      (differentiableAt_const 2 |>.mul (differentiableAt_const 1 |>.add differentiableAt_id)))
  have hden : DifferentiableAt ℂ (fun w => zetaMulSubOne (1 + w)) z :=
    differentiable_zetaMulSubOne.differentiableAt.comp z
      (differentiableAt_const 1 |>.add differentiableAt_id)
  exact (hnum.div hden hz.2).differentiableWithinAt

/-! ### Section 3: Explicit boundary integral of `1 / z` around `[−del, T] × [−T, T]` -/

private noncomputable def rectInt (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
    I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I))

private lemma rectInt_eq_zero_of_differentiableOn {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f ([[a, b]] ×ℂ [[c, d]])) :
    rectInt f a b c d = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (a + c * I) (b + d * I)
  simpa [rectInt, smul_eq_mul] using h (by simpa using hf)

private lemma horizontal_inv_integral (a b y₀ : ℝ) (hy : y₀ ≠ 0) :
    (∫ x : ℝ in a..b, ((x : ℂ) + y₀ * I)⁻¹) =
      (((Real.log (b ^ 2 + y₀ ^ 2) / 2 : ℝ) : ℂ) - ((Real.arctan (b / y₀) : ℝ) : ℂ) * I) -
      (((Real.log (a ^ 2 + y₀ ^ 2) / 2 : ℝ) : ℂ) - ((Real.arctan (a / y₀) : ℝ) : ℂ) * I) := by
  let F : ℝ → ℂ := fun x =>
    ((Real.log (x ^ 2 + y₀ ^ 2) / 2 : ℝ) : ℂ) - ((Real.arctan (x / y₀) : ℝ) : ℂ) * I
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (((x : ℂ) + y₀ * I)⁻¹) x := by
    intro x _
    have hpos : 0 < x ^ 2 + y₀ ^ 2 := by positivity
    have hlog : HasDerivAt (fun t : ℝ => Real.log (t ^ 2 + y₀ ^ 2) / 2)
        (x / (x ^ 2 + y₀ ^ 2)) x := by
      have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + y₀ ^ 2) (2 * x) x := by
        simpa using ((hasDerivAt_pow 2 x).add_const (y₀ ^ 2))
      have h2 : HasDerivAt (fun t : ℝ => Real.log (t ^ 2 + y₀ ^ 2) / 2)
          ((2 * x / (x ^ 2 + y₀ ^ 2)) / 2) x :=
        (h1.log hpos.ne').div_const 2
      rwa [show (2 * x / (x ^ 2 + y₀ ^ 2)) / 2 = x / (x ^ 2 + y₀ ^ 2) by ring] at h2
    have harctan : HasDerivAt (fun t : ℝ => Real.arctan (t / y₀))
        (y₀ / (x ^ 2 + y₀ ^ 2)) x := by
      have h1 : HasDerivAt (fun t : ℝ => t / y₀) (1 / y₀) x := by
        simpa using (hasDerivAt_id x).div_const y₀
      have h2 := (Real.hasDerivAt_arctan (x / y₀)).comp x h1
      change HasDerivAt (fun t : ℝ => Real.arctan (t / y₀))
        (1 / (1 + (x / y₀) ^ 2) * (1 / y₀)) x at h2
      have hden : 1 + (x / y₀) ^ 2 ≠ 0 := by positivity
      have heq : 1 / (1 + (x / y₀) ^ 2) * (1 / y₀) = y₀ / (x ^ 2 + y₀ ^ 2) := by
        field_simp [hy, hpos.ne', hden]
        ring
      rwa [heq] at h2
    have hF : HasDerivAt F
        (((x / (x ^ 2 + y₀ ^ 2) : ℝ) : ℂ) - ((y₀ / (x ^ 2 + y₀ ^ 2) : ℝ) : ℂ) * I) x :=
      hlog.ofReal_comp.sub (harctan.ofReal_comp.mul_const I)
    convert hF using 1
    symm
    apply eq_inv_of_mul_eq_one_left
    apply Complex.ext
    · simp only [mul_re, sub_re, add_re, ofReal_re, mul_im, sub_im, add_im, ofReal_im,
        I_re, I_im, one_re, mul_zero, mul_one, sub_zero, add_zero, zero_add]
      field_simp [hpos.ne']
      ring
    · simp only [mul_im, sub_im, add_im, ofReal_im, mul_re, sub_re, add_re, ofReal_re,
        I_re, I_im, one_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
      ring
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + y₀ * I)⁻¹) (Set.uIcc a b) := by
    refine ContinuousOn.inv₀ (continuous_ofReal.add continuous_const).continuousOn fun x _ => ?_
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hy him
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

private lemma vertical_inv_integral (x₀ c d : ℝ) (hx : x₀ ≠ 0) :
    I * (∫ y : ℝ in c..d, ((x₀ : ℂ) + y * I)⁻¹) =
      (((Real.log (x₀ ^ 2 + d ^ 2) / 2 : ℝ) : ℂ) + ((Real.arctan (d / x₀) : ℝ) : ℂ) * I) -
      (((Real.log (x₀ ^ 2 + c ^ 2) / 2 : ℝ) : ℂ) + ((Real.arctan (c / x₀) : ℝ) : ℂ) * I) := by
  rw [← intervalIntegral.integral_const_mul]
  let F : ℝ → ℂ := fun y =>
    ((Real.log (x₀ ^ 2 + y ^ 2) / 2 : ℝ) : ℂ) + ((Real.arctan (y / x₀) : ℝ) : ℂ) * I
  have hderiv : ∀ y ∈ Set.uIcc c d, HasDerivAt F (I * ((x₀ : ℂ) + y * I)⁻¹) y := by
    intro y _
    have hpos : 0 < x₀ ^ 2 + y ^ 2 := by positivity
    have hlog : HasDerivAt (fun t : ℝ => Real.log (x₀ ^ 2 + t ^ 2) / 2)
        (y / (x₀ ^ 2 + y ^ 2)) y := by
      have h1 : HasDerivAt (fun t : ℝ => x₀ ^ 2 + t ^ 2) (2 * y) y := by
        simpa using (hasDerivAt_pow 2 y).const_add (x₀ ^ 2)
      have h2 : HasDerivAt (fun t : ℝ => Real.log (x₀ ^ 2 + t ^ 2) / 2)
          ((2 * y / (x₀ ^ 2 + y ^ 2)) / 2) y :=
        (h1.log hpos.ne').div_const 2
      rwa [show (2 * y / (x₀ ^ 2 + y ^ 2)) / 2 = y / (x₀ ^ 2 + y ^ 2) by ring] at h2
    have harctan : HasDerivAt (fun t : ℝ => Real.arctan (t / x₀))
        (x₀ / (x₀ ^ 2 + y ^ 2)) y := by
      have h1 : HasDerivAt (fun t : ℝ => t / x₀) (1 / x₀) y := by
        simpa using (hasDerivAt_id y).div_const x₀
      have h2 := (Real.hasDerivAt_arctan (y / x₀)).comp y h1
      change HasDerivAt (fun t : ℝ => Real.arctan (t / x₀))
        (1 / (1 + (y / x₀) ^ 2) * (1 / x₀)) y at h2
      have hden : 1 + (y / x₀) ^ 2 ≠ 0 := by positivity
      have heq : 1 / (1 + (y / x₀) ^ 2) * (1 / x₀) = x₀ / (x₀ ^ 2 + y ^ 2) := by
        field_simp [hx, hpos.ne', hden]
      rwa [heq] at h2
    have hF : HasDerivAt F
        (((y / (x₀ ^ 2 + y ^ 2) : ℝ) : ℂ) + ((x₀ / (x₀ ^ 2 + y ^ 2) : ℝ) : ℂ) * I) y :=
      hlog.ofReal_comp.add (harctan.ofReal_comp.mul_const I)
    convert hF using 1
    have hne : (x₀ : ℂ) + y * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      exact hx hre
    rw [mul_inv_eq_iff_eq_mul₀ hne]
    apply Complex.ext
    · simp only [mul_re, add_re, ofReal_re, mul_im, add_im, ofReal_im,
        I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
      ring
    · simp only [mul_im, add_im, ofReal_im, mul_re, add_re, ofReal_re,
        I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
      field_simp [hpos.ne']
      ring
  have hcont : ContinuousOn (fun y : ℝ => I * ((x₀ : ℂ) + y * I)⁻¹) (Set.uIcc c d) := by
    refine continuousOn_const.mul (ContinuousOn.inv₀
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn fun y _ => ?_)
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact hx hre
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

private lemma rectInt_inv (del T : ℝ) (hdel : 0 < del) (hT : 0 < T) :
    rectInt (fun z => z⁻¹) (-del) T (-T) T = 2 * Real.pi * I := by
  unfold rectInt
  rw [horizontal_inv_integral (-del) T (-T) (neg_ne_zero.mpr hT.ne'),
    horizontal_inv_integral (-del) T T hT.ne',
    vertical_inv_integral T (-T) T hT.ne',
    vertical_inv_integral (-del) (-T) T (neg_ne_zero.mpr hdel.ne')]
  have h1 : Real.arctan (T / T) = Real.pi / 4 := by
    rw [div_self hT.ne', Real.arctan_one]
  have h2 : Real.arctan ((-T) / T) = -(Real.pi / 4) := by
    rw [neg_div, div_self hT.ne', Real.arctan_neg, Real.arctan_one]
  have h3 : Real.arctan (T / (-T)) = -(Real.pi / 4) := by
    rw [div_neg, div_self hT.ne', Real.arctan_neg, Real.arctan_one]
  have h4 : Real.arctan ((-del) / (-T)) = Real.arctan (del / T) := by
    rw [neg_div_neg_eq]
  have h5 : Real.arctan ((-del) / T) = -Real.arctan (del / T) := by
    rw [neg_div, Real.arctan_neg]
  have h6 : Real.arctan (T / (-del)) = -Real.arctan (T / del) := by
    rw [div_neg, Real.arctan_neg]
  have h7 : Real.arctan ((-T) / (-del)) = Real.arctan (T / del) := by
    rw [neg_div_neg_eq]
  have hinv : Real.arctan (T / del) = Real.pi / 2 - Real.arctan (del / T) := by
    have hpos : 0 < del / T := div_pos hdel hT
    have heq : T / del = (del / T)⁻¹ := by rw [inv_div]
    rw [heq, Real.arctan_inv_of_pos hpos]
  have hsq1 : (-del) ^ 2 = del ^ 2 := neg_sq del
  have hsq2 : (-T) ^ 2 = T ^ 2 := neg_sq T
  rw [h1, h2, h3, h4, h5, h6, h7, hinv, hsq1, hsq2]
  push_cast
  ring

/-! ### Section 4: Cauchy integral formula for `F(z) * (1 / z + z / T^2)` on `[−del, T] × [−T, T]` -/

private noncomputable def K (T : ℝ) (z : ℂ) : ℂ :=
  z⁻¹ + z / (T : ℂ) ^ 2

private lemma cauchy_rect_kernel {F : ℂ → ℂ} {del T : ℝ} (hdel : 0 < del) (hT : 0 < T)
    (hF : DifferentiableOn ℂ F ([[-del, T]] ×ℂ [[-T, T]])) :
    rectInt (fun z => F z * K T z) (-del) T (-T) T = 2 * Real.pi * I * F 0 := by
  have hmem0 : ([[-del, T]] ×ℂ [[-T, T]]) ∈ 𝓝 (0 : ℂ) := by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    have hopen : IsOpen (Set.Ioo (-del) T ×ℂ Set.Ioo (-T) T) := isOpen_Ioo.reProdIm isOpen_Ioo
    refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
    · simp [Complex.mem_reProdIm, hdel, hT]
    · exact Set.inter_subset_inter (preimage_mono Ioo_subset_Icc_self)
        (preimage_mono Ioo_subset_Icc_self)
  have hd1 : DifferentiableOn ℂ (dslope F 0) ([[-del, T]] ×ℂ [[-T, T]]) :=
    (Complex.differentiableOn_dslope hmem0).mpr hF
  have hd3 : DifferentiableOn ℂ (fun z => F z * (z / (T : ℂ) ^ 2)) ([[-del, T]] ×ℂ [[-T, T]]) :=
    hF.mul (differentiableOn_id.div_const _)
  have h0_1 : rectInt (dslope F 0) (-del) T (-T) T = 0 :=
    rectInt_eq_zero_of_differentiableOn hd1
  have h0_3 : rectInt (fun z => F z * (z / (T : ℂ) ^ 2)) (-del) T (-T) T = 0 :=
    rectInt_eq_zero_of_differentiableOn hd3
  have hsplit : ∀ z : ℂ, z ≠ 0 →
      F z * K T z = dslope F 0 z + F 0 * z⁻¹ + F z * (z / (T : ℂ) ^ 2) := by
    intro z hz
    rw [dslope_of_ne _ hz, slope_def_field, sub_zero, K]
    field_simp [hz]
    ring
  have hEdgeInt : ∀ (g₁ g₂ g₃ : ℂ → ℂ) (a b : ℝ) (γ : ℝ → ℂ),
      (∀ t ∈ Set.uIcc a b, γ t ≠ 0) →
      ContinuousOn g₁ (γ '' Set.uIcc a b) →
      ContinuousOn g₂ (γ '' Set.uIcc a b) →
      ContinuousOn g₃ (γ '' Set.uIcc a b) →
      ContinuousOn γ (Set.uIcc a b) →
      (∀ t ∈ Set.uIcc a b, F (γ t) * K T (γ t) = g₁ (γ t) + g₂ (γ t) + g₃ (γ t)) →
      (∫ t in a..b, F (γ t) * K T (γ t)) =
        (∫ t in a..b, g₁ (γ t)) + (∫ t in a..b, g₂ (γ t)) + (∫ t in a..b, g₃ (γ t)) := by
    intro g₁ g₂ g₃ a b γ _ hc₁ hc₂ hc₃ hcγ heq
    have hi₁ : IntervalIntegrable (fun t => g₁ (γ t)) volume a b :=
      (hc₁.comp hcγ (Set.mapsTo_image γ _)).intervalIntegrable
    have hi₂ : IntervalIntegrable (fun t => g₂ (γ t)) volume a b :=
      (hc₂.comp hcγ (Set.mapsTo_image γ _)).intervalIntegrable
    have hi₃ : IntervalIntegrable (fun t => g₃ (γ t)) volume a b :=
      (hc₃.comp hcγ (Set.mapsTo_image γ _)).intervalIntegrable
    rw [intervalIntegral.integral_congr (fun t ht => heq t ht),
      intervalIntegral.integral_add (hi₁.add hi₂) hi₃,
      intervalIntegral.integral_add hi₁ hi₂]
  have hRectSub : ∀ (a b c d : ℝ), a ∈ Set.uIcc (-del) T → b ∈ Set.uIcc (-del) T →
      c ∈ Set.uIcc (-T) T → d ∈ Set.uIcc (-T) T → True := fun _ _ _ _ _ _ _ _ => trivial
  -- Decompose each of the 4 edges
  have hBot : (∫ x in (-del)..T, F (x + (-T : ℝ) * I) * K T (x + (-T : ℝ) * I)) =
      (∫ x in (-del)..T, dslope F 0 (x + (-T : ℝ) * I)) +
      F 0 * (∫ x in (-del)..T, ((x : ℂ) + (-T : ℝ) * I)⁻¹) +
      (∫ x in (-del)..T, F (x + (-T : ℝ) * I) * ((x + (-T : ℝ) * I) / (T : ℂ) ^ 2)) := by
    let γ : ℝ → ℂ := fun x => x + (-T : ℝ) * I
    have hγne : ∀ x ∈ Set.uIcc (-del) T, γ x ≠ 0 := fun x _ h => by
      have him := congrArg Complex.im h; simp [γ] at him; linarith
    have hγsub : γ '' Set.uIcc (-del) T ⊆ [[-del, T]] ×ℂ [[-T, T]] := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨by simpa [γ] using hx, by simp [γ, Set.left_mem_uIcc]⟩
    have hinv_cont : ContinuousOn (fun z : ℂ => F 0 * z⁻¹) (γ '' Set.uIcc (-del) T) :=
      continuousOn_const.mul (continuousOn_inv₀.mono (by rintro _ ⟨x, hx, rfl⟩; exact hγne x hx))
    rw [hEdgeInt (dslope F 0) (fun z => F 0 * z⁻¹) (fun z => F z * (z / (T : ℂ) ^ 2))
      (-del) T γ hγne (hd1.continuousOn.mono hγsub) hinv_cont (hd3.continuousOn.mono hγsub)
      (continuous_ofReal.add continuous_const).continuousOn (fun x hx => hsplit _ (hγne x hx)),
      intervalIntegral.integral_const_mul]
  have hTop : (∫ x in (-del)..T, F (x + (T : ℝ) * I) * K T (x + (T : ℝ) * I)) =
      (∫ x in (-del)..T, dslope F 0 (x + (T : ℝ) * I)) +
      F 0 * (∫ x in (-del)..T, ((x : ℂ) + (T : ℝ) * I)⁻¹) +
      (∫ x in (-del)..T, F (x + (T : ℝ) * I) * ((x + (T : ℝ) * I) / (T : ℂ) ^ 2)) := by
    let γ : ℝ → ℂ := fun x => x + (T : ℝ) * I
    have hγne : ∀ x ∈ Set.uIcc (-del) T, γ x ≠ 0 := fun x _ h => by
      have him := congrArg Complex.im h; simp [γ] at him; linarith
    have hγsub : γ '' Set.uIcc (-del) T ⊆ [[-del, T]] ×ℂ [[-T, T]] := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨by simpa [γ] using hx, by simp [γ, Set.right_mem_uIcc]⟩
    have hinv_cont : ContinuousOn (fun z : ℂ => F 0 * z⁻¹) (γ '' Set.uIcc (-del) T) :=
      continuousOn_const.mul (continuousOn_inv₀.mono (by rintro _ ⟨x, hx, rfl⟩; exact hγne x hx))
    rw [hEdgeInt (dslope F 0) (fun z => F 0 * z⁻¹) (fun z => F z * (z / (T : ℂ) ^ 2))
      (-del) T γ hγne (hd1.continuousOn.mono hγsub) hinv_cont (hd3.continuousOn.mono hγsub)
      (continuous_ofReal.add continuous_const).continuousOn (fun x hx => hsplit _ (hγne x hx)),
      intervalIntegral.integral_const_mul]
  have hRight : (∫ y in (-T)..T, F ((T : ℝ) + y * I) * K T ((T : ℝ) + y * I)) =
      (∫ y in (-T)..T, dslope F 0 ((T : ℝ) + y * I)) +
      F 0 * (∫ y in (-T)..T, ((T : ℝ) + y * I)⁻¹) +
      (∫ y in (-T)..T, F ((T : ℝ) + y * I) * (((T : ℝ) + y * I) / (T : ℂ) ^ 2)) := by
    let γ : ℝ → ℂ := fun y => (T : ℝ) + y * I
    have hγne : ∀ y ∈ Set.uIcc (-T) T, γ y ≠ 0 := fun y _ h => by
      have hre := congrArg Complex.re h; simp [γ] at hre; linarith
    have hγsub : γ '' Set.uIcc (-T) T ⊆ [[-del, T]] ×ℂ [[-T, T]] := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨by simp [γ, Set.right_mem_uIcc], by simpa [γ] using hy⟩
    have hinv_cont : ContinuousOn (fun z : ℂ => F 0 * z⁻¹) (γ '' Set.uIcc (-T) T) :=
      continuousOn_const.mul (continuousOn_inv₀.mono (by rintro _ ⟨y, hy, rfl⟩; exact hγne y hy))
    rw [hEdgeInt (dslope F 0) (fun z => F 0 * z⁻¹) (fun z => F z * (z / (T : ℂ) ^ 2))
      (-T) T γ hγne (hd1.continuousOn.mono hγsub) hinv_cont (hd3.continuousOn.mono hγsub)
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => hsplit _ (hγne y hy)),
      intervalIntegral.integral_const_mul]
  have hLeft : (∫ y in (-T)..T, F ((-del : ℝ) + y * I) * K T ((-del : ℝ) + y * I)) =
      (∫ y in (-T)..T, dslope F 0 ((-del : ℝ) + y * I)) +
      F 0 * (∫ y in (-T)..T, ((-del : ℝ) + y * I)⁻¹) +
      (∫ y in (-T)..T, F ((-del : ℝ) + y * I) * (((-del : ℝ) + y * I) / (T : ℂ) ^ 2)) := by
    let γ : ℝ → ℂ := fun y => (-del : ℝ) + y * I
    have hγne : ∀ y ∈ Set.uIcc (-T) T, γ y ≠ 0 := fun y _ h => by
      have hre := congrArg Complex.re h; simp [γ] at hre; linarith
    have hγsub : γ '' Set.uIcc (-T) T ⊆ [[-del, T]] ×ℂ [[-T, T]] := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨by simp [γ, Set.left_mem_uIcc], by simpa [γ] using hy⟩
    have hinv_cont : ContinuousOn (fun z : ℂ => F 0 * z⁻¹) (γ '' Set.uIcc (-T) T) :=
      continuousOn_const.mul (continuousOn_inv₀.mono (by rintro _ ⟨y, hy, rfl⟩; exact hγne y hy))
    rw [hEdgeInt (dslope F 0) (fun z => F 0 * z⁻¹) (fun z => F z * (z / (T : ℂ) ^ 2))
      (-T) T γ hγne (hd1.continuousOn.mono hγsub) hinv_cont (hd3.continuousOn.mono hγsub)
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => hsplit _ (hγne y hy)),
      intervalIntegral.integral_const_mul]
  have hsum : rectInt (fun z => F z * K T z) (-del) T (-T) T =
      rectInt (dslope F 0) (-del) T (-T) T +
      F 0 * rectInt (fun z => z⁻¹) (-del) T (-T) T +
      rectInt (fun z => F z * (z / (T : ℂ) ^ 2)) (-del) T (-T) T := by
    unfold rectInt
    rw [hBot, hTop, hRight, hLeft]
    ring
  rw [hsum, h0_1, h0_3, rectInt_inv del T hdel hT]
  ring

/-! ### Section 5: Kernel bounds, Dirichlet tail/partial-sum bounds, and Rectangular Newman Theorem -/

private lemma norm_K_horiz (T x : ℝ) (hT : 0 < T) (s : ℝ) (hs : s = T ∨ s = -T) :
    ‖K T ((x : ℂ) + s * I)‖ ≤ 2 * |x| / T ^ 2 := by
  have hs2 : s ^ 2 = T ^ 2 := by rcases hs with rfl | rfl <;> ring
  have hz_ne : (x : ℂ) + s * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    rcases hs with rfl | rfl <;> linarith
  have hT_ne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hK : K T ((x : ℂ) + s * I) =
      (((x ^ 2 : ℝ) : ℂ) + ((2 * x * s : ℝ) : ℂ) * I) / (((x : ℂ) + s * I) * (T : ℂ) ^ 2) := by
    unfold K
    have hs2C : (s : ℂ) ^ 2 = (T : ℂ) ^ 2 := by exact_mod_cast hs2
    field_simp [hz_ne, hT_ne]
    push_cast
    ring_nf
    rw [I_sq]
    ring_nf
    rw [hs2C]
    ring
  rw [hK, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  have hnum_le : ‖(((x ^ 2 : ℝ) : ℂ) + ((2 * x * s : ℝ) : ℂ) * I)‖ ≤
      2 * |x| * ‖(x : ℂ) + s * I‖ := by
    have hsq : ‖(((x ^ 2 : ℝ) : ℂ) + ((2 * x * s : ℝ) : ℂ) * I)‖ ^ 2 ≤
        (2 * |x| * ‖(x : ℂ) + s * I‖) ^ 2 := by
      have h1 : ‖(((x ^ 2 : ℝ) : ℂ) + ((2 * x * s : ℝ) : ℂ) * I)‖ ^ 2 =
          (x ^ 2) ^ 2 + (2 * x * s) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [sq]
      have h2 : ‖(x : ℂ) + s * I‖ ^ 2 = x ^ 2 + s ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [sq]
      rw [h1, show (2 * |x| * ‖(x : ℂ) + s * I‖) ^ 2 = 4 * |x| ^ 2 * ‖(x : ℂ) + s * I‖ ^ 2 by ring,
        sq_abs, h2]
      nlinarith [sq_nonneg x, sq_nonneg s]
    nlinarith [norm_nonneg (((x ^ 2 : ℝ) : ℂ) + ((2 * x * s : ℝ) : ℂ) * I),
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg x)) (norm_nonneg ((x : ℂ) + s * I))]
  have hznorm_pos : 0 < ‖(x : ℂ) + s * I‖ := norm_pos_iff.mpr hz_ne
  rw [div_le_div_iff₀ (mul_pos hznorm_pos (pow_pos hT 2)) (pow_pos hT 2)]
  nlinarith [pow_pos hT 2]

private lemma norm_K_vert (T x y : ℝ) (hT : 0 < T) (hx : x = T ∨ x = -T) (hy : |y| ≤ T) :
    ‖K T ((x : ℂ) + y * I)‖ ≤ 3 / T := by
  have hx2 : x ^ 2 = T ^ 2 := by rcases hx with rfl | rfl <;> ring
  have hnorm_sq : ‖(x : ℂ) + y * I‖ ^ 2 = T ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← hx2]
    simp [sq]
  have hnorm_ge : T ≤ ‖(x : ℂ) + y * I‖ := by
    nlinarith [norm_nonneg ((x : ℂ) + y * I), sq_nonneg y]
  have hnorm_le : ‖(x : ℂ) + y * I‖ ≤ 2 * T := by
    have hy2 : y ^ 2 ≤ T ^ 2 := by nlinarith [abs_le.mp hy]
    nlinarith [norm_nonneg ((x : ℂ) + y * I)]
  calc ‖K T ((x : ℂ) + y * I)‖
      ≤ ‖((x : ℂ) + y * I)⁻¹‖ + ‖((x : ℂ) + y * I) / (T : ℂ) ^ 2‖ := norm_add_le _ _
    _ = ‖(x : ℂ) + y * I‖⁻¹ + ‖(x : ℂ) + y * I‖ / T ^ 2 := by
        rw [norm_inv, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    _ ≤ T⁻¹ + (2 * T) / T ^ 2 := by
        gcongr
    _ = 3 / T := by
        field_simp [hT.ne']
        ring

private noncomputable def GN (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, lamC n / (n : ℂ) ^ (1 + z)

private lemma differentiable_GN (N : ℕ) : Differentiable ℂ (GN N) := by
  unfold GN
  refine Differentiable.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1)
  refine differentiable_const (lamC n) |>.div ?_ (fun z => Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))
  exact Differentiable.const_cpow (differentiable_const 1 |>.add differentiable_id) (Or.inl hn0)

private lemma sum_rpow_tail_le (N M : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Icc (N + 1) M, (n : ℝ) ^ (-(1 + x))) ≤ (N : ℝ) ^ (-x) / x := by
  by_cases hNM : N + 1 ≤ M
  · have hstep : ∀ n ∈ Finset.Icc (N + 1) M,
        (n : ℝ) ^ (-(1 + x)) ≤ ∫ u in ((n - 1 : ℕ) : ℝ)..(n : ℝ), u ^ (-(1 + x)) := by
      intro n hn
      have hn2 : 2 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
      have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
      have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le n 1)
      have hsub1 : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
        have h1 : 1 ≤ n := by omega
        rw [Nat.cast_sub h1, Nat.cast_one]; ring
      have hcont : ContinuousOn (fun u : ℝ => u ^ (-(1 + x))) (Set.uIcc ((n - 1 : ℕ) : ℝ) n) := by
        refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
        rw [Set.uIcc_of_le hle] at hu
        linarith [hu.1]
      calc (n : ℝ) ^ (-(1 + x))
          = ∫ _ in ((n - 1 : ℕ) : ℝ)..(n : ℝ), (n : ℝ) ^ (-(1 + x)) := by
            rw [intervalIntegral.integral_const, hsub1, one_smul]
        _ ≤ ∫ u in ((n - 1 : ℕ) : ℝ)..(n : ℝ), u ^ (-(1 + x)) := by
            refine intervalIntegral.integral_mono_on hle intervalIntegrable_const hcont.intervalIntegrable
              fun u hu => ?_
            exact Real.rpow_le_rpow_of_nonpos (by linarith [hu.1]) hu.2 (by linarith)
    have hsum_le : (∑ n ∈ Finset.Icc (N + 1) M, (n : ℝ) ^ (-(1 + x))) ≤
        ∑ n ∈ Finset.Icc (N + 1) M, ∫ u in ((n - 1 : ℕ) : ℝ)..(n : ℝ), u ^ (-(1 + x)) :=
      Finset.sum_le_sum hstep
    have htelescope : (∑ n ∈ Finset.Icc (N + 1) M, ∫ u in ((n - 1 : ℕ) : ℝ)..(n : ℝ), u ^ (-(1 + x))) =
        ∫ u in (N : ℝ)..(M : ℝ), u ^ (-(1 + x)) := by
      have hshift : ∀ k : ℕ,
          (∑ n ∈ Finset.Icc (N + 1) (N + k), ∫ u in ((n - 1 : ℕ) : ℝ)..(n : ℝ), u ^ (-(1 + x))) =
          ∫ u in (N : ℝ)..((N + k : ℕ) : ℝ), u ^ (-(1 + x)) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hIcc : Finset.Icc (N + 1) (N + (k + 1)) = insert (N + k + 1) (Finset.Icc (N + 1) (N + k)) := by
            ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have hnotmem : N + k + 1 ∉ Finset.Icc (N + 1) (N + k) := by simp
          rw [hIcc, Finset.sum_insert hnotmem, ih, Nat.add_sub_cancel]
          have hcont1 : ContinuousOn (fun u : ℝ => u ^ (-(1 + x))) (Set.uIcc (N : ℝ) ((N + k : ℕ) : ℝ)) := by
            refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
            rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_add_right N k)] at hu
            have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
            linarith [hu.1]
          have hcont2 : ContinuousOn (fun u : ℝ => u ^ (-(1 + x))) (Set.uIcc ((N + k : ℕ) : ℝ) ((N + k + 1 : ℕ) : ℝ)) := by
            refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
            rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ (N + k))] at hu
            have hNpos : (0 : ℝ) < ((N + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N + k)
            linarith [hu.1]
          rw [add_comm]
          exact intervalIntegral.integral_add_adjacent_intervals hcont1.intervalIntegrable hcont2.intervalIntegrable
      have hM : M = N + (M - N) := (Nat.add_sub_of_le (by omega)).symm
      rw [hM, hshift (M - N)]
    have hint : ∫ u in (N : ℝ)..(M : ℝ), u ^ (-(1 + x)) =
        ((M : ℝ) ^ (-x) - (N : ℝ) ^ (-x)) / (-x) := by
      have h0not : (0 : ℝ) ∉ Set.uIcc (N : ℝ) (M : ℝ) := by
        rw [Set.uIcc_of_le (by exact_mod_cast (by omega : N ≤ M))]
        simp only [Set.mem_Icc, not_and_or, not_le]
        left
        exact_mod_cast (by omega : 0 < N)
      rw [integral_rpow (Or.inr ⟨by linarith, h0not⟩)]
      have hpow : -(1 + x) + 1 = -x := by ring
      rw [hpow]
    calc (∑ n ∈ Finset.Icc (N + 1) M, (n : ℝ) ^ (-(1 + x)))
        ≤ ∫ u in (N : ℝ)..(M : ℝ), u ^ (-(1 + x)) := htelescope ▸ hsum_le
      _ = ((M : ℝ) ^ (-x) - (N : ℝ) ^ (-x)) / (-x) := hint
      _ = ((N : ℝ) ^ (-x) - (M : ℝ) ^ (-x)) / x := by field_simp [hx.ne']; ring
      _ ≤ (N : ℝ) ^ (-x) / x := by
          gcongr
          linarith [Real.rpow_nonneg (Nat.cast_nonneg M) (-x)]
  · have hemp : Finset.Icc (N + 1) M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) (-x)) hx.le

private lemma norm_G_sub_GN_mul_cpow_le (N : ℕ) (hN : 1 ≤ N) {z : ℂ} (hz : 0 < z.re) :
    ‖(G z - GN N z) * (N : ℂ) ^ z‖ ≤ 1 / z.re := by
  have hre : 1 < (1 + z).re := by simp; linarith
  rw [G_eq_LSeries hz]
  have hsumb : Summable (LSeries.term lamC (1 + z)) := LSeriesSummable_lamC hre
  have hfin : GN N z = ∑ n ∈ Finset.range (N + 1), LSeries.term lamC (1 + z) n := by
    unfold GN
    rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < N + 1)]
    have hIco : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := rfl
    rw [LSeries.term_zero, zero_add, hIco]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero hn0]
  have hsub : LSeries lamC (1 + z) - GN N z =
      ∑' k : ℕ, LSeries.term lamC (1 + z) (k + (N + 1)) := by
    unfold LSeries
    rw [hfin, sub_eq_iff_eq_add', hsumb.sum_add_tsum_nat_add (N + 1)]
  have hsumb_tail : Summable (fun k : ℕ => ‖LSeries.term lamC (1 + z) (k + (N + 1))‖) :=
    (hsumb.norm).comp_injective (add_left_injective (N + 1))
  have htail_le : ‖LSeries lamC (1 + z) - GN N z‖ ≤ (N : ℝ) ^ (-z.re) / z.re := by
    rw [hsub]
    calc ‖∑' k : ℕ, LSeries.term lamC (1 + z) (k + (N + 1))‖
        ≤ ∑' k : ℕ, ‖LSeries.term lamC (1 + z) (k + (N + 1))‖ :=
          norm_tsum_le_tsum_norm hsumb_tail
      _ ≤ (N : ℝ) ^ (-z.re) / z.re := by
          refine hsumb_tail.tsum_le_of_sum_range_le fun m => ?_
          calc (∑ k ∈ Finset.range m, ‖LSeries.term lamC (1 + z) (k + (N + 1))‖)
              ≤ ∑ k ∈ Finset.range m, ((k + (N + 1) : ℕ) : ℝ) ^ (-(1 + z.re)) := by
                refine Finset.sum_le_sum fun k _ => ?_
                have hk0 : k + (N + 1) ≠ 0 := by omega
                rw [LSeries.term_of_ne_zero hk0, norm_div,
                  Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk0),
                  add_re, one_re, Real.rpow_neg (Nat.cast_nonneg _), ← one_div]
                exact div_le_div_of_nonneg_right (norm_lamC_le_one _)
                  (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            _ = ∑ n ∈ Finset.Icc (N + 1) (N + m), (n : ℝ) ^ (-(1 + z.re)) := by
                refine Finset.sum_bij (fun k _ => k + (N + 1)) ?_ ?_ ?_ ?_
                · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
                · intro a _ b _ hab; omega
                · intro n hn; simp only [Finset.mem_Icc] at hn
                  exact ⟨n - (N + 1), by simp only [Finset.mem_range]; omega, by omega⟩
                · intro k _; rfl
            _ ≤ (N : ℝ) ^ (-z.re) / z.re := sum_rpow_tail_le N (N + m) hN hz
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < N)]
  calc ‖LSeries lamC (1 + z) - GN N z‖ * (N : ℝ) ^ z.re
      ≤ ((N : ℝ) ^ (-z.re) / z.re) * (N : ℝ) ^ z.re :=
        mul_le_mul_of_nonneg_right htail_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = 1 / z.re := by
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        rw [div_mul_eq_mul_div, ← Real.rpow_add hNpos, neg_add_cancel, Real.rpow_zero]

private lemma sum_rpow_left_le (N : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (x - 1)) ≤ (N : ℝ) ^ x / x + (N : ℝ) ^ (x - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hint : ∫ u in (1 : ℝ)..(N : ℝ), u ^ (x - 1) = ((N : ℝ) ^ x - 1) / x := by
    have h0not : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hN)]
      simp only [Set.mem_Icc, not_and_or, not_le]; left; norm_num
    rw [integral_rpow (Or.inl (by linarith))]
    have hpow : x - 1 + 1 = x := by ring
    rw [hpow, Real.one_rpow]
  by_cases hx1 : x ≤ 1
  · -- Antitone on [1, N]: split off n = 1, integrate n = 2..N
    have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h1not : 1 ∉ Finset.Icc 2 N := by simp
    rw [hIcc, Finset.sum_insert h1not, Nat.cast_one, Real.one_rpow]
    have hsum2 : (∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (x - 1)) ≤ ∫ u in (1 : ℝ)..(N : ℝ), u ^ (x - 1) := by
      have hstep : ∀ n ∈ Finset.Icc 2 N,
          (n : ℝ) ^ (x - 1) ≤ ∫ u in ((n - 1 : ℕ) : ℝ)..(n : ℝ), u ^ (x - 1) := by
        intro n hn
        have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le n 1)
        have hsub1 : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]; ring
        have hcont : ContinuousOn (fun u : ℝ => u ^ (x - 1)) (Set.uIcc ((n - 1 : ℕ) : ℝ) n) := by
          refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
          rw [Set.uIcc_of_le hle] at hu
          have hpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
          linarith [hu.1]
        calc (n : ℝ) ^ (x - 1)
            = ∫ _ in ((n - 1 : ℕ) : ℝ)..(n : ℝ), (n : ℝ) ^ (x - 1) := by
              rw [intervalIntegral.integral_const, hsub1, one_smul]
          _ ≤ ∫ u in ((n - 1 : ℕ) : ℝ)..(n : ℝ), u ^ (x - 1) := by
              refine intervalIntegral.integral_mono_on hle intervalIntegrable_const hcont.intervalIntegrable
                fun u hu => ?_
              have hpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
              exact Real.rpow_le_rpow_of_nonpos (by linarith [hu.1]) hu.2 (by linarith)
      have htel : ∀ M : ℕ, 1 ≤ M →
          (∑ n ∈ Finset.Icc 2 M, ∫ u in ((n - 1 : ℕ) : ℝ)..(n : ℝ), u ^ (x - 1)) =
          ∫ u in (1 : ℝ)..(M : ℝ), u ^ (x - 1) := by
        intro M hM
        induction M with
        | zero => omega
        | succ M ih =>
          by_cases hM0 : M = 0
          · subst hM0; simp
          · have hM1 : 1 ≤ M := by omega
            have hIcc' : Finset.Icc 2 (M + 1) = insert (M + 1) (Finset.Icc 2 M) := by
              ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            have hnm : M + 1 ∉ Finset.Icc 2 M := by simp
            rw [hIcc', Finset.sum_insert hnm, ih hM1, Nat.add_sub_cancel, add_comm]
            have hc1 : ContinuousOn (fun u : ℝ => u ^ (x - 1)) (Set.uIcc (1 : ℝ) (M : ℝ)) := by
              refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
              rw [Set.uIcc_of_le (by exact_mod_cast hM1)] at hu; linarith [hu.1]
            have hc2 : ContinuousOn (fun u : ℝ => u ^ (x - 1)) (Set.uIcc (M : ℝ) ((M + 1 : ℕ) : ℝ)) := by
              refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
              rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ M)] at hu
              have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
              linarith [hu.1]
            exact intervalIntegral.integral_add_adjacent_intervals hc1.intervalIntegrable hc2.intervalIntegrable
      exact (htel N hN) ▸ Finset.sum_le_sum hstep
    have hcalc : 1 + ((N : ℝ) ^ x - 1) / x ≤ (N : ℝ) ^ x / x := by
      rw [← sub_nonneg]
      have : (N : ℝ) ^ x / x - (1 + ((N : ℝ) ^ x - 1) / x) = (1 - x) / x := by
        field_simp [hx.ne']; ring
      rw [this]
      exact div_nonneg (by linarith) hx.le
    linarith [hsum2, hint, hcalc, Real.rpow_nonneg (Nat.cast_nonneg N) (x - 1)]
  · -- Monotone on [1, N]: split off n = N, integrate n = 1..N-1
    push Not at hx1
    have hIcc : Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hNnot : N ∉ Finset.Icc 1 (N - 1) := by simp; omega
    rw [hIcc, Finset.sum_insert hNnot, add_comm]
    have hsum1 : (∑ n ∈ Finset.Icc 1 (N - 1), (n : ℝ) ^ (x - 1)) ≤
        ∫ u in (1 : ℝ)..(N : ℝ), u ^ (x - 1) := by
      have hstep : ∀ n ∈ Finset.Icc 1 (N - 1),
          (n : ℝ) ^ (x - 1) ≤ ∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ), u ^ (x - 1) := by
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
        have hsub1 : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
        have hcont : ContinuousOn (fun u : ℝ => u ^ (x - 1)) (Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ)) := by
          refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
          rw [Set.uIcc_of_le hle] at hu
          have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          linarith [hu.1]
        calc (n : ℝ) ^ (x - 1)
            = ∫ _ in (n : ℝ)..((n + 1 : ℕ) : ℝ), (n : ℝ) ^ (x - 1) := by
              rw [intervalIntegral.integral_const, hsub1, one_smul]
          _ ≤ ∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ), u ^ (x - 1) := by
              refine intervalIntegral.integral_mono_on hle intervalIntegrable_const hcont.intervalIntegrable
                fun u hu => ?_
              exact Real.rpow_le_rpow (Nat.cast_nonneg n) hu.1 (by linarith)
      have htel : ∀ M : ℕ, 1 ≤ M →
          (∑ n ∈ Finset.Icc 1 (M - 1), ∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ), u ^ (x - 1)) =
          ∫ u in (1 : ℝ)..(M : ℝ), u ^ (x - 1) := by
        intro M hM
        induction M with
        | zero => omega
        | succ M ih =>
          by_cases hM0 : M = 0
          · subst hM0; simp
          · have hM1 : 1 ≤ M := by omega
            have hIcc' : Finset.Icc 1 M = insert M (Finset.Icc 1 (M - 1)) := by
              ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            have hnm : M ∉ Finset.Icc 1 (M - 1) := by simp; omega
            rw [Nat.add_sub_cancel, hIcc', Finset.sum_insert hnm, ih hM1, add_comm]
            have hc1 : ContinuousOn (fun u : ℝ => u ^ (x - 1)) (Set.uIcc (1 : ℝ) (M : ℝ)) := by
              refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
              rw [Set.uIcc_of_le (by exact_mod_cast hM1)] at hu; linarith [hu.1]
            have hc2 : ContinuousOn (fun u : ℝ => u ^ (x - 1)) (Set.uIcc (M : ℝ) ((M + 1 : ℕ) : ℝ)) := by
              refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
              rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ M)] at hu
              have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
              linarith [hu.1]
            exact intervalIntegral.integral_add_adjacent_intervals hc1.intervalIntegrable hc2.intervalIntegrable
      exact (htel N hN) ▸ Finset.sum_le_sum hstep
    have hdiv : ((N : ℝ) ^ x - 1) / x ≤ (N : ℝ) ^ x / x := by
      gcongr; linarith
    linarith [hsum1, hint, hdiv]

private lemma norm_GN_mul_cpow_le (N : ℕ) (hN : 1 ≤ N) {z : ℂ} (hz : z.re < 0) :
    ‖GN N z * (N : ℂ) ^ z‖ ≤ 1 / (-z.re) + 1 / (N : ℝ) := by
  have hx : 0 < -z.re := neg_pos.mpr hz
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hGN : ‖GN N z‖ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ ((-z.re) - 1) := by
    unfold GN
    calc ‖∑ n ∈ Finset.Icc 1 N, lamC n / (n : ℂ) ^ (1 + z)‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖lamC n / (n : ℂ) ^ (1 + z)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ ((-z.re) - 1) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
          rw [norm_div, Complex.norm_natCast_cpow_of_pos hn0, add_re, one_re,
            show (-z.re) - 1 = -(1 + z.re) by ring, Real.rpow_neg (Nat.cast_nonneg n), ← one_div]
          exact div_le_div_of_nonneg_right (norm_lamC_le_one n)
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < N)]
  calc ‖GN N z‖ * (N : ℝ) ^ z.re
      ≤ ((N : ℝ) ^ (-z.re) / (-z.re) + (N : ℝ) ^ ((-z.re) - 1)) * (N : ℝ) ^ z.re := by
        exact mul_le_mul_of_nonneg_right (hGN.trans (sum_rpow_left_le N hN hx))
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = 1 / (-z.re) + 1 / (N : ℝ) := by
        rw [add_mul, div_mul_eq_mul_div, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos,
          neg_add_cancel, Real.rpow_zero, show (-z.re) - 1 + z.re = -1 by ring,
          Real.rpow_neg_one, one_div, one_div]

private lemma integral_rpow_neg_delta_zero (N : ℕ) (hN : 2 ≤ N) {del : ℝ} (_hdel : 0 < del) :
    (∫ x in (-del)..(0 : ℝ), (N : ℝ) ^ x) ≤ 1 / Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hderiv : ∀ x ∈ Set.uIcc (-del) (0 : ℝ),
      HasDerivAt (fun t : ℝ => (N : ℝ) ^ t / Real.log (N : ℝ)) ((N : ℝ) ^ x) x := by
    intro x _
    have h : HasDerivAt (fun t : ℝ => (N : ℝ) ^ t / Real.log (N : ℝ))
        (((N : ℝ) ^ x * Real.log (N : ℝ)) / Real.log (N : ℝ)) x :=
      ((Real.hasStrictDerivAt_const_rpow hNpos x).hasDerivAt).div_const (Real.log (N : ℝ))
    rwa [mul_div_cancel_right₀ _ hlog_pos.ne'] at h
  have hcont : ContinuousOn (fun t : ℝ => (N : ℝ) ^ t) (Set.uIcc (-del) (0 : ℝ)) :=
    (Continuous.rpow continuous_const continuous_id (fun _ => Or.inl hNpos.ne')).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
    Real.rpow_zero, ← sub_div]
  gcongr
  linarith [Real.rpow_nonneg hNpos.le (-del)]

private lemma tendsto_GN_zero : Tendsto (fun N : ℕ => GN N 0) atTop (𝓝 (G 0)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set T : ℝ := max 1 (10 / ε)
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hT_eps : 10 / ε ≤ T := le_max_right _ _
  -- Find del ∈ (0, T] such that [-del, T] × [-T, T] ⊆ Udom
  have hK0_compact : IsCompact (Set.Icc (0 : ℝ) T ×ℂ Set.Icc (-T) T) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hK0_sub : Set.Icc (0 : ℝ) T ×ℂ Set.Icc (-T) T ⊆ Udom := by
    intro z hz
    exact halfPlane_subset_Udom hz.1.1
  obtain ⟨r, hr_pos, hr_sub⟩ := hK0_compact.exists_thickening_subset_open isOpen_Udom hK0_sub
  set del : ℝ := min (r / 2) (T / 2)
  have hdel_pos : 0 < del := lt_min (half_pos hr_pos) (half_pos hT_pos)
  have hdel_lt_r : del < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr_pos)
  have hdel_le_T : del ≤ T := le_trans (min_le_right _ _) (by linarith)
  have hRect_sub : ([[-del, T]] ×ℂ [[-T, T]]) ⊆ Udom := by
    intro z hz
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hz
    apply hr_sub
    rw [Metric.mem_thickening_iff]
    refine ⟨((max 0 z.re : ℝ) : ℂ) + (z.im : ℂ) * I, ?_, ?_⟩
    · simp only [Complex.mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
      exact ⟨⟨le_max_left _ _, max_le hT_pos.le hz.1.2⟩, hz.2⟩
    · rw [Complex.dist_eq]
      have hdiff : z - (((max 0 z.re : ℝ) : ℂ) + (z.im : ℂ) * I) = ((z.re - max 0 z.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
      by_cases hzr : 0 ≤ z.re
      · rw [max_eq_right hzr, sub_self, abs_zero]; exact hr_pos
      · push Not at hzr
        rw [max_eq_left hzr.le, sub_zero, abs_of_neg hzr]
        linarith [hz.1.1]
  have hG_diff : DifferentiableOn ℂ G ([[-del, T]] ×ℂ [[-T, T]]) :=
    differentiableOn_G_Udom.mono hRect_sub
  -- Compact bound M for ‖G z * K T z‖ on the 3 left edges of [-del, 0] × [-T, T]
  let EbotL : Set ℂ := (fun x : ℝ => (x : ℂ) + (-T : ℝ) * I) '' Set.Icc (-del) 0
  let EtopL : Set ℂ := (fun x : ℝ => (x : ℂ) + (T : ℝ) * I) '' Set.Icc (-del) 0
  let EvertL : Set ℂ := (fun y : ℝ => (-del : ℝ) + y * I) '' Set.Icc (-T) T
  have hGK_cont : ∀ E : Set ℂ, IsCompact E → E ⊆ ([[-del, T]] ×ℂ [[-T, T]]) → (0 : ℂ) ∉ E →
      ∃ C ≥ 0, ∀ z ∈ E, ‖G z * K T z‖ ≤ C := by
    intro E hEc hEsub h0not
    have hc : ContinuousOn (fun z => G z * K T z) E := by
      refine (hG_diff.continuousOn.mono hEsub).mul ?_
      exact (continuousOn_inv₀.mono (fun z hz => ne_of_mem_of_not_mem hz h0not)).add
        (continuousOn_id.div_const _)
    obtain ⟨C, hC⟩ := hEc.exists_bound_of_continuousOn hc
    exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩
  have hEbotL_sub : EbotL ⊆ [[-del, T]] ×ℂ [[-T, T]] := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact ⟨⟨by simpa using hx.1, by simp; linarith [hx.2]⟩, by simp; linarith⟩
  have hEtopL_sub : EtopL ⊆ [[-del, T]] ×ℂ [[-T, T]] := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact ⟨⟨by simpa using hx.1, by simp; linarith [hx.2]⟩, by simp; linarith⟩
  have hEvertL_sub : EvertL ⊆ [[-del, T]] ×ℂ [[-T, T]] := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact ⟨by simp; linarith, by simpa using hy⟩
  obtain ⟨M1, hM1_nn, hM1⟩ := hGK_cont EbotL
    (isCompact_Icc.image (continuous_ofReal.add continuous_const)) hEbotL_sub
    (by rintro ⟨x, _, h⟩; have := congrArg Complex.im h; simp at this; linarith)
  obtain ⟨M2, hM2_nn, hM2⟩ := hGK_cont EtopL
    (isCompact_Icc.image (continuous_ofReal.add continuous_const)) hEtopL_sub
    (by rintro ⟨x, _, h⟩; have := congrArg Complex.im h; simp at this; linarith)
  obtain ⟨M3, hM3_nn, hM3⟩ := hGK_cont EvertL
    (isCompact_Icc.image (continuous_const.add (continuous_ofReal.mul continuous_const))) hEvertL_sub
    (by rintro ⟨y, _, h⟩; have := congrArg Complex.re h; simp at this; linarith)
  set M : ℝ := max M1 (max M2 M3)
  have hM_nn : 0 ≤ M := le_trans hM1_nn (le_max_left _ _)
  -- Main bound for every N ≥ 2
  have hMain : ∀ N : ℕ, 2 ≤ N →
      ‖G 0 - GN N 0‖ ≤ (20 / T + 10 / (N : ℝ) + 2 * M / Real.log (N : ℝ) +
        2 * T * M * (N : ℝ) ^ (-del)) / (2 * Real.pi) := by
    intro N hN2
    have hN1 : 1 ≤ N := by omega
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hNC0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    let F : ℂ → ℂ := fun z => (G z - GN N z) * (N : ℂ) ^ z
    let H : ℂ → ℂ := fun z => F z * K T z
    let H1 : ℂ → ℂ := fun z => G z * (N : ℂ) ^ z * K T z
    let H2 : ℂ → ℂ := fun z => GN N z * (N : ℂ) ^ z * K T z
    have hF_diff : DifferentiableOn ℂ F ([[-del, T]] ×ℂ [[-T, T]]) :=
      (hG_diff.sub (differentiable_GN N).differentiableOn).mul
        (Differentiable.const_cpow differentiable_id (Or.inl hNC0)).differentiableOn
    have hCauchy := cauchy_rect_kernel hdel_pos hT_pos hF_diff
    have hF0 : F 0 = G 0 - GN N 0 := by simp [F]
    -- H2 is differentiable on [-T, -del] × [-T, T]
    have hH2_diff_L : DifferentiableOn ℂ H2 ([[-T, -del]] ×ℂ [[-T, T]]) := by
      intro z hz
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hz
      have hz0 : z ≠ 0 := by
        intro h; have hle := hz.1.2; rw [h, zero_re] at hle; linarith
      have hK_diff : DifferentiableAt ℂ (K T) z :=
        (differentiableAt_inv hz0).add (differentiableAt_id.div_const _)
      exact ((((differentiable_GN N).differentiableAt.mul
        (Differentiable.const_cpow differentiable_id (Or.inl hNC0)).differentiableAt)).mul
        hK_diff).differentiableWithinAt
    have hH2_rect0 : rectInt H2 (-T) (-del) (-T) T = 0 :=
      rectInt_eq_zero_of_differentiableOn hH2_diff_L
    -- Continuity helpers for splitting integrals
    have hH_cont_bot : ContinuousOn (fun x : ℝ => H (x + (-T : ℝ) * I)) (Set.uIcc (-del) T) := by
      refine ((hF_diff.continuousOn.comp (continuous_ofReal.add continuous_const).continuousOn
        (fun x hx => ⟨by simpa using hx, by simp [Set.left_mem_uIcc]⟩)).mul ?_)
      refine ((continuousOn_inv₀.comp (continuous_ofReal.add continuous_const).continuousOn
        (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)).add
        (((continuous_ofReal.add continuous_const).continuousOn).div_const _))
    have hH_cont_top : ContinuousOn (fun x : ℝ => H (x + (T : ℝ) * I)) (Set.uIcc (-del) T) := by
      refine ((hF_diff.continuousOn.comp (continuous_ofReal.add continuous_const).continuousOn
        (fun x hx => ⟨by simpa using hx, by simp [Set.right_mem_uIcc]⟩)).mul ?_)
      refine ((continuousOn_inv₀.comp (continuous_ofReal.add continuous_const).continuousOn
        (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)).add
        (((continuous_ofReal.add continuous_const).continuousOn).div_const _))
    have hH1_cont_bot : ContinuousOn (fun x : ℝ => H1 (x + (-T : ℝ) * I)) (Set.uIcc (-del) 0) := by
      have hsub : Set.uIcc (-del) 0 ⊆ Set.uIcc (-del) T := by
        rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc_right hT_pos.le
      refine (((hG_diff.continuousOn.comp (continuous_ofReal.add continuous_const).continuousOn
        (fun x hx => ⟨by simpa using hsub hx, by simp [Set.left_mem_uIcc]⟩)).mul
        ((Differentiable.const_cpow differentiable_id (Or.inl hNC0)).continuous.comp
          (continuous_ofReal.add continuous_const)).continuousOn).mul ?_)
      exact (continuousOn_inv₀.comp (continuous_ofReal.add continuous_const).continuousOn
        (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)).add
        (((continuous_ofReal.add continuous_const).continuousOn).div_const _)
    have hH1_cont_top : ContinuousOn (fun x : ℝ => H1 (x + (T : ℝ) * I)) (Set.uIcc (-del) 0) := by
      have hsub : Set.uIcc (-del) 0 ⊆ Set.uIcc (-del) T := by
        rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc_right hT_pos.le
      refine (((hG_diff.continuousOn.comp (continuous_ofReal.add continuous_const).continuousOn
        (fun x hx => ⟨by simpa using hsub hx, by simp [Set.right_mem_uIcc]⟩)).mul
        ((Differentiable.const_cpow differentiable_id (Or.inl hNC0)).continuous.comp
          (continuous_ofReal.add continuous_const)).continuousOn).mul ?_)
      exact (continuousOn_inv₀.comp (continuous_ofReal.add continuous_const).continuousOn
        (fun x _ h => by have := congrArg Complex.im h; simp at this; linarith)).add
        (((continuous_ofReal.add continuous_const).continuousOn).div_const _)
    have hH1_cont_vert : ContinuousOn (fun y : ℝ => H1 ((-del : ℝ) + y * I)) (Set.uIcc (-T) T) := by
      refine (((hG_diff.continuousOn.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
        (fun y hy => ⟨by simp [Set.left_mem_uIcc], by simpa using hy⟩)).mul
        ((Differentiable.const_cpow differentiable_id (Or.inl hNC0)).continuous.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn).mul ?_)
      exact (continuousOn_inv₀.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
        (fun y _ h => by have := congrArg Complex.re h; simp at this; linarith)).add
        (((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn).div_const _)
    have hH2_cont_horiz : ∀ s : ℝ, s ≠ 0 → Continuous (fun x : ℝ => H2 (x + s * I)) := by
      intro s hs
      refine (((differentiable_GN N).continuous.comp (continuous_ofReal.add continuous_const)).mul
        ((Differentiable.const_cpow differentiable_id (Or.inl hNC0)).continuous.comp
          (continuous_ofReal.add continuous_const))).mul ?_
      exact (Continuous.inv₀ (continuous_ofReal.add continuous_const)
        (fun x h => by have := congrArg Complex.im h; simp at this; exact hs this)).add
        ((continuous_ofReal.add continuous_const).div_const _)
    have hH2_cont_vert : ContinuousOn (fun y : ℝ => H2 ((-del : ℝ) + y * I)) (Set.uIcc (-T) T) := by
      refine (((differentiable_GN N).continuous.comp
        (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn.mul
        ((Differentiable.const_cpow differentiable_id (Or.inl hNC0)).continuous.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn).mul ?_
      exact (continuousOn_inv₀.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
        (fun y _ h => by have := congrArg Complex.re h; simp at this; linarith)).add
        (((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn).div_const _)
    -- Split integrals at 0 and combine H2 integrals using hH2_rect0
    have hSub_eq : ∀ z, H z = H1 z - H2 z := fun z => by simp [H, F, H1, H2, sub_mul]
    have hBot_split : (∫ x in (-del)..T, H (x + (-T : ℝ) * I)) =
        (∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)) +
        (∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)) -
        (∫ x in (-del)..(0 : ℝ), H2 (x + (-T : ℝ) * I)) := by
      have hsub1 : Set.uIcc (-del) 0 ⊆ Set.uIcc (-del) T := by
        rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc_right hT_pos.le
      have hsub2 : Set.uIcc 0 T ⊆ Set.uIcc (-del) T := by
        rw [Set.uIcc_of_le hT_pos.le, Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc_left (by linarith)
      have h1 := (intervalIntegral.integral_add_adjacent_intervals
        ((hH_cont_bot.mono hsub1).intervalIntegrable (μ := volume))
        ((hH_cont_bot.mono hsub2).intervalIntegrable (μ := volume))).symm
      rw [h1]
      have h2 : (∫ x in (-del)..(0 : ℝ), H (x + (-T : ℝ) * I)) =
          (∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)) -
          (∫ x in (-del)..(0 : ℝ), H2 (x + (-T : ℝ) * I)) := by
        simp_rw [hSub_eq]
        exact intervalIntegral.integral_sub hH1_cont_bot.intervalIntegrable
          ((hH2_cont_horiz (-T) (neg_ne_zero.mpr hT_pos.ne')).intervalIntegrable (μ := volume) _ _)
      rw [h2]; ring
    have hTop_split : (∫ x in (-del)..T, H (x + (T : ℝ) * I)) =
        (∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)) +
        (∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)) -
        (∫ x in (-del)..(0 : ℝ), H2 (x + (T : ℝ) * I)) := by
      have hsub1 : Set.uIcc (-del) 0 ⊆ Set.uIcc (-del) T := by
        rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc_right hT_pos.le
      have hsub2 : Set.uIcc 0 T ⊆ Set.uIcc (-del) T := by
        rw [Set.uIcc_of_le hT_pos.le, Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc_left (by linarith)
      have h1 := (intervalIntegral.integral_add_adjacent_intervals
        ((hH_cont_top.mono hsub1).intervalIntegrable (μ := volume))
        ((hH_cont_top.mono hsub2).intervalIntegrable (μ := volume))).symm
      rw [h1]
      have h2 : (∫ x in (-del)..(0 : ℝ), H (x + (T : ℝ) * I)) =
          (∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)) -
          (∫ x in (-del)..(0 : ℝ), H2 (x + (T : ℝ) * I)) := by
        simp_rw [hSub_eq]
        exact intervalIntegral.integral_sub hH1_cont_top.intervalIntegrable
          ((hH2_cont_horiz T hT_pos.ne').intervalIntegrable (μ := volume) _ _)
      rw [h2]; ring
    have hVert_split : (∫ y in (-T)..T, H ((-del : ℝ) + y * I)) =
        (∫ y in (-T)..T, H1 ((-del : ℝ) + y * I)) - (∫ y in (-T)..T, H2 ((-del : ℝ) + y * I)) := by
      simp_rw [hSub_eq]
      exact intervalIntegral.integral_sub hH1_cont_vert.intervalIntegrable hH2_cont_vert.intervalIntegrable
    have hH2_bot_merge : (∫ x in (-T)..(-del), H2 (x + (-T : ℝ) * I)) +
        (∫ x in (-del)..(0 : ℝ), H2 (x + (-T : ℝ) * I)) =
        ∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hH2_cont_horiz (-T) (neg_ne_zero.mpr hT_pos.ne')).intervalIntegrable (μ := volume) _ _)
        ((hH2_cont_horiz (-T) (neg_ne_zero.mpr hT_pos.ne')).intervalIntegrable (μ := volume) _ _)
    have hH2_top_merge : (∫ x in (-T)..(-del), H2 (x + (T : ℝ) * I)) +
        (∫ x in (-del)..(0 : ℝ), H2 (x + (T : ℝ) * I)) =
        ∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hH2_cont_horiz T hT_pos.ne').intervalIntegrable (μ := volume) _ _)
        ((hH2_cont_horiz T hT_pos.ne').intervalIntegrable (μ := volume) _ _)
    have hDecomp : 2 * Real.pi * I * (G 0 - GN N 0) =
        (∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)) -
        (∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)) +
        I * (∫ y in (-T)..T, H ((T : ℝ) + y * I)) +
        ((∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)) -
         (∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)) -
         I * (∫ y in (-T)..T, H1 ((-del : ℝ) + y * I))) +
        (-(∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)) +
          (∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I)) +
          I * (∫ y in (-T)..T, H2 ((-T : ℝ) + y * I))) := by
      rw [← hF0, ← hCauchy]
      have h0 : rectInt H (-del) T (-T) T = rectInt H (-del) T (-T) T - rectInt H2 (-T) (-del) (-T) T := by
        rw [hH2_rect0, sub_zero]
      rw [h0]
      unfold rectInt
      rw [hBot_split, hTop_split, hVert_split, ← hH2_bot_merge, ← hH2_top_merge]
      ring
    -- Now bound each of the 9 integrals!
    have b1 : ‖∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)‖ ≤ 2 / T := by
      have hle : ‖∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)‖ ≤ (2 / T ^ 2) * |T - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
        rw [Set.uIoc_of_le hT_pos.le] at hx
        have hx_pos : 0 < x := hx.1
        rw [show H (x + (-T : ℝ) * I) = F (x + (-T : ℝ) * I) * K T (x + (-T : ℝ) * I) from rfl, norm_mul]
        have hF_le := norm_G_sub_GN_mul_cpow_le N hN1 (z := (x : ℂ) + (-T : ℝ) * I) (by simpa using hx_pos)
        have hK_le := norm_K_horiz T x hT_pos (-T) (Or.inr rfl)
        rw [abs_of_pos hx_pos] at hK_le
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero] at hF_le
        calc ‖F (x + (-T : ℝ) * I)‖ * ‖K T (x + (-T : ℝ) * I)‖
            ≤ (1 / x) * (2 * x / T ^ 2) :=
              mul_le_mul hF_le hK_le (norm_nonneg _) (by positivity)
          _ = 2 / T ^ 2 := by field_simp [hx_pos.ne']
      calc ‖∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)‖
          ≤ (2 / T ^ 2) * |T - 0| := hle
        _ = 2 / T := by rw [sub_zero, abs_of_pos hT_pos]; field_simp [hT_pos.ne']
    have b2 : ‖∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)‖ ≤ 2 / T := by
      have hle : ‖∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)‖ ≤ (2 / T ^ 2) * |T - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
        rw [Set.uIoc_of_le hT_pos.le] at hx
        have hx_pos : 0 < x := hx.1
        rw [show H (x + (T : ℝ) * I) = F (x + (T : ℝ) * I) * K T (x + (T : ℝ) * I) from rfl, norm_mul]
        have hF_le := norm_G_sub_GN_mul_cpow_le N hN1 (z := (x : ℂ) + (T : ℝ) * I) (by simpa using hx_pos)
        have hK_le := norm_K_horiz T x hT_pos T (Or.inl rfl)
        rw [abs_of_pos hx_pos] at hK_le
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero] at hF_le
        calc ‖F (x + (T : ℝ) * I)‖ * ‖K T (x + (T : ℝ) * I)‖
            ≤ (1 / x) * (2 * x / T ^ 2) :=
              mul_le_mul hF_le hK_le (norm_nonneg _) (by positivity)
          _ = 2 / T ^ 2 := by field_simp [hx_pos.ne']
      calc ‖∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)‖
          ≤ (2 / T ^ 2) * |T - 0| := hle
        _ = 2 / T := by rw [sub_zero, abs_of_pos hT_pos]; field_simp [hT_pos.ne']
    have b3 : ‖I * (∫ y in (-T)..T, H ((T : ℝ) + y * I))‖ ≤ 6 / T := by
      rw [norm_mul, Complex.norm_I, one_mul]
      have hle : ‖∫ y in (-T)..T, H ((T : ℝ) + y * I)‖ ≤ (3 / T ^ 2) * |T - (-T)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        rw [Set.uIoc_of_le (by linarith)] at hy
        rw [show H ((T : ℝ) + y * I) = F ((T : ℝ) + y * I) * K T ((T : ℝ) + y * I) from rfl, norm_mul]
        have hF_le := norm_G_sub_GN_mul_cpow_le N hN1 (z := (T : ℂ) + y * I) (by simpa using hT_pos)
        have hK_le := norm_K_vert T T y hT_pos (Or.inl rfl) (abs_le.mpr ⟨hy.1.le, hy.2⟩)
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero] at hF_le
        calc ‖F ((T : ℝ) + y * I)‖ * ‖K T ((T : ℝ) + y * I)‖
            ≤ (1 / T) * (3 / T) := mul_le_mul hF_le hK_le (norm_nonneg _) (by positivity)
          _ = 3 / T ^ 2 := by ring
      calc ‖∫ y in (-T)..T, H ((T : ℝ) + y * I)‖
          ≤ (3 / T ^ 2) * |T - (-T)| := hle
        _ = 6 / T := by
            rw [sub_neg_eq_add, show T + T = 2 * T by ring, abs_of_pos (by linarith)]
            field_simp [hT_pos.ne']; ring
    have b4 : ‖∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)‖ ≤ M / Real.log (N : ℝ) := by
      have hcont_g : Continuous (fun x : ℝ => M * (N : ℝ) ^ x) :=
        continuous_const.mul (Continuous.rpow continuous_const continuous_id (fun _ => Or.inl hNpos.ne'))
      calc ‖∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)‖
          ≤ ∫ x in (-del)..(0 : ℝ), M * (N : ℝ) ^ x := by
            refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
              (Eventually.of_forall fun x hx => ?_) (hcont_g.intervalIntegrable (μ := volume) _ _)
            have hx_mem : (x : ℂ) + (-T : ℝ) * I ∈ EbotL := ⟨x, ⟨hx.1.le, hx.2⟩, rfl⟩
            have h1 : ‖G (x + (-T : ℝ) * I) * K T (x + (-T : ℝ) * I)‖ ≤ M :=
              (hM1 _ hx_mem).trans (le_max_left _ _)
            have hre_eq : ((x : ℂ) + (-T : ℝ) * I).re = x := by simp
            calc ‖H1 (x + (-T : ℝ) * I)‖
                = ‖G (x + (-T : ℝ) * I) * K T (x + (-T : ℝ) * I)‖ * ‖(N : ℂ) ^ ((x : ℂ) + (-T : ℝ) * I)‖ := by
                  simp only [H1]; rw [mul_right_comm, norm_mul]
              _ = ‖G (x + (-T : ℝ) * I) * K T (x + (-T : ℝ) * I)‖ * (N : ℝ) ^ x := by
                  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N), hre_eq]
              _ ≤ M * (N : ℝ) ^ x := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hNpos.le x)
        _ = M * ∫ x in (-del)..(0 : ℝ), (N : ℝ) ^ x := intervalIntegral.integral_const_mul _ _
        _ ≤ M * (1 / Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (integral_rpow_neg_delta_zero N hN2 hdel_pos) hM_nn
        _ = M / Real.log (N : ℝ) := by ring
    have b5 : ‖∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)‖ ≤ M / Real.log (N : ℝ) := by
      have hcont_g : Continuous (fun x : ℝ => M * (N : ℝ) ^ x) :=
        continuous_const.mul (Continuous.rpow continuous_const continuous_id (fun _ => Or.inl hNpos.ne'))
      calc ‖∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)‖
          ≤ ∫ x in (-del)..(0 : ℝ), M * (N : ℝ) ^ x := by
            refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
              (Eventually.of_forall fun x hx => ?_) (hcont_g.intervalIntegrable (μ := volume) _ _)
            have hx_mem : (x : ℂ) + (T : ℝ) * I ∈ EtopL := ⟨x, ⟨hx.1.le, hx.2⟩, rfl⟩
            have h1 : ‖G (x + (T : ℝ) * I) * K T (x + (T : ℝ) * I)‖ ≤ M :=
              (hM2 _ hx_mem).trans (le_trans (le_max_left _ _) (le_max_right _ _))
            have hre_eq : ((x : ℂ) + (T : ℝ) * I).re = x := by simp
            calc ‖H1 (x + (T : ℝ) * I)‖
                = ‖G (x + (T : ℝ) * I) * K T (x + (T : ℝ) * I)‖ * ‖(N : ℂ) ^ ((x : ℂ) + (T : ℝ) * I)‖ := by
                  simp only [H1]; rw [mul_right_comm, norm_mul]
              _ = ‖G (x + (T : ℝ) * I) * K T (x + (T : ℝ) * I)‖ * (N : ℝ) ^ x := by
                  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N), hre_eq]
              _ ≤ M * (N : ℝ) ^ x := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hNpos.le x)
        _ = M * ∫ x in (-del)..(0 : ℝ), (N : ℝ) ^ x := intervalIntegral.integral_const_mul _ _
        _ ≤ M * (1 / Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (integral_rpow_neg_delta_zero N hN2 hdel_pos) hM_nn
        _ = M / Real.log (N : ℝ) := by ring
    have b6 : ‖I * (∫ y in (-T)..T, H1 ((-del : ℝ) + y * I))‖ ≤ 2 * T * M * (N : ℝ) ^ (-del) := by
      rw [norm_mul, Complex.norm_I, one_mul]
      have hle : ‖∫ y in (-T)..T, H1 ((-del : ℝ) + y * I)‖ ≤ (M * (N : ℝ) ^ (-del)) * |T - (-T)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        rw [Set.uIoc_of_le (by linarith)] at hy
        have hy_mem : (-del : ℝ) + y * I ∈ EvertL := ⟨y, ⟨hy.1.le, hy.2⟩, rfl⟩
        have h1 : ‖G ((-del : ℝ) + y * I) * K T ((-del : ℝ) + y * I)‖ ≤ M :=
          (hM3 _ hy_mem).trans (le_trans (le_max_right _ _) (le_max_right _ _))
        have hre_eq : ((-del : ℝ) + y * I).re = -del := by simp
        calc ‖H1 ((-del : ℝ) + y * I)‖
            = ‖G ((-del : ℝ) + y * I) * K T ((-del : ℝ) + y * I)‖ * ‖(N : ℂ) ^ ((-del : ℝ) + y * I)‖ := by
              simp only [H1]; rw [mul_right_comm, norm_mul]
          _ = ‖G ((-del : ℝ) + y * I) * K T ((-del : ℝ) + y * I)‖ * (N : ℝ) ^ (-del) := by
              rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N), hre_eq]
          _ ≤ M * (N : ℝ) ^ (-del) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hNpos.le _)
      calc ‖∫ y in (-T)..T, H1 ((-del : ℝ) + y * I)‖
          ≤ (M * (N : ℝ) ^ (-del)) * |T - (-T)| := hle
        _ = 2 * T * M * (N : ℝ) ^ (-del) := by
            rw [sub_neg_eq_add, show T + T = 2 * T by ring, abs_of_pos (by linarith)]; ring
    have b7 : ‖∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)‖ ≤ 2 / T + 2 / (N : ℝ) := by
      have hle : ‖∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)‖ ≤
          (2 / T ^ 2 + 2 / ((N : ℝ) * T)) * |(0 : ℝ) - (-T)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
        rw [Set.uIoc_of_le (by linarith)] at hx
        by_cases hx0 : x = 0
        · subst hx0
          have hK0 : K T (((0 : ℝ) : ℂ) + (-T : ℝ) * I) = 0 := by
            unfold K
            have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT_pos.ne'
            simp only [ofReal_zero, zero_add, ofReal_neg]
            field_simp [hTne, I_ne_zero]
            ring_nf
            simp
          change ‖GN N (((0 : ℝ) : ℂ) + (-T : ℝ) * I) * (N : ℂ) ^ (((0 : ℝ) : ℂ) + (-T : ℝ) * I) *
            K T (((0 : ℝ) : ℂ) + (-T : ℝ) * I)‖ ≤ _
          rw [hK0, mul_zero, norm_zero]
          positivity
        · have hx_neg : x < 0 := lt_of_le_of_ne hx.2 hx0
          have hmx_pos : 0 < -x := neg_pos.mpr hx_neg
          have hGN_le := norm_GN_mul_cpow_le N hN1 (z := (x : ℂ) + (-T : ℝ) * I) (by simpa using hx_neg)
          have hK_le := norm_K_horiz T x hT_pos (-T) (Or.inr rfl)
          rw [abs_of_neg hx_neg] at hK_le
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, add_zero] at hGN_le
          rw [show H2 (x + (-T : ℝ) * I) = (GN N (x + (-T : ℝ) * I) * (N : ℂ) ^ ((x : ℂ) + (-T : ℝ) * I)) *
            K T (x + (-T : ℝ) * I) from rfl, norm_mul]
          calc ‖GN N _ * (N : ℂ) ^ _‖ * ‖K T (x + (-T : ℝ) * I)‖
              ≤ (1 / (-x) + 1 / (N : ℝ)) * (2 * (-x) / T ^ 2) :=
                mul_le_mul hGN_le hK_le (norm_nonneg _) (by positivity)
            _ = 2 / T ^ 2 + 2 * (-x) / ((N : ℝ) * T ^ 2) := by
                field_simp [hmx_pos.ne', hNpos.ne', hT_pos.ne']
                ring
            _ ≤ 2 / T ^ 2 + 2 * T / ((N : ℝ) * T ^ 2) := by
                gcongr; linarith [hx.1]
            _ = 2 / T ^ 2 + 2 / ((N : ℝ) * T) := by
                field_simp [hNpos.ne', hT_pos.ne']
      calc ‖∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)‖
          ≤ (2 / T ^ 2 + 2 / ((N : ℝ) * T)) * |(0 : ℝ) - (-T)| := hle
        _ = 2 / T + 2 / (N : ℝ) := by
            rw [sub_neg_eq_add, zero_add, abs_of_pos hT_pos]
            field_simp [hT_pos.ne', hNpos.ne']
    have b8 : ‖∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I)‖ ≤ 2 / T + 2 / (N : ℝ) := by
      have hle : ‖∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I)‖ ≤
          (2 / T ^ 2 + 2 / ((N : ℝ) * T)) * |(0 : ℝ) - (-T)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
        rw [Set.uIoc_of_le (by linarith)] at hx
        by_cases hx0 : x = 0
        · subst hx0
          have hK0 : K T (((0 : ℝ) : ℂ) + (T : ℝ) * I) = 0 := by
            unfold K
            have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT_pos.ne'
            simp only [ofReal_zero, zero_add]
            field_simp [hTne, I_ne_zero]
            ring_nf
            simp
          change ‖GN N (((0 : ℝ) : ℂ) + (T : ℝ) * I) * (N : ℂ) ^ (((0 : ℝ) : ℂ) + (T : ℝ) * I) *
            K T (((0 : ℝ) : ℂ) + (T : ℝ) * I)‖ ≤ _
          rw [hK0, mul_zero, norm_zero]
          positivity
        · have hx_neg : x < 0 := lt_of_le_of_ne hx.2 hx0
          have hmx_pos : 0 < -x := neg_pos.mpr hx_neg
          have hGN_le := norm_GN_mul_cpow_le N hN1 (z := (x : ℂ) + (T : ℝ) * I) (by simpa using hx_neg)
          have hK_le := norm_K_horiz T x hT_pos T (Or.inl rfl)
          rw [abs_of_neg hx_neg] at hK_le
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, add_zero] at hGN_le
          rw [show H2 (x + (T : ℝ) * I) = (GN N (x + (T : ℝ) * I) * (N : ℂ) ^ ((x : ℂ) + (T : ℝ) * I)) *
            K T (x + (T : ℝ) * I) from rfl, norm_mul]
          calc ‖GN N _ * (N : ℂ) ^ _‖ * ‖K T (x + (T : ℝ) * I)‖
              ≤ (1 / (-x) + 1 / (N : ℝ)) * (2 * (-x) / T ^ 2) :=
                mul_le_mul hGN_le hK_le (norm_nonneg _) (by positivity)
            _ = 2 / T ^ 2 + 2 * (-x) / ((N : ℝ) * T ^ 2) := by
                field_simp [hmx_pos.ne', hNpos.ne', hT_pos.ne']
                ring
            _ ≤ 2 / T ^ 2 + 2 * T / ((N : ℝ) * T ^ 2) := by
                gcongr; linarith [hx.1]
            _ = 2 / T ^ 2 + 2 / ((N : ℝ) * T) := by
                field_simp [hNpos.ne', hT_pos.ne']
      calc ‖∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I)‖
          ≤ (2 / T ^ 2 + 2 / ((N : ℝ) * T)) * |(0 : ℝ) - (-T)| := hle
        _ = 2 / T + 2 / (N : ℝ) := by
            rw [sub_neg_eq_add, zero_add, abs_of_pos hT_pos]
            field_simp [hT_pos.ne', hNpos.ne']
    have b9 : ‖I * (∫ y in (-T)..T, H2 ((-T : ℝ) + y * I))‖ ≤ 6 / T + 6 / (N : ℝ) := by
      rw [norm_mul, Complex.norm_I, one_mul]
      have hle : ‖∫ y in (-T)..T, H2 ((-T : ℝ) + y * I)‖ ≤
          ((1 / T + 1 / (N : ℝ)) * (3 / T)) * |T - (-T)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        rw [Set.uIoc_of_le (by linarith)] at hy
        have hGN_le := norm_GN_mul_cpow_le N hN1 (z := (-T : ℝ) + y * I) (by simp; linarith)
        have hK_le := norm_K_vert T (-T) y hT_pos (Or.inr rfl) (abs_le.mpr ⟨hy.1.le, hy.2⟩)
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, neg_neg] at hGN_le
        rw [show H2 ((-T : ℝ) + y * I) = (GN N ((-T : ℝ) + y * I) * (N : ℂ) ^ ((-T : ℝ) + y * I)) *
          K T ((-T : ℝ) + y * I) from rfl, norm_mul]
        exact mul_le_mul hGN_le hK_le (norm_nonneg _) (by positivity)
      calc ‖∫ y in (-T)..T, H2 ((-T : ℝ) + y * I)‖
          ≤ ((1 / T + 1 / (N : ℝ)) * (3 / T)) * |T - (-T)| := hle
        _ = 6 / T + 6 / (N : ℝ) := by
            rw [sub_neg_eq_add, show T + T = 2 * T by ring, abs_of_pos (by linarith)]
            field_simp [hT_pos.ne', hNpos.ne']; ring
    -- Combine all 9 bounds
    have h2pi_pos : 0 < 2 * Real.pi := by positivity
    have hnorm_lhs : ‖2 * Real.pi * I * (G 0 - GN N 0)‖ = (2 * Real.pi) * ‖G 0 - GN N 0‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    have hnorm_rhs : ‖2 * Real.pi * I * (G 0 - GN N 0)‖ ≤
        20 / T + 10 / (N : ℝ) + 2 * M / Real.log (N : ℝ) + 2 * T * M * (N : ℝ) ^ (-del) := by
      rw [hDecomp]
      have tri := norm_add_le
        ((∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)) - (∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)) +
          I * (∫ y in (-T)..T, H ((T : ℝ) + y * I)) +
         ((∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)) -
          (∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)) -
          I * (∫ y in (-T)..T, H1 ((-del : ℝ) + y * I))))
        (-(∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)) +
          (∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I)) +
          I * (∫ y in (-T)..T, H2 ((-T : ℝ) + y * I)))
      have tA : ‖(∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)) - (∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)) +
          I * (∫ y in (-T)..T, H ((T : ℝ) + y * I))‖ ≤ 10 / T := by
        calc ‖(∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)) - (∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)) +
              I * (∫ y in (-T)..T, H ((T : ℝ) + y * I))‖
            ≤ ‖(∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)) - (∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I))‖ +
              ‖I * (∫ y in (-T)..T, H ((T : ℝ) + y * I))‖ := norm_add_le _ _
          _ ≤ (‖∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)‖ + ‖∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)‖) +
              ‖I * (∫ y in (-T)..T, H ((T : ℝ) + y * I))‖ := add_le_add (norm_sub_le _ _) le_rfl
          _ ≤ 10 / T := by
              have h10T : 2 / T + 2 / T + 6 / T = 10 / T := by ring
              linarith [b1, b2, b3, h10T]
      have tB : ‖(∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)) -
          (∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)) -
          I * (∫ y in (-T)..T, H1 ((-del : ℝ) + y * I))‖ ≤
          2 * M / Real.log (N : ℝ) + 2 * T * M * (N : ℝ) ^ (-del) := by
        calc ‖(∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)) -
              (∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)) -
              I * (∫ y in (-T)..T, H1 ((-del : ℝ) + y * I))‖
            ≤ ‖(∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)) -
              (∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I))‖ +
              ‖I * (∫ y in (-T)..T, H1 ((-del : ℝ) + y * I))‖ := norm_sub_le _ _
          _ ≤ (‖∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)‖ +
              ‖∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)‖) +
              ‖I * (∫ y in (-T)..T, H1 ((-del : ℝ) + y * I))‖ := add_le_add (norm_sub_le _ _) le_rfl
          _ ≤ 2 * M / Real.log (N : ℝ) + 2 * T * M * (N : ℝ) ^ (-del) := by
              have h2M : M / Real.log (N : ℝ) + M / Real.log (N : ℝ) = 2 * M / Real.log (N : ℝ) := by ring
              linarith [b4, b5, b6, h2M]
      have tC : ‖-(∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)) +
          (∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I)) +
          I * (∫ y in (-T)..T, H2 ((-T : ℝ) + y * I))‖ ≤ 10 / T + 10 / (N : ℝ) := by
        have h1 : ‖-(∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)) +
            (∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I))‖ ≤
            ‖∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)‖ +
            ‖∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I)‖ := by
          simpa [norm_neg] using norm_add_le (-(∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)))
            (∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I))
        calc ‖-(∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)) +
              (∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I)) +
              I * (∫ y in (-T)..T, H2 ((-T : ℝ) + y * I))‖
            ≤ ‖-(∫ x in (-T)..(0 : ℝ), H2 (x + (-T : ℝ) * I)) +
              (∫ x in (-T)..(0 : ℝ), H2 (x + (T : ℝ) * I))‖ +
              ‖I * (∫ y in (-T)..T, H2 ((-T : ℝ) + y * I))‖ := norm_add_le _ _
          _ ≤ 10 / T + 10 / (N : ℝ) := by
              have h10T : 2 / T + 2 / T + 6 / T = 10 / T := by ring
              have h10N : 2 / (N : ℝ) + 2 / (N : ℝ) + 6 / (N : ℝ) = 10 / (N : ℝ) := by ring
              linarith [h1, b7, b8, b9, h10T, h10N]
      have tAB : ‖((∫ x in (0 : ℝ)..T, H (x + (-T : ℝ) * I)) - (∫ x in (0 : ℝ)..T, H (x + (T : ℝ) * I)) +
          I * (∫ y in (-T)..T, H ((T : ℝ) + y * I))) +
         ((∫ x in (-del)..(0 : ℝ), H1 (x + (-T : ℝ) * I)) -
          (∫ x in (-del)..(0 : ℝ), H1 (x + (T : ℝ) * I)) -
          I * (∫ y in (-T)..T, H1 ((-del : ℝ) + y * I)))‖ ≤
          10 / T + (2 * M / Real.log (N : ℝ) + 2 * T * M * (N : ℝ) ^ (-del)) :=
        (norm_add_le _ _).trans (add_le_add tA tB)
      have h20 : 10 / T + 10 / T = 20 / T := by ring
      linarith [tri, tAB, tC, h20]
    rw [le_div_iff₀ h2pi_pos, mul_comm]
    linarith [hnorm_lhs, hnorm_rhs]
  -- Now take N large enough
  have htend_tail : Tendsto (fun N : ℕ =>
      (10 / (N : ℝ) + 2 * M / Real.log (N : ℝ) + 2 * T * M * (N : ℝ) ^ (-del)) / (2 * Real.pi))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 10 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => 2 * M / Real.log (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h3 : Tendsto (fun N : ℕ => 2 * T * M * (N : ℝ) ^ (-del)) atTop (𝓝 0) := by
      have hr : Tendsto (fun N : ℕ => (N : ℝ) ^ (-del)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hdel_pos).comp tendsto_natCast_atTop_atTop
      simpa using hr.const_mul (2 * T * M)
    have hsum : Tendsto (fun N : ℕ => 10 / (N : ℝ) + 2 * M / Real.log (N : ℝ) + 2 * T * M * (N : ℝ) ^ (-del))
        atTop (𝓝 (0 + 0 + 0)) := (h1.add h2).add h3
    simpa using hsum.div_const (2 * Real.pi)
  have hT_bound : (20 / T) / (2 * Real.pi) < 2 * ε / 3 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h20 : 20 / T ≤ 2 * ε := by
      rw [div_le_iff₀ hT_pos]
      have h10 : 10 ≤ T * ε := (div_le_iff₀ hε).mp hT_eps
      linarith
    have h2pi : (6 : ℝ) < 2 * Real.pi := by linarith
    have hdiv1 : (20 / T) / (2 * Real.pi) ≤ (2 * ε) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right h20 (by positivity)
    have hdiv2 : (2 * ε) / (2 * Real.pi) < (2 * ε) / 6 :=
      div_lt_div_of_pos_left (by positivity) (by norm_num) h2pi
    linarith
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp htend_tail) (ε / 3) (by linarith)
  refine ⟨max 2 N₀, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hNN0 : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have htail := hN₀ N hNN0
  rw [Real.dist_eq, sub_zero] at htail
  have htail' : (10 / (N : ℝ) + 2 * M / Real.log (N : ℝ) + 2 * T * M * (N : ℝ) ^ (-del)) / (2 * Real.pi) < ε / 3 :=
    lt_of_le_of_lt (le_abs_self _) htail
  have hM' := hMain N hN2
  rw [Complex.dist_eq, norm_sub_rev]
  have hsplit_div : (20 / T + 10 / (N : ℝ) + 2 * M / Real.log (N : ℝ) + 2 * T * M * (N : ℝ) ^ (-del)) / (2 * Real.pi) =
      (20 / T) / (2 * Real.pi) +
      (10 / (N : ℝ) + 2 * M / Real.log (N : ℝ) + 2 * T * M * (N : ℝ) ^ (-del)) / (2 * Real.pi) := by
    ring
  linarith [hM', hsplit_div, hT_bound, htail']

/-! ### Section 6: Kronecker's Lemma and conclusion -/

private lemma abel_sum_kronecker (a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, a n) =
      (N : ℝ) * (∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ)) -
      ∑ k ∈ Finset.range N, (∑ n ∈ Finset.Icc 1 k, a n / (n : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnm : N + 1 ∉ Finset.Icc 1 N := by simp
    rw [hIcc, Finset.sum_insert hnm, Finset.sum_insert hnm, Finset.sum_range_succ, ih]
    have hN1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
    push_cast
    field_simp [hN1]
    ring

lemma one_point_proof :
    Filter.Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ)) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  let S : ℕ → ℝ := fun N => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ) / (n : ℝ)
  have hS : Tendsto S atTop (𝓝 0) := by
    have hre := (Complex.continuous_re.tendsto (G 0)).comp tendsto_GN_zero
    rw [G_zero, zero_re] at hre
    refine hre.congr fun N => ?_
    simp only [Function.comp_apply, GN, Complex.re_sum, S, lamC]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_zero, Complex.cpow_one]
    have : ((ArithmeticFunction.liouville n : ℂ) / (n : ℂ)) =
        (((ArithmeticFunction.liouville n : ℝ) / (n : ℝ) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hces : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, S k) atTop (𝓝 0) :=
    hS.cesaro
  have hdiff : Tendsto (fun N : ℕ => S N - (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, S k) atTop (𝓝 0) := by
    simpa using hS.sub hces
  refine hdiff.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [abel_sum_kronecker (fun n => (ArithmeticFunction.liouville n : ℝ)) N]
  simp only [S]
  field_simp [hN0]

end ChowlaOnePointProof

theorem OMA.solution : type_of% @ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.one_point :=
  ChowlaOnePointProof.one_point_proof
