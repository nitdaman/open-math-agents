import FormalConjectures.ErdosProblems.«1047»
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
The referee's lemniscate example reported by A. W. Goodman in On the convexity
of the level curves of a polynomial, p. 361.
-/

namespace OMA.Erdos1047Referee

open Set Metric Polynomial

noncomputable def curvePolynomial : ℂ[X] := X * (X ^ 5 - 1)

theorem eval_curvePolynomial (z : ℂ) : curvePolynomial.eval z = z * (z ^ 5 - 1) := by
  simp [curvePolynomial]

theorem norm_eval (z : ℂ) : ‖curvePolynomial.eval z‖ = ‖z‖ * ‖z ^ 5 - 1‖ := by
  rw [eval_curvePolynomial, norm_mul]

noncomputable def radius : ℝ := (6 : ℝ) ^ (-(1 : ℝ) / 5)

theorem radius_pos : 0 < radius := Real.rpow_pos_of_pos (by norm_num) _

theorem radius_pow : radius ^ 5 = (1 : ℝ) / 6 := by
  unfold radius
  rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (6 : ℝ))]
  norm_num [Real.rpow_neg_one]

theorem radius_lt_one : radius < 1 := by
  by_contra! h
  have hp := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) h 5
  norm_num [radius_pow] at hp

theorem threshold_eq : 5 * (6 : ℝ) ^ (-(6 : ℝ) / 5) = 5 * radius / 6 := by
  rw [show -(6 : ℝ) / 5 = -(1 : ℝ) / 5 + (-1) by norm_num,
    Real.rpow_add (by norm_num : 0 < (6 : ℝ)), Real.rpow_neg_one]
  unfold radius
  ring

def region : Set ℂ := {z | ‖curvePolynomial.eval z‖ < 5 * radius / 6}

theorem continuous_eval : Continuous curvePolynomial.eval := by
  simp_rw [eval_curvePolynomial]
  fun_prop

theorem region_open : IsOpen region :=
  isOpen_lt continuous_eval.norm continuous_const

theorem norm_sub_lower (z : ℂ) : 1 - ‖z‖ ^ 5 ≤ ‖z ^ 5 - 1‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (z ^ 5)
  rw [norm_sub_rev (1 : ℂ) (z ^ 5)] at h
  simpa only [norm_one, norm_pow] using h

theorem avoids_radius {z : ℂ} (hz : z ∈ region) : ‖z‖ ≠ radius := by
  intro he
  have h := norm_sub_lower z
  rw [he, radius_pow] at h
  change ‖curvePolynomial.eval z‖ < 5 * radius / 6 at hz
  rw [norm_eval, he] at hz
  have hmul := mul_le_mul_of_nonneg_left h radius_pos.le
  linarith

theorem region_subset_ball : region ⊆ closedBall (0 : ℂ) 2 := by
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  by_contra! h
  have hp := pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℝ)) h.le 5
  have hb : ‖z‖ ^ 5 - 1 ≤ ‖z ^ 5 - 1‖ := by
    simpa only [Complex.norm_pow, norm_one] using norm_sub_norm_le (z ^ (5 : ℕ)) (1 : ℂ)
  have h₁ : (1 : ℝ) ≤ ‖z ^ 5 - 1‖ := by norm_num at hp; linarith
  have h₂ : (1 : ℝ) ≤ ‖z‖ := by linarith
  have hlower : (1 : ℝ) ≤ ‖z‖ * ‖z ^ 5 - 1‖ := by
    simpa only [one_mul] using mul_le_mul h₂ h₁ zero_le_one (norm_nonneg z)
  change ‖curvePolynomial.eval z‖ < 5 * radius / 6 at hz
  rw [norm_eval] at hz
  linarith [radius_lt_one]

theorem eval_open_map : IsOpenMap curvePolynomial.eval := by
  obtain ⟨c, hc⟩ | hopen :=
    (AnalyticOnNhd.eval_polynomial curvePolynomial).is_constant_or_isOpenMap
  · have h := (hc 0).trans (hc 2).symm
    norm_num [eval_curvePolynomial] at h
  · exact hopen

-- The minimum of the modulus on the closure of a component lies in the open
-- sublevel. The open mapping theorem forces this minimum to be zero.
theorem component_has_root {z : ℂ} (hz : z ∈ region) :
    ∃ w ∈ connectedComponentIn region z, curvePolynomial.eval w = 0 := by
  let T := connectedComponentIn region z
  have hzT : z ∈ T := mem_connectedComponentIn hz
  have hTS : T ⊆ region := connectedComponentIn_subset _ _
  have hT : IsPreconnected T := isPreconnected_connectedComponentIn
  have hcompact : IsCompact (closure T) := (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset
    isClosed_closure (closure_minimal (hTS.trans region_subset_ball) isClosed_closedBall)
  obtain ⟨w, hwc, hwmin⟩ :=
    hcompact.exists_isMinOn ⟨z, subset_closure hzT⟩ continuous_eval.norm.continuousOn
  have hwS : w ∈ region := by
    change ‖curvePolynomial.eval w‖ < 5 * radius / 6
    exact lt_of_le_of_lt (hwmin (subset_closure hzT)) hz
  have hpre : IsPreconnected (closure T ∩ region) :=
    hT.subset_closure (fun _ ht => ⟨subset_closure ht, hTS ht⟩) inter_subset_left
  have hwT : w ∈ T := hpre.subset_connectedComponentIn
    ⟨subset_closure hzT, hz⟩ inter_subset_right ⟨hwc, hwS⟩
  refine ⟨w, hwT, ?_⟩
  by_contra hn
  have hpos : 0 < ‖curvePolynomial.eval w‖ := norm_pos_iff.mpr hn
  have hin : curvePolynomial.eval w ∈ closure (ball (0 : ℂ) ‖curvePolynomial.eval w‖) := by
    rw [closure_ball _ hpos.ne']
    simp [mem_closedBall, dist_zero_right]
  obtain ⟨_, ⟨v, hv, rfl⟩, hvball⟩ := _root_.mem_closure_iff.mp hin _
    (eval_open_map _ region_open.connectedComponentIn) ⟨w, hwT, rfl⟩
  rw [mem_ball, dist_zero_right] at hvball
  exact (not_lt_of_ge (hwmin (subset_closure hv))) hvball

theorem same_side {z w : ℂ} (hw : w ∈ connectedComponentIn region z) :
    ‖w‖ < radius ↔ ‖z‖ < radius := by
  let T := connectedComponentIn region z
  have hz : z ∈ T :=
    mem_connectedComponentIn (connectedComponentIn_nonempty_iff.mp ⟨w, hw⟩)
  have ht : OrdConnected ((fun x : ℂ => ‖x‖) '' T) :=
    (isPreconnected_connectedComponentIn.image _ continuous_norm.continuousOn).ordConnected
  have hside {a b : ℂ} (ha : a ∈ T) (hb : b ∈ T) (ha' : ‖a‖ < radius) :
      ‖b‖ < radius := by
    by_contra! hb'
    have hr := ht.out (mem_image_of_mem _ ha) (mem_image_of_mem _ hb) ⟨ha'.le, hb'⟩
    obtain ⟨x, hx, hxr⟩ := hr
    exact avoids_radius (connectedComponentIn_subset _ _ hx) hxr
  exact ⟨hside hw hz, hside hz hw⟩

def fifthRoots : Set ℂ := {z | z ^ 5 = 1}

theorem fifthRoots_eq : fifthRoots = (nthRootsFinset 5 (1 : ℂ) : Set ℂ) := by
  ext z
  exact (mem_nthRootsFinset (by norm_num : 0 < (5 : ℕ)) (1 : ℂ)).symm

theorem fifthRoots_finite : fifthRoots.Finite := by
  rw [fifthRoots_eq]
  exact Finset.finite_toSet _

theorem fifthRoots_card : fifthRoots.ncard = 5 := by
  rw [fifthRoots_eq, ncard_coe_finset]
  exact (Complex.isPrimitiveRoot_exp 5 (by norm_num)).card_nthRootsFinset

theorem norm_of_fifthRoot {z : ℂ} (hz : z ^ 5 = 1) : ‖z‖ = 1 := by
  apply (pow_left_inj₀ (norm_nonneg z) (by norm_num : 0 ≤ (1 : ℝ))
    (by norm_num : (5 : ℕ) ≠ 0)).mp
  simpa only [norm_pow, norm_one, one_pow] using congrArg norm hz

noncomputable def fifthRoot (z : ℂ) : ℂ := z ^ ((5 : ℂ)⁻¹)

theorem fifthRoot_pow (z : ℂ) : (fifthRoot z) ^ 5 = z := by
  simp [fifthRoot]

noncomputable def direction (z : ℂ) : ℂ := z / fifthRoot (z ^ 5)

theorem outer_slitPlane {z : ℂ} (hz : z ∈ region) (hr : radius < ‖z‖) :
    z ^ 5 ∈ Complex.slitPlane := by
  have hd : ‖z ^ 5 - 1‖ < (5 : ℝ) / 6 := by
    change ‖curvePolynomial.eval z‖ < 5 * radius / 6 at hz
    rw [norm_eval] at hz
    by_contra! h
    have hl := mul_le_mul hr.le h (by norm_num : 0 ≤ (5 : ℝ) / 6) (norm_nonneg z)
    linarith
  have h := Complex.mem_slitPlane_of_norm_lt_one (hd.trans (by norm_num))
  rwa [show 1 + (z ^ 5 - 1) = z ^ 5 by ring] at h

-- On the outside of the separating circle, division by the principal
-- fifth root of z^5 continuously labels points by fifth roots of unity.
theorem same_outer_root {z w : ℂ} (hz : z ^ 5 = 1) (hw : w ^ 5 = 1)
    (hwT : w ∈ connectedComponentIn region z) : z = w := by
  let T := connectedComponentIn region z
  have hzS : z ∈ region := connectedComponentIn_nonempty_iff.mp ⟨w, hwT⟩
  have hzT : z ∈ T := mem_connectedComponentIn hzS
  have hslit (v : ℂ) (hv : v ∈ T) : v ^ 5 ∈ Complex.slitPlane := by
    have hvS := connectedComponentIn_subset region z hv
    have hv' : radius < ‖v‖ := by
      refine lt_of_le_of_ne (le_of_not_gt ?_) (avoids_radius hvS).symm
      intro hvlt
      have hzlt := (same_side hv).mp hvlt
      rw [norm_of_fifthRoot hz] at hzlt
      exact (not_lt_of_ge radius_lt_one.le) hzlt
    exact outer_slitPlane hvS hv'
  have hne (v : ℂ) (hv : v ∈ T) : fifthRoot (v ^ 5) ≠ 0 := by
    intro he
    have h := fifthRoot_pow (v ^ 5)
    simp only [he, zero_pow (by decide : (5 : ℕ) ≠ 0)] at h
    exact Complex.slitPlane_ne_zero (hslit v hv) h.symm
  have hcont_aux : ContinuousOn (fun v : ℂ => fifthRoot (v ^ 5)) T := by
    intro v hv
    have hroot : ContinuousAt fifthRoot (v ^ 5) := continuousAt_cpow_const (hslit v hv)
    have hpower : ContinuousAt (fun x : ℂ => x ^ (5 : ℕ)) v := by fun_prop
    exact (hroot.comp' (f := fun x : ℂ => x ^ (5 : ℕ)) (x := v) hpower).continuousWithinAt
  have hcont : ContinuousOn direction T := continuous_id.continuousOn.div hcont_aux hne
  have hpre : IsPreconnected (direction '' T) := isPreconnected_connectedComponentIn.image _ hcont
  have hsub : direction '' T ⊆ fifthRoots := by
    rintro _ ⟨v, hv, rfl⟩
    change (v / fifthRoot (v ^ 5)) ^ 5 = 1
    rw [div_pow, fifthRoot_pow]
    exact div_self (Complex.slitPlane_ne_zero (hslit v hv))
  have hs : (direction '' T).Subsingleton := by
    intro a ha b hb
    by_contra! hab
    exact (fifthRoots_finite.subset hsub).not_infinite
      (hpre.infinite_of_nontrivial ⟨a, ha, b, hb, hab⟩)
  simpa [direction, fifthRoot, hz, hw] using hs
    (mem_image_of_mem direction hzT) (mem_image_of_mem direction hwT)

theorem root_region {z : ℂ} (hz : z ∈ insert 0 fifthRoots) : z ∈ region := by
  have h : curvePolynomial.eval z = 0 := by
    rcases mem_insert_iff.mp hz with rfl | hz
    · simp [eval_curvePolynomial]
    · change z ^ 5 = 1 at hz
      simp [eval_curvePolynomial, hz]
  change ‖curvePolynomial.eval z‖ < 5 * radius / 6
  rw [h, norm_zero]
  linarith [radius_pos]

theorem component_injective : InjOn (connectedComponentIn region) (insert 0 fifthRoots) := by
  intro z hz w hw he
  have hwT : w ∈ connectedComponentIn region z := he ▸ mem_connectedComponentIn (root_region hw)
  have hside := same_side hwT
  rcases mem_insert_iff.mp hz with rfl | hz
  · rcases mem_insert_iff.mp hw with rfl | hw
    · rfl
    · have h := hside.mpr (by simpa using radius_pos)
      rw [norm_of_fifthRoot hw] at h
      linarith [radius_lt_one]
  · rcases mem_insert_iff.mp hw with rfl | hw
    · have h := hside.mp (by simpa using radius_pos)
      rw [norm_of_fifthRoot hz] at h
      linarith [radius_lt_one]
    · exact same_outer_root hz hw hwT

theorem component_card : (Erdos1047.componentsIn region).ncard = 6 := by
  have himage : Erdos1047.componentsIn region = connectedComponentIn region '' insert 0 fifthRoots := by
    ext T
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hp⟩ := component_has_root hz
      have hroot : w ∈ insert 0 fifthRoots := by
        rw [eval_curvePolynomial, mul_eq_zero, sub_eq_zero] at hp
        exact mem_insert_iff.mpr hp
      exact ⟨w, hroot, (connectedComponentIn_eq hw).symm⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, root_region hw, rfl⟩
  rw [himage, component_injective.ncard_image,
    ncard_insert_of_notMem (by simp [fifthRoots]) fifthRoots_finite, fifthRoots_card]

theorem radial_mono : StrictMonoOn (fun t : ℝ => t - t ^ 6) (Icc 0 radius) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (by fun_prop) ?_
  intro t ht
  rw [interior_Icc] at ht
  have hderiv : HasDerivAt (fun x : ℝ => x - x ^ 6) (1 - 6 * t ^ 5) t := by
    have hid : HasDerivAt (fun x : ℝ => x) (1 : ℝ) t := hasDerivAt_id t
    simpa using hid.fun_sub (hid.fun_pow 6)
  rw [hderiv.deriv]
  have hp := pow_lt_pow_left₀ ht.2 ht.1.le (by norm_num : (5 : ℕ) ≠ 0)
  rw [radius_pow] at hp
  linarith

theorem radial_mem_component {ζ : ℂ} (hζ : ζ ^ 5 = 1) {a : ℝ} (ha : 0 ≤ a)
    (har : a < radius) : (a : ℂ) * ζ ∈ connectedComponentIn region 0 := by
  let ray : ℝ → ℂ := fun t => (t : ℂ) * ζ
  have hzero : (0 : ℂ) ∈ ray '' Icc 0 a := ⟨0, ⟨le_rfl, ha⟩, by simp [ray]⟩
  have hpre : IsPreconnected (ray '' Icc 0 a) :=
    (isPreconnected_Icc.image ray (by unfold ray; fun_prop))
  have hsub : ray '' Icc 0 a ⊆ region := by
    rintro _ ⟨t, ht, rfl⟩
    have htr : t < radius := ht.2.trans_lt har
    have htp : t ^ 5 ≤ (1 : ℝ) := by
      simpa using pow_le_pow_left₀ ht.1 (htr.trans radius_lt_one).le 5
    have hh := radial_mono (show t ∈ Icc 0 radius from ⟨ht.1, htr.le⟩)
      (show radius ∈ Icc 0 radius from ⟨radius_pos.le, le_rfl⟩) htr
    change ‖curvePolynomial.eval ((t : ℂ) * ζ)‖ < 5 * radius / 6
    rw [norm_eval, norm_mul, norm_of_fifthRoot hζ, mul_one, mul_pow, hζ, mul_one]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg ht.1, abs_of_nonpos (sub_nonpos.mpr htp)]
    have hrp : radius ^ 6 = radius / 6 := by rw [pow_succ, radius_pow]; ring
    change t - t ^ 6 < radius - radius ^ 6 at hh
    rw [hrp] at hh
    nlinarith only [hh]
  exact hpre.subset_connectedComponentIn hzero hsub ⟨a, ⟨ha, le_rfl⟩, rfl⟩

theorem norm_eval_neg_real {b : ℝ} (hb : 0 ≤ b) :
    ‖curvePolynomial.eval ((-b : ℝ) : ℂ)‖ = b * (b ^ 5 + 1) := by
  rw [norm_eval]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_neg, abs_of_nonneg hb, show (-b)^5 - 1 = -(b^5 + 1) by ring,
    abs_neg, abs_of_nonneg (by positivity : 0 ≤ b ^ 5 + 1)]

-- Two points of radius 199/200 of the separating radius on the adjacent
-- fifth-root rays about the negative real axis have a midpoint outside.
theorem component_zero_nonconvex : ¬ Convex ℝ (connectedComponentIn region 0) := by
  let ζ : ℂ := Complex.exp ((↑(4 * Real.pi / 5 : ℝ) : ℂ) * Complex.I)
  have hζ : ζ ^ 5 = 1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_nat_mul_two_pi_mul_I 2 using 2
    push_cast
    ring
  let η : ℂ := (starRingEnd ℂ) ζ
  have hη : η ^ 5 = 1 := by
    change ((starRingEnd ℂ) ζ) ^ 5 = 1
    rw [← map_pow, hζ, map_one]
  let c := Real.cos (Real.pi / 5)
  have hrec : ζ.re = -c := by
    dsimp [ζ,c]
    rw [Complex.exp_ofReal_mul_I_re, show 4 * Real.pi / 5 = Real.pi - Real.pi / 5 by ring,
      Real.cos_pi_sub]
  have hc : (4 : ℝ) / 5 < c := by
    dsimp [c]
    rw [Real.cos_pi_div_five]
    have hn : (11 : ℝ) / 5 < Real.sqrt 5 := by
      have hs := Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))
      have hs0 := Real.sqrt_nonneg 5
      by_contra! h
      have hp := pow_le_pow_left₀ hs0 h 2
      rw [hs] at hp
      norm_num at hp
    linarith
  let a := radius * (199 / 200)
  let k := (199 / 200) * c
  have ha : 0 ≤ a := mul_nonneg radius_pos.le (by norm_num)
  have har : a < radius := by dsimp [a]; nlinarith [radius_pos]
  have hx := radial_mem_component hζ ha har
  have hy := radial_mem_component hη ha har
  have hk : (199 : ℝ) / 250 < k := by dsimp [k]; linarith
  have hk0 : 0 ≤ k := by linarith
  have hk6 : ((199 : ℝ) / 250) ^ 6 ≤ k ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hk.le 6
  have htest : (5 : ℝ) / 6 < (199 / 250 : ℝ) + (199 / 250 : ℝ) ^ 6 / 6 := by norm_num
  have hbound : (5 : ℝ) / 6 < k * ((1 / 6) * k ^ 5 + 1) :=
    by nlinarith only [htest, hk, hk6]
  intro hconv
  have hmid := hconv hx hy (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmean : (1 / 2 : ℝ) • ((a : ℂ) * ζ) + (1 / 2 : ℝ) • ((a : ℂ) * η) =
      ((-(radius * k) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [η, Complex.mul_re, hrec, a, k]
      ring
    · simp [η, Complex.mul_im]
  rw [hmean] at hmid
  have hmem := connectedComponentIn_subset region 0 hmid
  change ‖curvePolynomial.eval ((-(radius * k) : ℝ) : ℂ)‖ < 5 * radius / 6 at hmem
  rw [norm_eval_neg_real (mul_nonneg radius_pos.le hk0), mul_pow, radius_pow] at hmem
  have hh := mul_lt_mul_of_pos_left hbound radius_pos
  nlinarith only [hh, hmem]

end OMA.Erdos1047Referee

theorem OMA.solution : type_of% @Erdos1047.erdos_1047.variants.referee := by
  open OMA.Erdos1047Referee in
    rw [threshold_eq]
    change (Erdos1047.componentsIn region).ncard = 6 ∧
      ∃ t ∈ Erdos1047.componentsIn region, ¬ Convex ℝ t
    exact ⟨component_card, connectedComponentIn region 0, ⟨0, root_region (by simp), rfl⟩,
      component_zero_nonconvex⟩
