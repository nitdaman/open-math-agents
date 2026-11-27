import FormalConjectures.ErdosProblems.«1047»
import Mathlib.Analysis.Complex.OpenMapping

/-!
A. W. Goodman's first quartic example, at its exact critical level.
See “On the convexity of the level curves of a polynomial” (1966),
https://doi.org/10.1090/S0002-9939-1966-0188408-3.
-/

open Polynomial Set

private noncomputable def OMA.goodmanP : ℂ[X] :=
  (X ^ 2 + 1) * (X - C 2) ^ 2

private noncomputable def OMA.goodmanCriticalLevel : ℝ :=
  (5 : ℝ) ^ ((3 : ℝ) / 2) / 4

private def OMA.goodmanOpen : Set ℂ :=
  Erdos1047.strictSublevelSet goodmanP goodmanCriticalLevel

private theorem OMA.goodmanP_degree_monic : goodmanP.natDegree = 4 ∧ goodmanP.Monic := by
  have h₁ : (X ^ 2 + 1 : ℂ[X]).Monic := by
    simpa using (monic_X_pow_add_C (1 : ℂ) (n := 2) (by decide))
  have h₂ : ((X - C (2 : ℂ)) ^ 2).Monic := (monic_X_sub_C 2).pow 2
  refine ⟨?_, h₁.mul h₂⟩
  unfold goodmanP
  rw [h₁.natDegree_mul h₂]
  have hq : (X ^ 2 + 1 : ℂ[X]).natDegree = 2 := by
    change (X ^ 2 + C 1 : ℂ[X]).natDegree = 2
    rw [natDegree_add_C, natDegree_X_pow]
  simp [hq]

private theorem OMA.goodman_eval_factor (z : ℂ) :
    goodmanP.eval z = (z - Complex.I) * (z + Complex.I) * (z - 2) ^ 2 := by
  have he : (z - Complex.I) * (z + Complex.I) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  simp [goodmanP, he]

private theorem OMA.goodman_level_pos : 0 < goodmanCriticalLevel := by
  unfold goodmanCriticalLevel
  positivity

private theorem OMA.goodman_level_sq : goodmanCriticalLevel ^ 2 = 125 / 16 := by
  unfold goodmanCriticalLevel
  rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5),
    show ((3 : ℝ) / 2) * (↑(2 : ℕ) : ℝ) = (↑(3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  norm_num

private noncomputable def OMA.goodmanNormSq (x y : ℝ) : ℝ :=
  (x ^ 2 + (y - 1) ^ 2) * (x ^ 2 + (y + 1) ^ 2) * ((x - 2) ^ 2 + y ^ 2) ^ 2

private theorem OMA.goodman_normSq (z : ℂ) :
    ‖goodmanP.eval z‖ ^ 2 = goodmanNormSq z.re z.im := by
  rw [goodman_eval_factor, norm_mul, norm_mul, norm_pow]
  calc
    _ = ‖z - Complex.I‖ ^ 2 * ‖z + Complex.I‖ ^ 2 * (‖z - 2‖ ^ 2) ^ 2 := by ring
    _ = _ := by
      simp [Complex.sq_norm, Complex.normSq_apply, goodmanNormSq]
      ring

private theorem OMA.goodman_open_iff (z : ℂ) :
    z ∈ goodmanOpen ↔ goodmanNormSq z.re z.im < 125 / 16 := by
  change ‖goodmanP.eval z‖ < goodmanCriticalLevel ↔ _
  rw [← goodman_normSq, ← goodman_level_sq]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) goodman_level_pos.le (by decide : (2 : ℕ) ≠ 0)).symm

private theorem OMA.goodman_open_bounded : Bornology.IsBounded goodmanOpen := by
  refine Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) 4) ?_
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra! hn
  have hi := norm_add_le (z - Complex.I) Complex.I
  rw [sub_add_cancel, Complex.norm_I] at hi
  have hj := norm_sub_le (z + Complex.I) Complex.I
  rw [add_sub_cancel_right, Complex.norm_I] at hj
  have hk := norm_add_le (z - 2) (2 : ℂ)
  rw [sub_add_cancel, Complex.norm_ofNat] at hk
  have h₁ : 1 ≤ ‖z - Complex.I‖ := by linarith
  have h₂ : 1 ≤ ‖z + Complex.I‖ := by linarith
  have h₃ : 4 ≤ ‖z - (2 : ℂ)‖ ^ 2 :=
    (show (2 : ℝ) ^ 2 = 4 by norm_num) ▸
      pow_le_pow_left₀ (by norm_num) (show 2 ≤ ‖z - (2 : ℂ)‖ by linarith) 2
  have hprod : 4 ≤ ‖goodmanP.eval z‖ := by
    rw [goodman_eval_factor, norm_mul, norm_mul, norm_pow]
    exact h₃.trans (le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le h₁ h₂))
  have hlevel : goodmanCriticalLevel < 4 := by
    by_contra! h
    have hl := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h 2
    rw [goodman_level_sq] at hl
    norm_num at hl
  exact (not_lt_of_ge hprod) ((show ‖goodmanP.eval z‖ < goodmanCriticalLevel from hz).trans hlevel)

private theorem OMA.goodman_strict_component_root (p : ℂ[X]) (hdeg : 0 < p.natDegree)
    {c : ℝ} (hc : 0 < c) (hbounded : Bornology.IsBounded {z : ℂ | ‖p.eval z‖ < c})
    {z : ℂ} (hz : ‖p.eval z‖ < c) :
    ∃ r ∈ connectedComponentIn {q : ℂ | ‖p.eval q‖ < c} z, p.eval r = 0 := by
  let S := {q : ℂ | ‖p.eval q‖ < c}
  let D := Metric.ball (0 : ℂ) c
  let U := connectedComponentIn S z
  have hzS : z ∈ S := hz
  have hUS : U ⊆ S := connectedComponentIn_subset S z
  have hzU : z ∈ U := mem_connectedComponentIn hzS
  have hU : IsConnected U := isConnected_connectedComponentIn_iff.mpr hzS
  have hD : IsPreconnected D := (convex_ball (0 : ℂ) c).isPreconnected
  have hSopen : IsOpen S := isOpen_lt p.continuous.norm continuous_const
  have hmap : IsOpenMap p.eval := by
    have han : AnalyticOnNhd ℂ p.eval univ := fun v _ => p.differentiable.analyticAt v
    rcases han.is_constant_or_isOpenMap with ⟨w, heq⟩ | hopen
    · have hpconst : p = C w := Polynomial.funext (fun x => by simpa using heq x)
      rw [hpconst, natDegree_C] at hdeg
      omega
    · exact hopen
  have hzD : p.eval z ∈ D := by simpa [D, Metric.mem_ball, dist_zero_right] using hz
  have hpart : closure U ∩ S ⊆ U := by
    have hpre : IsPreconnected (closure U ∩ S) :=
      hU.isPreconnected.subset_closure
        (fun q hq => ⟨subset_closure hq, hUS hq⟩) inter_subset_left
    exact hpre.subset_connectedComponentIn ⟨subset_closure hzU, hzS⟩ inter_subset_right
  have hcl : IsClosed (p.eval '' closure U) :=
    (((hbounded.subset hUS).isCompact_closure).image p.continuous).isClosed
  have hclSub : closure (p.eval '' U) ⊆ p.eval '' closure U :=
    closure_minimal (image_mono subset_closure) hcl
  have hsurj := hD.subset_of_closure_inter_subset (hmap _ hSopen.connectedComponentIn)
    ⟨p.eval z, hzD, ⟨z, hzU, rfl⟩⟩ (by
      intro w hw
      obtain ⟨q, hq, rfl⟩ := hclSub hw.1
      have hqS : q ∈ S := by
        simpa [S, D, Metric.mem_ball, dist_zero_right] using hw.2
      exact ⟨q, hpart ⟨hq, hqS⟩, rfl⟩)
  exact hsurj (Metric.mem_ball_self hc)

private theorem OMA.goodman_fixed_barriers (z : ℂ) (hz : z ∈ goodmanOpen) :
    z.re ≠ 1 / 2 ∧ (z.re < 1 / 2 → z.im ≠ 0) := by
  have h := (goodman_open_iff z).1 hz
  refine ⟨?_, ?_⟩
  · intro hx
    rw [hx] at h
    let v := z.im ^ 2
    have hv : 0 ≤ v := sq_nonneg _
    have he : goodmanNormSq (1 / 2) z.im =
        125 / 16 + (v - 1 / 4) ^ 2 * (v ^ 2 + (7 / 2) * v + 25 / 16) := by
      dsimp [goodmanNormSq, v]
      ring
    rw [he] at h
    have hp : 0 ≤ v ^ 2 + (7 / 2) * v + 25 / 16 := by positivity
    linarith [mul_nonneg (sq_nonneg (v - 1 / 4)) hp]
  · intro hx hy
    rw [hy] at h
    let t := 1 / 2 - z.re
    have ht : 0 ≤ t := sub_nonneg.mpr hx.le
    have he : goodmanNormSq z.re 0 =
        (45 / 16 + (3 / 2) * t + (1 / 2) * t ^ 2 + 2 * t ^ 3 + t ^ 4) ^ 2 := by
      dsimp [goodmanNormSq, t]
      ring
    rw [he] at h
    have hp : 45 / 16 ≤ 45 / 16 + (3 / 2) * t + (1 / 2) * t ^ 2 + 2 * t ^ 3 + t ^ 4 := by
      linarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 45 / 16) hp 2
    norm_num at hsq
    linarith

private noncomputable def OMA.goodmanFixedZone (z : ℂ) : Fin 3 :=
  if z.re < 1 / 2 then
    if z.im < 0 then 0 else 1
  else 2

private theorem OMA.goodman_fixed_zone_constant {U : Set ℂ} (hU : IsPreconnected U)
    (hsub : U ⊆ goodmanOpen) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    goodmanFixedZone z = goodmanFixedZone w := by
  have hre := Complex.continuous_re.continuousOn (s := U)
  have hne (v : ℂ) (hv : v ∈ U) : v.re ≠ 1 / 2 := (goodman_fixed_barriers v (hsub hv)).1
  have hl : z.re < 1 / 2 ↔ w.re < 1 / 2 :=
    ⟨fun h => hU.gt_of_ne hre hne ⟨z, hz, h⟩ hw,
      fun h => hU.gt_of_ne hre hne ⟨w, hw, h⟩ hz⟩
  by_cases hleft : z.re < 1 / 2
  · have him := Complex.continuous_im.continuousOn (s := U)
    have hneIm (v : ℂ) (hv : v ∈ U) : v.im ≠ 0 :=
      (goodman_fixed_barriers v (hsub hv)).2 (hU.gt_of_ne hre hne ⟨z, hz, hleft⟩ hv)
    have hi : z.im < 0 ↔ w.im < 0 :=
      ⟨fun h => hU.gt_of_ne him hneIm ⟨z, hz, h⟩ hw,
        fun h => hU.gt_of_ne him hneIm ⟨w, hw, h⟩ hz⟩
    simp only [goodmanFixedZone, if_pos hleft, if_pos (hl.mp hleft), hi]
  · simp only [goodmanFixedZone, if_neg hleft, if_neg (mt hl.mpr hleft)]

private noncomputable def OMA.goodmanFixedRoots : Fin 3 → ℂ :=
  ![-Complex.I, Complex.I, 2]

private theorem OMA.goodman_fixed_root_mem (i : Fin 3) :
    goodmanFixedRoots i ∈ goodmanOpen := by
  change ‖goodmanP.eval (goodmanFixedRoots i)‖ < goodmanCriticalLevel
  have hz : goodmanP.eval (goodmanFixedRoots i) = 0 := by
    fin_cases i <;> simp [goodmanFixedRoots, goodman_eval_factor]
  simpa [hz] using goodman_level_pos

private theorem OMA.goodman_fixed_root_zone (i : Fin 3) :
    goodmanFixedZone (goodmanFixedRoots i) = i := by
  fin_cases i <;> apply Fin.ext <;> norm_num [goodmanFixedRoots, goodmanFixedZone,
    show (2 : ℂ).re = 2 from rfl]

private theorem OMA.goodman_fixed_roots_exhaust {r : ℂ} (hr : goodmanP.eval r = 0) :
    r ∈ Set.range goodmanFixedRoots := by
  rw [goodman_eval_factor] at hr
  rcases mul_eq_zero.mp hr with h|h
  · rcases mul_eq_zero.mp h with h|h
    · exact ⟨1, (sub_eq_zero.mp h).symm⟩
    · have he : r = -Complex.I := eq_neg_of_add_eq_zero_left h
      exact ⟨0, he.symm⟩
  · have he : r - 2 = 0 := by
      have hm : (r - 2) * (r - 2) = 0 := by simpa only [pow_two] using h
      exact (mul_eq_zero.mp hm).elim id id
    exact ⟨2, (sub_eq_zero.mp he).symm⟩

theorem OMA.solution : type_of% @Erdos1047.erdos_1047.variants.goodman := by
  classical
  change (Erdos1047.componentsIn goodmanOpen).ncard = 3 ∧
    ∃ t ∈ Erdos1047.componentsIn goodmanOpen, ¬ Convex ℝ t
  let W := Erdos1047.componentsIn goodmanOpen
  let F (i : Fin 3) := connectedComponentIn goodmanOpen (goodmanFixedRoots i)
  have hdeg := goodmanP_degree_monic.1
  have hroot (z : ℂ) (hz : z ∈ goodmanOpen) : ∃ r ∈ connectedComponentIn goodmanOpen z,
      goodmanP.eval r = 0 :=
    goodman_strict_component_root goodmanP (by omega)
      goodman_level_pos goodman_open_bounded hz
  have heq : W = Set.range F := by
    ext t
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, hzero⟩ := hroot z hz
      obtain ⟨i, hi⟩ := goodman_fixed_roots_exhaust hzero
      refine ⟨i, ?_⟩
      change connectedComponentIn goodmanOpen (goodmanFixedRoots i) = _
      rw [hi]
      exact (connectedComponentIn_eq hr).symm
    · rintro ⟨i, rfl⟩
      exact ⟨goodmanFixedRoots i, goodman_fixed_root_mem i, rfl⟩
  have hinj : Function.Injective F := by
    intro i j hij
    have hi : goodmanFixedRoots i ∈ F i := mem_connectedComponentIn (goodman_fixed_root_mem i)
    have hj : goodmanFixedRoots j ∈ F i := hij ▸ mem_connectedComponentIn (goodman_fixed_root_mem j)
    have hconst := goodman_fixed_zone_constant
      ((isConnected_connectedComponentIn_iff.mpr (goodman_fixed_root_mem i)).isPreconnected)
      (connectedComponentIn_subset _ _) hi hj
    simpa only [goodman_fixed_root_zone] using hconst
  have hcard : W.ncard = 3 := by
    rw [heq, Set.ncard_range_of_injective hinj]
    simp
  have hright (w : ℂ) (hw : w ∈ goodmanOpen) (hi : goodmanFixedZone w = 2) : w ∈ F 2 := by
    obtain ⟨i, hFi⟩ : connectedComponentIn goodmanOpen w ∈ Set.range F := by
      rw [← heq]
      exact ⟨w, hw, rfl⟩
    have hwF : w ∈ F i := hFi ▸ mem_connectedComponentIn hw
    have hri : goodmanFixedRoots i ∈ F i := mem_connectedComponentIn (goodman_fixed_root_mem i)
    have hconst := goodman_fixed_zone_constant
      ((isConnected_connectedComponentIn_iff.mpr (goodman_fixed_root_mem i)).isPreconnected)
      (connectedComponentIn_subset _ _) hri hwF
    rw [goodman_fixed_root_zone, hi] at hconst
    simpa [hconst] using hwF
  refine ⟨hcard, F 2, ?_, ?_⟩
  · show F 2 ∈ W
    rw [heq]
    exact ⟨2, rfl⟩
  · intro hconvex
    let wLower : ℂ := ⟨51 / 100, -1 / 2⟩
    let wUpper : ℂ := ⟨51 / 100, 1 / 2⟩
    have hLower : wLower ∈ F 2 :=
      hright wLower (by rw [goodman_open_iff]; norm_num [wLower, goodmanNormSq])
        (by norm_num [wLower, goodmanFixedZone])
    have hUpper : wUpper ∈ F 2 :=
      hright wUpper (by rw [goodman_open_iff]; norm_num [wUpper, goodmanNormSq])
        (by norm_num [wUpper, goodmanFixedZone])
    have hmid := hconvex hLower hUpper (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hmidS := connectedComponentIn_subset goodmanOpen (goodmanFixedRoots 2) hmid
    have hmidEq : (1 / 2 : ℝ) • wLower + (1 / 2 : ℝ) • wUpper = (⟨51 / 100, 0⟩ : ℂ) := by
      apply Complex.ext <;> norm_num [wLower, wUpper, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im]
    rw [hmidEq, goodman_open_iff] at hmidS
    norm_num [goodmanNormSq] at hmidS