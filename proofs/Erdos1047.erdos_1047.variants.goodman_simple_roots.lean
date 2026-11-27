import FormalConjectures.ErdosProblems.«1047»
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
We use A. W. Goodman's quartic, normalized to be monic, with a level slightly below
his critical level so that the four components remain separated even at their boundaries.
Goodman, “On the convexity of the level curves of a polynomial” (1966),
https://doi.org/10.1090/S0002-9939-1966-0188408-3.
-/

open scoped BigOperators
open Set Polynomial

private theorem OMA.goodman_prod_index {R M : Type*} [CommMonoid M] (s : Multiset R)
    (g : R → M) : (s.map g).prod = ∏ i : Fin s.toList.length, g (s.toList.get i) := by
  rw [← List.prod_ofFn]
  change _ = (List.ofFn (g ∘ s.toList.get)).prod
  rw [← List.map_ofFn, List.ofFn_get]
  simp

private theorem OMA.goodman_sublevel_compact (p : ℂ[X]) (hp : p.Monic)
    (hdeg : 0 < p.natDegree) (c : ℝ) (hc : 0 ≤ c) :
    IsCompact {z : ℂ | ‖p.eval z‖ ≤ c} := by
  classical
  have hclosed : IsClosed {z : ℂ | ‖p.eval z‖ ≤ c} := isClosed_le p.continuous.norm continuous_const
  have hfin : (p.rootSet ℂ).Finite := p.rootSet_finite _
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hfin.isBounded
  have hroot (r : ℂ) (hr : r ∈ p.roots) : ‖r‖ < R := by
    have he : p.eval r = 0 := (mem_roots hp.ne_zero).1 hr
    have hrC : r ∈ p.rootSet ℂ := hp.mem_rootSet.mpr (by simpa using he)
    simpa [Metric.mem_ball, dist_zero_right] using hR hrC
  refine Metric.isCompact_of_isClosed_isBounded hclosed
    (Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) (R + c + 1)) ?_)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra! h
  have hbound (i : Fin p.roots.toList.length) : c + 1 ≤ ‖z - p.roots.toList.get i‖ := by
    have hr := hroot (p.roots.toList.get i) (Multiset.mem_toList.mp (List.get_mem _ i))
    have ht := norm_add_le (z - p.roots.toList.get i) (p.roots.toList.get i)
    rw [sub_add_cancel] at ht
    linarith
  have hL : p.roots.toList.length = p.natDegree := by
    simpa using (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hprod : (c + 1) ^ p.natDegree ≤ ‖p.eval z‖ := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp, goodman_prod_index, norm_prod]
    have hprod : (∏ _ : Fin p.roots.toList.length, (c + 1)) ≤
        ∏ i, ‖z - p.roots.toList.get i‖ :=
      Finset.prod_le_prod (s := Finset.univ) (fun _ _ => by positivity) (fun i _ => hbound i)
    simpa [hL] using hprod
  have hpow : c + 1 ≤ (c + 1) ^ p.natDegree := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ c + 1 by linarith) (by omega : 1 ≤ p.natDegree)
  change ‖p.eval z‖ ≤ c at hz
  linarith [hpow.trans hprod]

private theorem OMA.goodman_component_has_root (p : ℂ[X]) (hdeg : 0 < p.natDegree)
    (c : ℝ) {S : Set ℂ} (hS : S = {z : ℂ | ‖p.eval z‖ ≤ c}) (hcompact : IsCompact S)
    {z : ℂ} (hz : z ∈ S) : ∃ r ∈ connectedComponentIn S z, p.eval r = 0 := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  let x : S := ⟨z, hz⟩
  let F : S → ℂ := fun y => p.eval y.1
  let Z := F ⁻¹' {0}
  have hF : Continuous F := p.continuous.comp continuous_subtype_val
  have hmap : IsOpenMap p.eval := by
    have han : AnalyticOnNhd ℂ p.eval univ := fun w _ => p.differentiable.analyticAt w
    rcases han.is_constant_or_isOpenMap with ⟨w, heq⟩ | hopen
    · have hpconst : p = C w := Polynomial.funext (fun v => by simpa using heq v)
      rw [hpconst, natDegree_C] at hdeg
      omega
    · exact hopen
  -- Every clopen neighborhood in the compact sublevel set has a point of minimum modulus.
  -- Open mapping forces that minimum to be zero.
  have hclopen (U : Set S) (hU : IsClopen U) (hxU : x ∈ U) : (Z ∩ U).Nonempty := by
    obtain ⟨m, hm, hmin⟩ := hU.1.isCompact.exists_isMinOn ⟨x, hxU⟩ hF.norm.continuousOn
    by_cases hm0 : F m = 0
    · exact ⟨m, hm0, hm⟩
    obtain ⟨V, hV, hEq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hU.2
    have hmV : m.val ∈ V := by rw [← hEq] at hm; exact hm
    have hmNorm : 0 < ‖F m‖ := norm_pos_iff.mpr hm0
    have hclosure : F m ∈ closure (Metric.ball (0 : ℂ) ‖F m‖) := by
      rw [closure_ball _ hmNorm.ne', Metric.mem_closedBall, dist_zero_right]
    obtain ⟨w, hw, hwi⟩ := mem_closure_iff.mp hclosure (p.eval '' V) (hmap V hV)
      ⟨m.val, hmV, rfl⟩
    obtain ⟨v, hvV, rfl⟩ := hw
    have hvlt : ‖p.eval v‖ < ‖F m‖ := by simpa [Metric.mem_ball, dist_zero_right] using hwi
    have hmle : ‖F m‖ ≤ c := by simpa [hS, F] using m.2
    have hvS : v ∈ S := by rw [hS]; exact hvlt.le.trans hmle
    let y : S := ⟨v, hvS⟩
    have hyU : y ∈ U := by rw [← hEq]; exact hvV
    exact ((not_lt_of_ge (hmin hyU)) hvlt).elim
  let ι := {U : Set S // IsClopen U ∧ x ∈ U}
  have hZ : IsCompact Z := (isClosed_singleton.preimage hF).isCompact
  have hinter := hZ.inter_iInter_nonempty (fun i : ι => i.1) (fun i => i.2.1.1) (by
    intro t
    exact hclopen _ (isClopen_biInter_finset fun i _ => i.2.1)
      (mem_iInter₂.2 fun i _ => i.2.2))
  obtain ⟨r, hrZ, hrC⟩ := hinter
  rw [← connectedComponent_eq_iInter_isClopen] at hrC
  exact ⟨r.1, connectedComponentIn_eq_image hz ▸ ⟨r, hrC, rfl⟩, hrZ⟩

private noncomputable def OMA.goodmanQuartic : ℂ[X] :=
  X ^ 4 + (-(C ((20 / 3 : ℝ) : ℂ)) * X ^ 3 + C 2 * X ^ 2 - C 20 * X + C 101)

private noncomputable def OMA.goodmanLevel : ℝ := Real.sqrt (9159995 / 900)

private noncomputable def OMA.goodmanS : Set ℂ := Erdos1047.sublevelSet goodmanQuartic goodmanLevel

private theorem OMA.goodmanQuartic_degree_monic :
    goodmanQuartic.natDegree = 4 ∧ goodmanQuartic.Monic := by
  let q : ℂ[X] := -(C ((20 / 3 : ℝ) : ℂ)) * X ^ 3 + C 2 * X ^ 2 - C 20 * X + C 101
  have hd3 : (-(C ((20 / 3 : ℝ) : ℂ)) * X ^ 3).natDegree ≤ 3 :=
    natDegree_mul_le.trans (by simp)
  have hd2 : (C 2 * X ^ 2 : ℂ[X]).natDegree ≤ 3 :=
    natDegree_mul_le.trans (by simp)
  have hd1 : natDegree (-(C ((20 / 3 : ℝ) : ℂ)) * X ^ 3 + C 2 * X ^ 2) ≤ 3 :=
    (natDegree_add_le _ _).trans (max_le hd3 hd2)
  have hlin : (C 20 * X : ℂ[X]).natDegree ≤ 3 :=
    natDegree_mul_le.trans (by simp)
  have hd : natDegree (-(C ((20 / 3 : ℝ) : ℂ)) * X ^ 3 + C 2 * X ^ 2 - C 20 * X) ≤ 3 :=
    (natDegree_sub_le _ _).trans (max_le hd1 hlin)
  have hq : q.natDegree ≤ 3 := (natDegree_add_le _ _).trans (max_le hd (by simp))
  have hqNat : q.natDegree < 4 := by omega
  have hq4 : q.degree < (4 : ℕ) := degree_le_natDegree.trans_lt (by exact_mod_cast hqNat)
  have hnq : q.natDegree < (X ^ 4 : ℂ[X]).natDegree := by simpa using hqNat
  change (X ^ 4 + q).natDegree = 4 ∧ (X ^ 4 + q).Monic
  exact ⟨by rw [natDegree_add_eq_left_of_natDegree_lt hnq, natDegree_X_pow],
    monic_X_pow_add hq4⟩

private noncomputable def OMA.goodmanSq (x y : ℝ) : ℝ :=
  (3 * (x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4) - 20 * (x ^ 3 - 3 * x * y ^ 2) +
      6 * (x ^ 2 - y ^ 2) - 60 * x + 303) ^ 2 +
  (3 * (4 * x ^ 3 * y - 4 * x * y ^ 3) - 20 * (3 * x ^ 2 * y - y ^ 3) +
      12 * x * y - 60 * y) ^ 2

private theorem OMA.goodman_mem_iff (z : ℂ) :
    z ∈ goodmanS ↔ goodmanSq z.re z.im ≤ 9159995 / 100 := by
  have he : (3 : ℂ) * goodmanQuartic.eval z =
      ((3 : ℝ) : ℂ) * z ^ 4 - ((20 : ℝ) : ℂ) * z ^ 3 + ((6 : ℝ) : ℂ) * z ^ 2 -
        ((60 : ℝ) : ℂ) * z + ((303 : ℝ) : ℂ) := by
    norm_num [goodmanQuartic]
    ring
  have hq : ‖(3 : ℂ) * goodmanQuartic.eval z‖ ^ 2 = goodmanSq z.re z.im := by
    rw [he, Complex.sq_norm, Complex.normSq_apply]
    simp only [goodmanSq, pow_succ, pow_zero, mul_assoc, one_mul, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [norm_mul, Complex.norm_ofNat] at hq
  change ‖goodmanQuartic.eval z‖ ≤ Real.sqrt (9159995 / 900) ↔ _
  rw [Real.le_sqrt (norm_nonneg _) (by norm_num), ← hq]
  constructor <;> intro h <;> nlinarith

private theorem OMA.goodman_barriers (z : ℂ) (hz : z ∈ goodmanS) :
    z.re ≠ 0 ∧ z.re ≠ 5 ∧ (z.re < 0 → z.im ≠ 0) := by
  have h := (goodman_mem_iff z).1 hz
  refine ⟨?_, ?_, ?_⟩
  · intro hx
    rw [hx] at h
    let u := z.im ^ 2 - 1
    have hu : -1 ≤ u := by dsimp [u]; nlinarith [sq_nonneg z.im]
    have he : goodmanSq 0 z.im = 91600 + u ^ 2 * (9 * u ^ 2 + 400 * u + 600) := by
      dsimp [goodmanSq, u]
      ring
    rw [he] at h
    have hf : 0 ≤ 9 * u ^ 2 + 400 * u + 600 := by nlinarith [sq_nonneg u]
    nlinarith [mul_nonneg (sq_nonneg u) hf]
  · intro hx
    rw [hx] at h
    let v := z.im ^ 2
    have hv : 0 ≤ v := sq_nonneg _
    have he : goodmanSq 5 z.im = 222784 + 147264 * v + 21504 * v ^ 2 + 664 * v ^ 3 + 9 * v ^ 4 := by
      dsimp [goodmanSq, v]
      ring
    rw [he] at h
    nlinarith [pow_nonneg hv 2, pow_nonneg hv 3, pow_nonneg hv 4]
  · intro hx hy
    rw [hy] at h
    let t := -z.re
    have ht : 0 ≤ t := neg_nonneg.mpr hx.le
    have he : goodmanSq z.re 0 = (3 * t ^ 4 + 20 * t ^ 3 + 6 * t ^ 2 + 60 * t + 303) ^ 2 := by
      dsimp [goodmanSq, t]
      ring
    rw [he] at h
    have hp : 303 ≤ 3 * t ^ 4 + 20 * t ^ 3 + 6 * t ^ 2 + 60 * t + 303 := by
      nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 303) hp 2
    norm_num at hsq
    linarith

private noncomputable def OMA.goodmanZone (z : ℂ) : Fin 4 :=
  if z.re < 0 then
    if z.im < 0 then 0 else 1
  else
    if z.re < 5 then 2 else 3

private theorem OMA.goodman_zone_constant {U : Set ℂ} (hU : IsPreconnected U)
    (hsub : U ⊆ goodmanS) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    goodmanZone z = goodmanZone w := by
  have hre := Complex.continuous_re.continuousOn (s := U)
  have hl : z.re < 0 ↔ w.re < 0 := by
    constructor
    · intro h; exact hU.gt_of_ne hre (fun v hv => (goodman_barriers v (hsub hv)).1) ⟨z, hz, h⟩ hw
    · intro h; exact hU.gt_of_ne hre (fun v hv => (goodman_barriers v (hsub hv)).1) ⟨w, hw, h⟩ hz
  have hr : z.re < 5 ↔ w.re < 5 := by
    constructor
    · intro h; exact hU.gt_of_ne hre (fun v hv => (goodman_barriers v (hsub hv)).2.1) ⟨z, hz, h⟩ hw
    · intro h; exact hU.gt_of_ne hre (fun v hv => (goodman_barriers v (hsub hv)).2.1) ⟨w, hw, h⟩ hz
  by_cases h0 : z.re < 0
  · have hleft (v : ℂ) (hv : v ∈ U) : v.re < 0 :=
      hU.gt_of_ne hre (fun y hy => (goodman_barriers y (hsub hy)).1) ⟨z, hz, h0⟩ hv
    have hne (v : ℂ) (hv : v ∈ U) : v.im ≠ 0 :=
      (goodman_barriers v (hsub hv)).2.2 (hleft v hv)
    have him := Complex.continuous_im.continuousOn (s := U)
    have hi : z.im < 0 ↔ w.im < 0 :=
      ⟨fun h => hU.gt_of_ne him hne ⟨z, hz, h⟩ hw,
        fun h => hU.gt_of_ne him hne ⟨w, hw, h⟩ hz⟩
    simp [goodmanZone, h0, hl.mp h0, hi]
  · simp [goodmanZone, h0, mt hl.mpr h0, hr]

private noncomputable def OMA.goodmanSamples : Fin 4 → ℂ :=
  ![⟨-1, -2⟩, ⟨-1, 2⟩, ⟨2, 0⟩, ⟨13 / 2, 0⟩]

private theorem OMA.goodman_samples_mem (i : Fin 4) : goodmanSamples i ∈ goodmanS := by
  rw [goodman_mem_iff]
  fin_cases i <;> norm_num [goodmanSamples, goodmanSq]

private theorem OMA.goodman_samples_zone (i : Fin 4) : goodmanZone (goodmanSamples i) = i := by
  fin_cases i <;> apply Fin.ext <;> norm_num [goodmanZone, goodmanSamples]

theorem OMA.solution : type_of% @Erdos1047.erdos_1047.variants.goodman_simple_roots := by
  classical
  have hdeg := goodmanQuartic_degree_monic.1
  have hmonic := goodmanQuartic_degree_monic.2
  have hc : 0 < goodmanLevel := Real.sqrt_pos.2 (by norm_num)
  let R := goodmanQuartic.rootSet ℂ
  let W := Erdos1047.componentsIn goodmanS
  let T (z : ℂ) : Set ℂ := connectedComponentIn goodmanS z
  have hScompact : IsCompact goodmanS :=
    goodman_sublevel_compact goodmanQuartic hmonic (by omega) goodmanLevel hc.le
  have hcomp : W = T '' R := by
    ext U
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, hzero⟩ := goodman_component_has_root goodmanQuartic (by omega)
        goodmanLevel rfl hScompact hz
      exact ⟨r, hmonic.mem_rootSet.mpr (by simpa using hzero), (connectedComponentIn_eq hr).symm⟩
    · rintro ⟨r, hr, rfl⟩
      have hzero : goodmanQuartic.eval r = 0 := by
        simpa using (hmonic.mem_rootSet.mp hr)
      refine ⟨r, ?_, rfl⟩
      change ‖goodmanQuartic.eval r‖ ≤ goodmanLevel
      rw [hzero, norm_zero]
      exact hc.le
  have hRfin : R.Finite := goodmanQuartic.rootSet_finite ℂ
  have hWfin : W.Finite := hcomp ▸ hRfin.image T
  have hWle : W.ncard ≤ R.ncard := by
    rw [hcomp]
    exact Set.ncard_image_le hRfin
  have hRle : R.ncard ≤ 4 := (goodmanQuartic.ncard_rootSet_le ℂ).trans_eq hdeg
  let F (i : Fin 4) := T (goodmanSamples i)
  have hFsub : Set.range F ⊆ W := by
    rintro U ⟨i, rfl⟩
    exact ⟨goodmanSamples i, goodman_samples_mem i, rfl⟩
  have hFinj : Function.Injective F := by
    intro i j hij
    have hi : goodmanSamples i ∈ F i := mem_connectedComponentIn (goodman_samples_mem i)
    have hj : goodmanSamples j ∈ F i := hij ▸ mem_connectedComponentIn (goodman_samples_mem j)
    have hconst := goodman_zone_constant
      ((isConnected_connectedComponentIn_iff.mpr (goodman_samples_mem i)).isPreconnected)
      (connectedComponentIn_subset _ _) hi hj
    simpa only [goodman_samples_zone] using hconst
  have hFcard : (Set.range F).ncard = 4 := by
    rw [Set.ncard_range_of_injective hFinj]
    simp
  have hWge : 4 ≤ W.ncard := hFcard ▸ Set.ncard_le_ncard hFsub hWfin
  have hWcard : W.ncard = 4 := le_antisymm (hWle.trans hRle) hWge
  have hRcard : R.ncard = 4 := le_antisymm hRle (hWge.trans hWle)
  have hrange : Set.range F = W :=
    Set.eq_of_subset_of_ncard_le hFsub (by rw [hWcard, hFcard]) hWfin
  have hcentral (w : ℂ) (hw : w ∈ goodmanS) (hzone : goodmanZone w = 2) : w ∈ F 2 := by
    obtain ⟨i, hi⟩ : T w ∈ Set.range F := by rw [hrange]; exact ⟨w, hw, rfl⟩
    have hwC : w ∈ F i := hi ▸ mem_connectedComponentIn hw
    have hsample : goodmanSamples i ∈ F i := mem_connectedComponentIn (goodman_samples_mem i)
    have hconst := goodman_zone_constant
      ((isConnected_connectedComponentIn_iff.mpr (goodman_samples_mem i)).isPreconnected)
      (connectedComponentIn_subset _ _) hsample hwC
    rw [goodman_samples_zone, hzone] at hconst
    simpa [hconst] using hwC
  refine ⟨goodmanQuartic, goodmanLevel, hmonic, hdeg, hRcard, hc, hWcard, F 2,
    hFsub ⟨2, rfl⟩, ?_⟩
  intro hconvex
  let wLower : ℂ := ⟨1 / 200, -1⟩
  let wUpper : ℂ := ⟨1 / 200, 1⟩
  have hLower : wLower ∈ F 2 :=
    hcentral wLower (by rw [goodman_mem_iff]; norm_num [wLower, goodmanSq])
      (by norm_num [wLower, goodmanZone])
  have hUpper : wUpper ∈ F 2 :=
    hcentral wUpper (by rw [goodman_mem_iff]; norm_num [wUpper, goodmanSq])
      (by norm_num [wUpper, goodmanZone])
  have hmid := hconvex hLower hUpper (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmidS := connectedComponentIn_subset goodmanS (goodmanSamples 2) hmid
  have he : (1 / 2 : ℝ) • wLower + (1 / 2 : ℝ) • wUpper = (⟨1 / 200, 0⟩ : ℂ) := by
    apply Complex.ext <;> norm_num [wLower, wUpper, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im]
  rw [he, goodman_mem_iff] at hmidS
  norm_num [goodmanSq] at hmidS