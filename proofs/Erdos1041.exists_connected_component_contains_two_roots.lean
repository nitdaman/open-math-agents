import FormalConjectures.ErdosProblems.«1041»
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
The critical-value argument is due to G. Szegő,
“Components of the set |(z−z₁)⋯(z−zₙ)| ≤ 1”, American Mathematical Monthly 58 (1951), 639.
-/

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Finset Matrix Polynomial Set

private theorem OMA.vandermonde_norm_bound {n : ℕ} (hn : 2 ≤ n)
    (r : Fin n → ℂ) (hr : ∀ i, ‖r i‖ < 1) :
    ‖(Matrix.vandermonde r).det‖ ^ 2 < (n : ℝ) ^ n := by
  classical
  let V := Matrix.vandermonde r
  let G := V * Vᴴ
  have hG : G.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  let e := hG.isHermitian.eigenvalues
  have he (i : Fin n) : 0 ≤ e i := hG.eigenvalues_nonneg i
  have hnd : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnd
  have htrace : ∑ i, e i < (n : ℝ) * n := by
    have ht := congrArg Complex.re hG.isHermitian.trace_eq_sum_eigenvalues
    change (∑ i : Fin n, G i i).re = (∑ i, (e i : ℂ)).re at ht
    simp only [Complex.re_sum, Complex.ofReal_re] at ht
    rw [← ht]
    have hrow (i : Fin n) : (G i i).re < n := by
      change (∑ j : Fin n, V i j * star (V i j)).re < n
      simp only [Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      have her (j : Fin n) : Complex.normSq (V i j) ≤ 1 := by
        simp only [V, Matrix.vandermonde_apply, map_pow]
        have hr₂ : Complex.normSq (r i) ≤ 1 := by
          rw [← Complex.sq_norm]
          nlinarith [norm_nonneg (r i), hr i, mul_nonneg (norm_nonneg (r i)) (sub_nonneg.mpr (hr i).le)]
        exact pow_le_one₀ (Complex.normSq_nonneg _) hr₂
      let j₁ : Fin n := ⟨1, by omega⟩
      have hl : Complex.normSq (V i j₁) < 1 := by
        simp only [V, j₁, Matrix.vandermonde_apply, pow_one, ← Complex.sq_norm]
        nlinarith [norm_nonneg (r i), hr i, mul_nonneg (norm_nonneg (r i)) (sub_nonneg.mpr (hr i).le)]
      simpa using Finset.sum_lt_sum (fun j _ => her j)
        ⟨j₁, Finset.mem_univ j₁, hl⟩
    have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin n)))
      ⟨⟨0, hnd⟩, Finset.mem_univ _⟩ (fun i _ => hrow i)
    simpa using hlt
  have hdet : ‖V.det‖ ^ 2 = ∏ i, e i := by
    have hd := congrArg Complex.re hG.isHermitian.det_eq_prod_eigenvalues
    change G.det.re = (∏ i, (e i : ℂ)).re at hd
    rw [← Complex.ofReal_prod Finset.univ e, Complex.ofReal_re] at hd
    rw [← hd]
    simp [G, Matrix.det_mul, Matrix.det_conjTranspose, Complex.mul_conj,
      Complex.sq_norm]
  let w : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  have hwSum : ∑ i, w i = 1 := by simp [w, hnR.ne']
  have ham := Real.geom_mean_le_arith_mean_weighted Finset.univ w e
    (fun _ _ => inv_nonneg.mpr hnR.le) hwSum (fun i _ => he i)
  have hsum : ∑ i, w i * e i < (n : ℝ) := by
    simp only [w, ← Finset.mul_sum]
    rw [← div_eq_inv_mul, div_lt_iff₀ hnR]
    exact htrace
  have hgm : (∏ i, e i) ^ (n : ℝ)⁻¹ < (n : ℝ) := by
    rw [← Real.finsetProd_rpow Finset.univ e (fun i _ => he i)]
    exact ham.trans_lt hsum
  have hpow := Real.rpow_lt_rpow (Real.rpow_nonneg (Finset.prod_nonneg fun i _ => he i) _)
    hgm hnR
  rw [Real.rpow_inv_rpow (Finset.prod_nonneg fun i _ => he i) hnR.ne',
    Real.rpow_natCast, ← hdet] at hpow
  exact hpow

private theorem OMA.prod_root_derivative_norm {n : ℕ} (r : Fin n → ℂ) :
    ∏ i, ‖(∏ j, (X - C (r j))).derivative.eval (r i)‖ = ‖(Matrix.vandermonde r).det‖ ^ 2 := by
  classical
  have hderiv (i : Fin n) : ‖(∏ j, (X - C (r j))).derivative.eval (r i)‖ =
      ∏ j ∈ Finset.univ.erase i, ‖r i - r j‖ := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => X - C (r j)) (Finset.mem_univ i)]
    simp [derivative_mul, eval_prod, norm_prod]
  have hsplit (i : Fin n) : ∏ j ∈ Finset.univ.erase i, ‖r i - r j‖ =
      (∏ j ∈ Finset.Ioi i, ‖r i - r j‖) * ∏ j ∈ Finset.Iio i, ‖r i - r j‖ := by
    rw [← Finset.prod_union (by
      refine Finset.disjoint_left.mpr ?_
      intro j hj hk
      exact (not_lt_of_ge (Finset.mem_Ioi.mp hj).le) (Finset.mem_Iio.mp hk))]
    congr 1
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
      Finset.mem_Iio]
    exact ne_iff_lt_or_gt.trans or_comm
  have hswap : (∏ i, ∏ j ∈ Finset.Iio i, ‖r i - r j‖) =
      ∏ i, ∏ j ∈ Finset.Ioi i, ‖r j - r i‖ := by
    apply Finset.prod_comm'
    simp
  rw [Matrix.det_vandermonde, norm_prod, sq]
  simp_rw [norm_prod, hderiv, hsplit, Finset.prod_mul_distrib, hswap]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => norm_sub_rev _ _))

private theorem OMA.prod_index_roots {R M : Type*} [CommMonoid M] (s : Multiset R)
    (g : R → M) : (s.map g).prod = ∏ i : Fin s.toList.length, g (s.toList.get i) := by
  rw [← List.prod_ofFn]
  change _ = (List.ofFn (g ∘ s.toList.get)).prod
  rw [← List.map_ofFn, List.ofFn_get]
  simp

private theorem OMA.polynomial_small_critical_value (p : ℂ[X]) (hdeg : 2 ≤ p.natDegree)
    (hp : p.Monic) (hr : ∀ z ∈ p.roots, ‖z‖ < 1) :
    ∃ z, p.derivative.IsRoot z ∧ ‖p.eval z‖ < 1 := by
  classical
  let L := p.roots.toList
  let r : Fin L.length → ℂ := L.get
  have hs := IsAlgClosed.splits p
  have hsd := IsAlgClosed.splits p.derivative
  have hL : L.length = p.natDegree := by simpa [L] using hs.natDegree_eq_card_roots.symm
  have hroots (i : Fin L.length) : ‖r i‖ < 1 :=
    hr (r i) (Multiset.mem_toList.mp (List.get_mem L i))
  have hpFact : p = ∏ j, (X - C (r j)) :=
    (hs.eq_prod_roots_of_monic hp).trans (prod_index_roots _ _)
  have hderivBound : ‖(p.roots.map p.derivative.eval).prod‖ < (p.natDegree : ℝ) ^ p.natDegree := by
    rw [prod_index_roots, norm_prod]
    change ∏ i, ‖p.derivative.eval (r i)‖ < _
    calc
      _ = ‖(Matrix.vandermonde r).det‖ ^ 2 := by
        convert prod_root_derivative_norm r using 1
        exact congrArg (fun q : ℂ[X] => ∏ i, ‖q.derivative.eval (r i)‖) hpFact
      _ < _ := by simpa [hL] using vandermonde_norm_bound (hL ▸ hdeg) r hroots
  have hre := resultant_eq_prod_eval p p.derivative p.derivative.natDegree le_rfl hs
  have hrd := resultant_eq_prod_eval p.derivative p p.natDegree le_rfl hsd
  have hidentity :
      (p.natDegree : ℝ) ^ p.natDegree * ‖(p.derivative.roots.map p.eval).prod‖ =
        ‖(p.roots.map p.derivative.eval).prod‖ := by
    calc
      _ = ‖resultant p.derivative p p.derivative.natDegree p.natDegree‖ := by
        rw [hrd, norm_mul, norm_pow, leadingCoeff_derivative, hp.leadingCoeff, one_mul,
          Complex.norm_natCast]
      _ = ‖resultant p p.derivative p.natDegree p.derivative.natDegree‖ := by
        rw [resultant_comm p.derivative p]
        simp [norm_pow]
      _ = _ := by rw [hre, hp.leadingCoeff, one_pow, one_mul]
  have hdn : p.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  by_contra! h
  have hprod : 1 ≤ ‖(p.derivative.roots.map p.eval).prod‖ := by
    rw [prod_index_roots, norm_prod]
    apply Finset.one_le_prod
    intro i _
    exact h _ ((mem_roots hdn).1 (Multiset.mem_toList.mp (List.get_mem _ i)))
  have hle :
      (p.natDegree : ℝ) ^ p.natDegree ≤
        (p.natDegree : ℝ) ^ p.natDegree * ‖(p.derivative.roots.map p.eval).prod‖ :=
    le_mul_of_one_le_right (by positivity) hprod
  exact (not_lt_of_ge (hle.trans_eq hidentity)) hderivBound

private theorem OMA.polynomial_component_surj (p : ℂ[X]) (hdeg : 0 < p.natDegree)
    (hbounded : Bornology.IsBounded {z : ℂ | ‖p.eval z‖ < 1})
    {z : ℂ} (hz : ‖p.eval z‖ < 1) :
    p.eval '' connectedComponentIn {q : ℂ | ‖p.eval q‖ < 1} z = Metric.ball 0 1 := by
  let S := {q : ℂ | ‖p.eval q‖ < 1}
  let D := Metric.ball (0 : ℂ) 1
  let U := connectedComponentIn S z
  have hzS : z ∈ S := hz
  have hUS : U ⊆ S := connectedComponentIn_subset S z
  have hzU : z ∈ U := mem_connectedComponentIn hzS
  have hU : IsConnected U := isConnected_connectedComponentIn_iff.mpr hzS
  have hD : IsPreconnected D := (convex_ball (0 : ℂ) 1).isPreconnected
  have hSopen : IsOpen S := isOpen_lt (p.continuous.norm) continuous_const
  have hmap : IsOpenMap p.eval := by
    have han : AnalyticOnNhd ℂ p.eval univ := fun z _ => p.differentiable.analyticAt z
    rcases han.is_constant_or_isOpenMap with ⟨w, heq⟩ | hopen
    · have hpconst : p = C w := Polynomial.funext (fun x => by simpa using heq x)
      rw [hpconst, natDegree_C] at hdeg
      omega
    · exact hopen
  have himage : p.eval '' U ⊆ D := by
    rintro w ⟨q, hq, rfl⟩
    simpa [S, D, Metric.mem_ball, dist_zero_right] using hUS hq
  have hpart : closure U ∩ S ⊆ U := by
    have hpre : IsPreconnected (closure U ∩ S) :=
      hU.isPreconnected.subset_closure
        (fun q hq => ⟨subset_closure hq, hUS hq⟩) inter_subset_left
    exact hpre.subset_connectedComponentIn ⟨subset_closure hzU, hzS⟩ inter_subset_right
  have hcl : IsClosed (p.eval '' closure U) :=
    (((hbounded.subset hUS).isCompact_closure).image p.continuous).isClosed
  have hclSub : closure (p.eval '' U) ⊆ p.eval '' closure U :=
    closure_minimal (image_mono subset_closure) hcl
  refine Subset.antisymm himage (hD.subset_of_closure_inter_subset
    (hmap _ hSopen.connectedComponentIn) ⟨p.eval z, himage ⟨z, hzU, rfl⟩, ⟨z, hzU, rfl⟩⟩ ?_)
  intro w hw
  obtain ⟨q, hq, rfl⟩ := hclSub hw.1
  have hqS : q ∈ S := by
    simpa [S, D, Metric.mem_ball, dist_zero_right] using hw.2
  exact ⟨q, hpart ⟨hq, hqS⟩, rfl⟩

private theorem OMA.polynomial_lemniscate_bounded (p : ℂ[X]) (hp : p.Monic)
    (hr : ∀ z ∈ p.roots, ‖z‖ < 1) :
    Bornology.IsBounded {z : ℂ | ‖p.eval z‖ < 1} := by
  classical
  refine Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) 2) ?_
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra! hzlarge
  have hge : 1 ≤ ‖p.eval z‖ := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp, prod_index_roots, norm_prod]
    apply Finset.one_le_prod
    intro i _
    have hi := hr (p.roots.toList.get i) (Multiset.mem_toList.mp (List.get_mem _ i))
    have ht := norm_add_le (z - p.roots.toList.get i) (p.roots.toList.get i)
    rw [sub_add_cancel] at ht
    linarith
  exact (not_lt_of_ge hge) hz

theorem OMA.solution :
    type_of% @Erdos1041.exists_connected_component_contains_two_roots := by
  classical
  intro n p hn hnum hp hr
  let S := {z : ℂ | ‖p.eval z‖ < 1}
  have hdeg : 2 ≤ p.natDegree := hnum ▸ hn
  have hroots (z : ℂ) (hz : z ∈ p.roots) : ‖z‖ < 1 := by
    have hz' := hr ((hp.mem_rootSet).2 (by simpa using (mem_roots hp.ne_zero).1 hz))
    simpa [Metric.mem_ball, dist_zero_right] using hz'
  have hb := polynomial_lemniscate_bounded p hp hroots
  obtain ⟨z, hdz, hz⟩ := polynomial_small_critical_value p hdeg hp hroots
  let q := p - C (p.eval z)
  have hqdeg : q.natDegree = p.natDegree := natDegree_sub_C
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hqdeg
    omega
  have hqm : 1 < q.rootMultiplicity z := by
    apply (one_lt_rootMultiplicity_iff_isRoot hq0).2
    constructor
    · simp [q, Polynomial.IsRoot]
    · simpa [q] using hdz
  have hqnd : ¬ q.roots.Nodup := by
    intro hnq
    have hcount := Multiset.nodup_iff_count_le_one.mp hnq z
    rw [count_roots] at hcount
    omega
  have hqcard : q.roots.toFinset.card < p.natDegree := by
    have hc := (IsAlgClosed.splits q).natDegree_eq_card_roots
    have hl := q.roots.toFinset_card_le
    rw [← hc, hqdeg] at hl
    exact lt_of_le_of_ne hl fun he => hqnd
      (Multiset.toFinset_card_eq_card_iff_nodup.mp (by rw [← hc, hqdeg]; exact he))
  by_contra! hno
  have hsmall (x : ℂ) (hx : x ∈ S) :
      (p.roots.filter (· ∈ connectedComponentIn S x)).card < 2 :=
    hno (connectedComponentIn S x) (connectedComponentIn_subset _ _)
      (isConnected_connectedComponentIn_iff.mpr hx)
  have hmem (x : ℂ) (hx : x ∈ p.roots) : x ∈ S := by
    change ‖p.eval x‖ < 1
    have he : p.eval x = 0 := (mem_roots hp.ne_zero).1 hx
    simp [he]
  have hnodup : p.roots.Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro x
    by_contra! hc
    have hxp : x ∈ p.roots := Multiset.count_pos.mp (by omega)
    have hxS := hmem x hxp
    have hxC : x ∈ connectedComponentIn S x := mem_connectedComponentIn hxS
    have hcard := Multiset.count_le_card x (p.roots.filter (· ∈ connectedComponentIn S x))
    rw [Multiset.count_filter_of_pos hxC] at hcard
    have hs := hsmall x hxS
    omega
  have hpre (x : p.roots.toFinset) : ∃ y,
      y ∈ connectedComponentIn S x.1 ∧ p.eval y = p.eval z := by
    have hx := hmem x.1 (Multiset.mem_toFinset.mp x.2)
    have hs := polynomial_component_surj p (by omega) hb hx
    have hv : p.eval z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    rw [← hs] at hv
    exact hv
  choose g hg using hpre
  let f : p.roots.toFinset → q.roots.toFinset := fun x =>
    ⟨g x, Multiset.mem_toFinset.mpr ((mem_roots hq0).2 (by
      simp [q, Polynomial.IsRoot, (hg x).2]))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_contra! hne
    have hgy : g x = g y := congrArg Subtype.val hxy
    have hCx := connectedComponentIn_eq (hg x).1
    have hCy := connectedComponentIn_eq (hg y).1
    have hCS : connectedComponentIn S x.1 = connectedComponentIn S y.1 := by
      rw [hCx, hgy, ← hCy]
    have hxS := hmem x.1 (Multiset.mem_toFinset.mp x.2)
    have hyS := hmem y.1 (Multiset.mem_toFinset.mp y.2)
    have hsub : ({x.1, y.1} : Finset ℂ) ⊆
        (p.roots.filter (· ∈ connectedComponentIn S x.1)).toFinset := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr
          ⟨Multiset.mem_toFinset.mp x.2, mem_connectedComponentIn hxS⟩)
      · exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr
          ⟨Multiset.mem_toFinset.mp y.2, hCS ▸ mem_connectedComponentIn hyS⟩)
    have htwo := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
    rw [Finset.card_pair hne] at htwo
    exact (not_lt_of_ge htwo) (hsmall x.1 hxS)
  have hpcard : p.roots.toFinset.card = p.natDegree := by
    rw [Multiset.toFinset_card_of_nodup hnodup, (IsAlgClosed.splits p).natDegree_eq_card_roots]
  have hle := Finset.card_le_card_of_injective hf
  rw [hpcard] at hle
  exact (not_lt_of_ge hle) hqcard