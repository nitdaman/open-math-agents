import FormalConjectures.ErdosProblems.«1038»
import Mathlib.Analysis.MeanInequalities

/-!
The cubic argument is due to J. Koizumi (19 December 2025).
https://www.erdosproblems.com/forum/thread/1038
-/

open scoped BigOperators ENNReal
open MeasureTheory Set Polynomial

private def OMA.rootProduct {n : ℕ} (r : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∏ i, |x - r i|

private theorem OMA.continuous_rootProduct {n : ℕ} (r : Fin n → ℝ) :
    Continuous (rootProduct r) :=
  continuous_finsetProd _ fun _ _ => (continuous_id.sub continuous_const).abs

private theorem OMA.rootProduct_lt_one {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1) (hs : 0 ≤ ∑ i, r i)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : rootProduct r x < 1 := by
  let w : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  let z : Fin n → ℝ := fun i => |x - r i|
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw (i : Fin n) : 0 < w i := inv_pos.mpr hnR
  have hwSum : ∑ i, w i = 1 := by simp [w, hnR.ne']
  have hz (i : Fin n) : 0 ≤ z i := abs_nonneg _
  have hzBound (i : Fin n) : z i ≤ 1 - x * r i := by
    dsimp [z]
    apply abs_le.mpr
    constructor
    · have hh := mul_nonneg (show 0 ≤ 1 + x by linarith [hx.1])
        (sub_nonneg.mpr (hr i).2)
      nlinarith
    · have hk := mul_nonneg (sub_nonneg.mpr hx.2.le)
        (show 0 ≤ 1 + r i by linarith [(hr i).1])
      nlinarith
  have hweighted : ∑ i, w i * z i ≤ 1 := by
    calc
      ∑ i, w i * z i ≤ ∑ i, w i * (1 - x * r i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hzBound i) (hw i).le
      _ = 1 - (n : ℝ)⁻¹ * x * ∑ i, r i := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hwSum]
        congr 1
        simp only [w, ← mul_assoc, Finset.mul_sum]
      _ ≤ 1 := sub_le_self _ (mul_nonneg (mul_nonneg (inv_nonneg.mpr hnR.le) hx.1.le) hs)
  have ham := Real.geom_mean_le_arith_mean_weighted Finset.univ w z
    (fun i _ => (hw i).le) hwSum (fun i _ => hz i)
  have hgm : (rootProduct r x) ^ (n : ℝ)⁻¹ = ∏ i, z i ^ w i :=
    (Real.finsetProd_rpow Finset.univ z (fun i _ => hz i) _).symm
  by_contra! h
  have hge : 1 ≤ ∏ i, z i ^ w i := by
    rw [← hgm, ← Real.one_rpow ((n : ℝ)⁻¹)]
    exact Real.rpow_le_rpow zero_le_one h (inv_nonneg.mpr hnR.le)
  have heq : ∏ i, z i ^ w i = ∑ i, w i * z i :=
    le_antisymm ham (hweighted.trans hge)
  have hsumOne : ∑ i, w i * z i = 1 := le_antisymm hweighted (hge.trans ham)
  have hone (i : Fin n) : z i = 1 := by
    have ht := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos'
      Finset.univ w z (fun i _ => hw i) hwSum (fun i _ => hz i)).mp heq i (Finset.mem_univ i)
    exact ht.trans hsumOne
  have hroot (i : Fin n) : r i = x - 1 := by
    have hi : |x - r i| = 1 := hone i
    rcases le_or_gt (r i) x with hle | hgt
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hi
      linarith
    · rw [abs_of_neg (sub_neg.mpr hgt)] at hi
      linarith [(hr i).2, hx.1]
  have hsum : ∑ i, r i = (n : ℝ) * (x - 1) := by simp [hroot, mul_sub]
  rw [hsum] at hs
  exact (not_lt_of_ge hs) (mul_neg_of_pos_of_neg hnR (sub_neg.mpr hx.2))

private theorem OMA.koizumiCubic {a b y : ℝ} (ha : a = 4 * b) (hb : 4 * b ^ 3 = 1)
    (hy : y ∈ Ioo 0 a) : 0 ≤ (a - y) * (y - b) ^ 2 ∧
      (a - y) * (y - b) ^ 2 ≤ 1 ∧
      (y ≠ 3 * b → (a - y) * (y - b) ^ 2 < 1) := by
  have hid : 1 - (a - y) * (y - b) ^ 2 = y * (y - 3 * b) ^ 2 := by
    rw [ha, ← hb]
    ring
  refine ⟨mul_nonneg (sub_nonneg.mpr hy.2.le) (sq_nonneg _), ?_, ?_⟩
  · linarith [mul_nonneg hy.1.le (sq_nonneg (y - 3 * b))]
  · intro hn
    linarith [mul_pos hy.1 (sq_pos_of_ne_zero (sub_ne_zero.mpr hn))]

private theorem OMA.koizumiTail {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1)
    {a b : ℝ} (ha : a = 4 * b) (hb : 4 * b ^ 3 = 1)
    {d : ℝ} (hd : d ∈ Ioo 1 (a - 1)) (hne : d ≠ 3 * b - r ⟨0, hn⟩) :
    rootProduct r (a - d) < 1 ∨ rootProduct r (b - d) < 1 := by
  let q : Fin n → ℝ := fun i => (a - (r i + d)) * (r i + d - b) ^ 2
  let i₀ : Fin n := ⟨0, hn⟩
  have hq (i : Fin n) := koizumiCubic ha hb
    (show r i + d ∈ Ioo 0 a from
      ⟨by linarith [(hr i).1, hd.1], by linarith [(hr i).2, hd.2]⟩)
  have hq₀ : q i₀ < 1 := (hq i₀).2.2 fun he => hne (by dsimp [i₀] at he; linarith)
  have hprod : ∏ i, q i < 1 := by
    rw [← Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i₀)]
    exact (mul_le_of_le_one_right (hq i₀).1
      (Finset.prod_le_one (fun i _ => (hq i).1) (fun i _ => (hq i).2.1))).trans_lt hq₀
  have hfactor (i : Fin n) : |a - d - r i| * |b - d - r i| ^ 2 = q i := by
    rw [abs_of_nonneg (show 0 ≤ a - d - r i by linarith [(hr i).2, hd.2]), sq_abs]
    dsimp [q]
    ring
  have hid : rootProduct r (a - d) * rootProduct r (b - d) ^ 2 = ∏ i, q i := by
    unfold rootProduct
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hfactor i)
  by_contra! h
  have ht : 1 ≤ rootProduct r (b - d) ^ 2 := by nlinarith [sq_nonneg (rootProduct r (b - d) - 1)]
  exact (not_lt_of_ge (one_le_mul_of_one_le_of_one_le h.1 ht)) (hid.trans_lt hprod)

private theorem OMA.rootProduct_measure_of_sum {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1) (hs : 0 ≤ ∑ i, r i)
    {a b : ℝ} (ha : a = 4 * b) (hb : 4 * b ^ 3 = 1) (ha₂ : 2 < a) (hb₁ : b < 1) :
    ENNReal.ofReal (a - 1) ≤ volume {x : ℝ | rootProduct r x < 1} := by
  let E := {x : ℝ | rootProduct r x < 1}
  let J := Ioo (1 : ℝ) (a - 1)
  let A := E ∩ Ioo 1 (a - 1)
  let B := E ∩ Ioo (b - (a - 1)) (b - 1)
  let C := Ioo (0 : ℝ) 1
  have hE : MeasurableSet E :=
    ((continuous_rootProduct r).isOpen_preimage _ isOpen_Iio).measurableSet
  have hA : MeasurableSet A := hE.inter measurableSet_Ioo
  have hB : MeasurableSet B := hE.inter measurableSet_Ioo
  have hC : MeasurableSet C := measurableSet_Ioo
  have hcover : J \ {3 * b - r ⟨0, hn⟩} ⊆
      ((fun x : ℝ => a - x) ⁻¹' A) ∪ ((fun x : ℝ => b - x) ⁻¹' B) := by
    rintro d ⟨hd, hne⟩
    rcases koizumiTail hn r hr ha hb hd hne with h | h
    · exact Or.inl ⟨h, by constructor <;> linarith [hd.1, hd.2]⟩
    · exact Or.inr ⟨h, by constructor <;> linarith [hd.1, hd.2]⟩
  have htails : ENNReal.ofReal (a - 2) ≤ volume A + volume B := by
    have h := (measure_mono (μ := (volume : Measure ℝ)) hcover).trans (measure_union_le _ _)
    rw [measure_sdiff_null (by simp),
      (volume.measurePreserving_sub_left a).measure_preimage hA.nullMeasurableSet,
      (volume.measurePreserving_sub_left b).measure_preimage hB.nullMeasurableSet, Real.volume_Ioo] at h
    simpa [J, show a - 1 - 1 = a - 2 by ring] using h
  have hCsub : C ⊆ E := fun x hx => rootProduct_lt_one hn r hr hs hx
  have hdisj : Disjoint A B := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    linarith [hx.2.1, hy.2.2]
  have hdisjC : Disjoint (A ∪ B) C := by
    refine Set.disjoint_left.mpr ?_
    rintro x (hx | hx) hy
    · exact (not_lt_of_ge hx.2.1.le) hy.2
    · linarith [hx.2.2, hy.1]
  have hsub : (A ∪ B) ∪ C ⊆ E :=
    union_subset (union_subset inter_subset_left inter_subset_left) hCsub
  calc
    ENNReal.ofReal (a - 1) = ENNReal.ofReal (a - 2) + volume C := by
      rw [show volume C = ENNReal.ofReal 1 by norm_num [C, Real.volume_Ioo],
        ← ENNReal.ofReal_add (sub_nonneg.mpr ha₂.le) zero_le_one]
      congr 1
      ring
    _ ≤ volume A + volume B + volume C := by gcongr
    _ = volume ((A ∪ B) ∪ C) := by rw [measure_union hdisjC hC, measure_union hdisj hB]
    _ ≤ volume E := measure_mono hsub

private theorem OMA.rootProduct_measure {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1) :
    ENNReal.ofReal ((2 : ℝ) ^ (4 / 3 : ℝ) - 1) ≤ volume {x : ℝ | rootProduct r x < 1} := by
  let a : ℝ := (2 : ℝ) ^ (4 / 3 : ℝ)
  let b : ℝ := a / 4
  have haPos : 0 < a := by dsimp [a]; positivity
  have haC : a ^ 3 = 16 := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
      show 4 / 3 * (↑(3 : ℕ) : ℝ) = 4 by norm_num]
    norm_num
  have ha₂ : 2 < a := by
    by_contra! h
    have h' := pow_le_pow_left₀ haPos.le h 3
    norm_num [haC] at h'
  have ha₄ : a < 4 := by
    by_contra! h
    have h' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h 3
    norm_num [haC] at h'
  have ha : a = 4 * b := by dsimp [b]; ring
  have hb : 4 * b ^ 3 = 1 := by dsimp [b]; rw [div_pow, haC]; norm_num
  have hb₁ : b < 1 := by dsimp [b]; linarith
  rcases le_or_gt 0 (∑ i, r i) with hs | hs
  · exact rootProduct_measure_of_sum hn r hr hs ha hb ha₂ hb₁
  · let s : Fin n → ℝ := fun i => -r i
    have hs' (i : Fin n) : s i ∈ Icc (-1 : ℝ) 1 :=
      ⟨by dsimp [s]; linarith [(hr i).2], by dsimp [s]; linarith [(hr i).1]⟩
    have hsum : 0 ≤ ∑ i, s i := by simpa [s, Finset.sum_neg_distrib] using neg_nonneg.mpr hs.le
    have he (x : ℝ) : rootProduct s x = rootProduct r (-x) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← abs_neg (-x - r i)]
      congr 1
      dsimp [s]
      ring
    have hmeas : MeasurableSet {x : ℝ | rootProduct r x < 1} :=
      ((continuous_rootProduct r).isOpen_preimage _ isOpen_Iio).measurableSet
    have hvol : volume {x : ℝ | rootProduct s x < 1} =
        volume {x : ℝ | rootProduct r x < 1} := by
      simp only [he]
      exact ((volume : Measure ℝ).measurePreserving_neg).measure_preimage hmeas.nullMeasurableSet
    rw [← hvol]
    exact rootProduct_measure_of_sum hn s hs' hsum ha hb ha₂ hb₁

theorem OMA.solution : type_of% @Erdos1038.erdos_1038.variants.inf_lowerBound := by
  classical
  refine le_iInf ?_
  rintro ⟨f, hmonic, hne, hfilter⟩
  have hcardle := f.card_roots'
  have hcardge := Multiset.card_le_card (Multiset.filter_le (fun x => x ∈ Icc (-1 : ℝ) 1) f.roots)
  have hcard : f.roots.card = f.natDegree := by omega
  have hfiltereq : f.roots.filter (fun x => x ∈ Icc (-1 : ℝ) 1) = f.roots :=
    Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) (by omega)
  have hr' (x : ℝ) (hx : x ∈ f.roots) : x ∈ Icc (-1 : ℝ) 1 :=
    (Multiset.mem_filter.mp (hfiltereq.symm ▸ hx)).2
  have hsplits := Polynomial.splits_iff_card_roots.mpr hcard
  let L := f.roots.toList
  let r : Fin L.length → ℝ := L.get
  have hn : 0 < L.length := by
    have hdeg : f.natDegree ≠ 0 := fun hd => hne (hmonic.natDegree_eq_zero.mp hd)
    simpa [L, hcard] using Nat.pos_of_ne_zero hdeg
  have hr (i : Fin L.length) : r i ∈ Icc (-1 : ℝ) 1 :=
    hr' (r i) (Multiset.mem_toList.mp (List.get_mem L i))
  have he (x : ℝ) : |f.eval x| = rootProduct r x := by
    rw [hsplits.eval_eq_prod_roots_of_monic hmonic]
    change |(f.roots.map fun z => x - z).prod| = _
    rw [← f.roots.coe_toList]
    simp only [Multiset.map_coe, Multiset.prod_coe]
    change |(L.map fun z => x - z).prod| = _
    calc
      _ = |((List.ofFn r).map fun z => x - z).prod| := by
        rw [show List.ofFn r = L from List.ofFn_get L]
      _ = _ := by rw [List.map_ofFn, List.prod_ofFn, Finset.abs_prod]; rfl
  simp_rw [he]
  calc
    (2 : ℝ≥0∞) ^ (4 / 3 : ℝ) - 1 =
        ENNReal.ofReal ((2 : ℝ) ^ (4 / 3 : ℝ) - 1) := by
      rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one,
        ← ENNReal.ofReal_rpow_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (by norm_num)]
      norm_num
    _ ≤ volume {x : ℝ | rootProduct r x < 1} := rootProduct_measure hn r hr