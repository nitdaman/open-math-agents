import FormalConjectures.ErdosProblems.«633»

/-!
# Simili-Cutting Every Triangle into `n ∉ {0, 2, 3, 5}` Similar Triangles

We prove `Erdos633.IsSimiliCuttable.of_ne_zero_two_three_five`: every triangle `T` in `ℝ²` can be
decomposed into `n` mutually similar triangles for every `n ∉ {0, 2, 3, 5}` (Soifer 2009).
1. Using barycentric coordinates on `T`, any nonzero scale `s` and offset `a : Fin 3 → ℝ` with
   `∑ i, a i = 1 - s` defines a homothetic sub-triangle `subTri T s hs a` similar to `T`, whose
   closed/open interior is characterized by `∀ i, a i ≤ w i` (when `s > 0`) or `∀ i, w i ≤ a i`
   (when `s < 0`).
2. For every `m ≥ 2`, placing one `((m - 1) / m)`-scaled copy at vertex `0` together with `m`
   upright and `m - 1` inverted `(1 / m)`-scaled copies along the opposite base strip gives a
   decomposition of `T` into `2 * m` copies similar to `T`.
3. For `n = 1`, `T` itself works. For odd `n ≥ 7`, decomposing `T` into the even number `n - 3 ≥ 4`
   copies and subdividing one copy into `4` copies (`m = 2`) yields `n` mutually similar copies.
-/

-- Problem: Erdős Problem 633 — of ne zero two three five
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/633.lean:110 (declaration Erdos633.IsSimiliCuttable.of_ne_zero_two_three_five)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos633SimiliCuttableProof

open Affine
open scoped EuclideanGeometry Similar NNReal

private def vec3 (x y z : ℝ) : Fin 3 → ℝ
  | 0 => x
  | 1 => y
  | 2 => z

private lemma affineCombination_eq_imp (T : Triangle ℝ ℝ²) {w₁ w₂ : Fin 3 → ℝ}
    (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1)
    (h : Finset.univ.affineCombination ℝ T.points w₁ =
      Finset.univ.affineCombination ℝ T.points w₂) : w₁ = w₂ := by
  have hind := T.independent.indicator_eq_of_affineCombination_eq
    Finset.univ Finset.univ w₁ w₂ hw₁ hw₂ h
  simpa using hind

private noncomputable def homothetyMap (s : ℝ) (c : ℝ²) : ℝ² →ᵃ[ℝ] ℝ² where
  toFun x := s • x + c
  linear := s • LinearMap.id
  map_vadd' p v := by
    change s • (v + p) + c = s • v + (s • p + c)
    rw [smul_add, add_assoc]

private lemma homothetyMap_injective {s : ℝ} (hs : s ≠ 0) (c : ℝ²) :
    Function.Injective (homothetyMap s c) := by
  intro x y h
  change s • x + c = s • y + c at h
  exact smul_right_injective ℝ² hs (add_right_cancel h)

private noncomputable def subTri (T : Triangle ℝ ℝ²) (s : ℝ) (hs : s ≠ 0)
    (a : Fin 3 → ℝ) : Triangle ℝ ℝ² :=
  T.map (homothetyMap s (∑ i : Fin 3, a i • T.points i)) (homothetyMap_injective hs _)

private lemma subTri_similar (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s ≠ 0) (a : Fin 3 → ℝ) :
    (subTri T s hs a).points ∼ T.points := by
  refine ⟨⟨|s|, abs_nonneg s⟩, ?_, fun i j => ?_⟩
  · intro h
    have h0 : |s| = 0 := congrArg NNReal.toReal h
    exact hs (abs_eq_zero.mp h0)
  · simp only [subTri, Simplex.map_points, Function.comp_apply, homothetyMap, AffineMap.coe_mk]
    rw [edist_dist, edist_dist]
    have hd : dist (s • T.points i + ∑ k : Fin 3, a k • T.points k)
        (s • T.points j + ∑ k : Fin 3, a k • T.points k) =
        |s| * dist (T.points i) (T.points j) := by
      rw [dist_add_right, dist_smul₀, Real.norm_eq_abs]
    rw [hd, ENNReal.ofReal_mul (abs_nonneg s), ENNReal.ofReal_eq_coe_nnreal (abs_nonneg s)]
    rfl

private lemma subTri_affineCombination (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s ≠ 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {u : Fin 3 → ℝ} (hu : ∑ i, u i = 1) :
    Finset.univ.affineCombination ℝ (subTri T s hs a).points u =
      Finset.univ.affineCombination ℝ T.points (fun i => a i + s * u i) := by
  have hw : ∑ i : Fin 3, (a i + s * u i) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hu]
    ring
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hu,
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  simp only [subTri, Simplex.map_points, Function.comp_apply, homothetyMap, AffineMap.coe_mk,
    smul_add, add_smul, Finset.sum_add_distrib]
  have hsmul : ∑ i : Fin 3, u i • ∑ k : Fin 3, a k • T.points k =
      (∑ i : Fin 3, u i) • ∑ k : Fin 3, a k • T.points k :=
    Finset.sum_smul.symm
  rw [hsmul, hu, one_smul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

private lemma mem_subTri_setInterior_iff (I : Set ℝ) (T : Triangle ℝ ℝ²)
    {s : ℝ} (hs : s ≠ 0) {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s hs a).setInterior I ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, (w i - a i) / s ∈ I) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  constructor
  · rintro ⟨u, hu, huI, rfl⟩
    refine ⟨fun i => a i + s * u i, ?_, ?_, (subTri_affineCombination T hs ha hu).symm⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hu]
      ring
    · intro i
      have hdiv : (a i + s * u i - a i) / s = u i := by
        field_simp [hs]
        ring
      rw [hdiv]
      exact huI i
  · rintro ⟨w, hw, hwI, rfl⟩
    let u : Fin 3 → ℝ := fun i => (w i - a i) / s
    have hu : ∑ i : Fin 3, u i = 1 := by
      simp only [u, ← Finset.sum_div, Finset.sum_sub_distrib, hw, ha]
      field_simp [hs]
      ring
    refine ⟨u, hu, hwI, ?_⟩
    rw [subTri_affineCombination T hs ha hu]
    congr 1
    funext i
    simp only [u]
    field_simp [hs]
    ring

private lemma mem_subTri_closedInterior_pos (T : Triangle ℝ ℝ²) {s : ℝ} (hs : 0 < s)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_gt hs) a).closedInterior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, a i ≤ w i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_gt hs) a).setInterior (Set.Icc 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Icc 0 1) T (ne_of_gt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  constructor
  · intro h i
    have h0 : 0 ≤ (w i - a i) / s := (h i).1
    have h1 : 0 ≤ w i - a i := (div_nonneg_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (w 0 - a 0) + (w 1 - a 1) + (w 2 - a 2) = s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 ≤ w 0 - a 0 := sub_nonneg.mpr (h 0)
    have h1 : 0 ≤ w 1 - a 1 := sub_nonneg.mpr (h 1)
    have h2 : 0 ≤ w 2 - a 2 := sub_nonneg.mpr (h 2)
    have hle : w i - a i ≤ s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    exact ⟨div_nonneg (sub_nonneg.mpr (h i)) (le_of_lt hs), (div_le_one hs).mpr hle⟩

private lemma mem_subTri_interior_pos (T : Triangle ℝ ℝ²) {s : ℝ} (hs : 0 < s)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_gt hs) a).interior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, a i < w i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_gt hs) a).setInterior (Set.Ioo 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Ioo 0 1) T (ne_of_gt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  constructor
  · intro h i
    have h0 : 0 < (w i - a i) / s := (h i).1
    have h1 : 0 < w i - a i := (div_pos_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (w 0 - a 0) + (w 1 - a 1) + (w 2 - a 2) = s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 < w 0 - a 0 := sub_pos.mpr (h 0)
    have h1 : 0 < w 1 - a 1 := sub_pos.mpr (h 1)
    have h2 : 0 < w 2 - a 2 := sub_pos.mpr (h 2)
    have hlt : w i - a i < s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    exact ⟨div_pos (sub_pos.mpr (h i)) hs, (div_lt_one hs).mpr hlt⟩

private lemma mem_subTri_closedInterior_neg (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s < 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_lt hs) a).closedInterior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, w i ≤ a i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_lt hs) a).setInterior (Set.Icc 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Icc 0 1) T (ne_of_lt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  have ht : 0 < -s := neg_pos.mpr hs
  constructor
  · intro h i
    have h0 : 0 ≤ (a i - w i) / (-s) := by
      have : (a i - w i) / (-s) = (w i - a i) / s := by field_simp [ne_of_lt hs]; ring
      rw [this]
      exact (h i).1
    have h1 : 0 ≤ a i - w i := (div_nonneg_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (a 0 - w 0) + (a 1 - w 1) + (a 2 - w 2) = -s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 ≤ a 0 - w 0 := sub_nonneg.mpr (h 0)
    have h1 : 0 ≤ a 1 - w 1 := sub_nonneg.mpr (h 1)
    have h2 : 0 ≤ a 2 - w 2 := sub_nonneg.mpr (h 2)
    have hle : a i - w i ≤ -s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    have heq : (w i - a i) / s = (a i - w i) / (-s) := by field_simp [ne_of_lt hs]; ring
    rw [heq]
    exact ⟨div_nonneg (sub_nonneg.mpr (h i)) (le_of_lt ht), (div_le_one ht).mpr hle⟩

private lemma mem_subTri_interior_neg (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s < 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_lt hs) a).interior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, w i < a i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_lt hs) a).setInterior (Set.Ioo 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Ioo 0 1) T (ne_of_lt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  have ht : 0 < -s := neg_pos.mpr hs
  constructor
  · intro h i
    have h0 : 0 < (a i - w i) / (-s) := by
      have : (a i - w i) / (-s) = (w i - a i) / s := by field_simp [ne_of_lt hs]; ring
      rw [this]
      exact (h i).1
    have h1 : 0 < a i - w i := (div_pos_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (a 0 - w 0) + (a 1 - w 1) + (a 2 - w 2) = -s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 < a 0 - w 0 := sub_pos.mpr (h 0)
    have h1 : 0 < a 1 - w 1 := sub_pos.mpr (h 1)
    have h2 : 0 < a 2 - w 2 := sub_pos.mpr (h 2)
    have hlt : a i - w i < -s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    have heq : (w i - a i) / s = (a i - w i) / (-s) := by field_simp [ne_of_lt hs]; ring
    rw [heq]
    exact ⟨div_pos (sub_pos.mpr (h i)) ht, (div_lt_one ht).mpr hlt⟩

private lemma mem_closedInterior_of_nonneg (T : Triangle ℝ ℝ²) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i = 1) (hnn : ∀ i, 0 ≤ w i) :
    Finset.univ.affineCombination ℝ T.points w ∈ T.closedInterior := by
  rw [T.affineCombination_mem_closedInterior_iff hw]
  intro i
  rw [Fin.sum_univ_three] at hw
  have h0 := hnn 0
  have h1 := hnn 1
  have h2 := hnn 2
  refine ⟨hnn i, ?_⟩
  match i with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

private lemma mem_interior_of_pos (T : Triangle ℝ ℝ²) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) :
    Finset.univ.affineCombination ℝ T.points w ∈ T.interior := by
  rw [T.affineCombination_mem_interior_iff hw]
  intro i
  rw [Fin.sum_univ_three] at hw
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  refine ⟨hpos i, ?_⟩
  match i with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

private def StrongSimiliCuttable (n : ℕ) (T : Triangle ℝ ℝ²) : Prop :=
  ∃ Ts : Fin n → Triangle ℝ ℝ²,
    (∀ i, (Ts i).points ∼ T.points) ∧
    (∀ i, (Ts i).interior ⊆ T.interior) ∧
    Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) ∧
    ⋃ i, (Ts i).closedInterior = T.closedInterior

private lemma StrongSimiliCuttable.toIsSimiliCuttable {n : ℕ} {T : Triangle ℝ ℝ²}
    (h : StrongSimiliCuttable n T) : Erdos633.IsSimiliCuttable n T := by
  rcases h with ⟨Ts, hsim, -, hdisj, hunion⟩
  exact ⟨Ts, fun i j => (hsim i).trans (hsim j).symm, hdisj, hunion⟩

private lemma strongSimiliCuttable_one (T : Triangle ℝ ℝ²) : StrongSimiliCuttable 1 T := by
  refine ⟨fun _ => T, fun _ => Similar.refl _, fun _ => Set.Subset.rfl, ?_, ?_⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · ext x
    simp

private lemma strongSimiliCuttable_two_mul (m : ℕ) (hm : 2 ≤ m) (T : Triangle ℝ ℝ²) :
    StrongSimiliCuttable (2 * m) T := by
  let mr : ℝ := (m : ℝ)
  have hmr_pos : 0 < mr := by
    dsimp only [mr]
    exact_mod_cast (by omega : 0 < m)
  have hmr_ge2 : (2 : ℝ) ≤ mr := by
    dsimp only [mr]
    exact_mod_cast hm
  have hs_big_pos : 0 < (mr - 1) / mr := div_pos (by linarith) hmr_pos
  have hs_up_pos : 0 < 1 / mr := div_pos one_pos hmr_pos
  have hs_inv_neg : -1 / mr < 0 := div_neg_of_neg_of_pos (by norm_num) hmr_pos
  let aBig : Fin 3 → ℝ := vec3 (1 / mr) 0 0
  have haBig : ∑ i : Fin 3, aBig i = 1 - (mr - 1) / mr := by
    rw [Fin.sum_univ_three]
    change 1 / mr + 0 + 0 = 1 - (mr - 1) / mr
    field_simp [ne_of_gt hmr_pos]
    ring
  let aUp (j : Fin m) : Fin 3 → ℝ := vec3 0 ((j.1 : ℝ) / mr) ((mr - 1 - (j.1 : ℝ)) / mr)
  have haUp (j : Fin m) : ∑ i : Fin 3, aUp j i = 1 - 1 / mr := by
    rw [Fin.sum_univ_three]
    change 0 + (j.1 : ℝ) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - 1 / mr
    field_simp [ne_of_gt hmr_pos]
    ring
  let aInv (j : Fin (m - 1)) : Fin 3 → ℝ :=
    vec3 (1 / mr) (((j.1 : ℝ) + 1) / mr) ((mr - 1 - (j.1 : ℝ)) / mr)
  have haInv (j : Fin (m - 1)) : ∑ i : Fin 3, aInv j i = 1 - (-1 / mr) := by
    rw [Fin.sum_univ_three]
    change 1 / mr + ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (-1 / mr)
    field_simp [ne_of_gt hmr_pos]
    ring
  let idx := Unit ⊕ Fin m ⊕ Fin (m - 1)
  let tile : idx → Triangle ℝ ℝ²
    | Sum.inl () => subTri T ((mr - 1) / mr) (ne_of_gt hs_big_pos) aBig
    | Sum.inr (Sum.inl j) => subTri T (1 / mr) (ne_of_gt hs_up_pos) (aUp j)
    | Sum.inr (Sum.inr j) => subTri T (-1 / mr) (ne_of_lt hs_inv_neg) (aInv j)
  have hcard : Fintype.card idx = 2 * m := by
    dsimp only [idx]
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_fin]
    omega
  let e : Fin (2 * m) ≃ idx := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => tile (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with ⟨⟩ | j | j
    · exact subTri_similar T (ne_of_gt hs_big_pos) aBig
    · exact subTri_similar T (ne_of_gt hs_up_pos) (aUp j)
    · exact subTri_similar T (ne_of_lt hs_inv_neg) (aInv j)
  · intro i x hx
    dsimp only at hx
    generalize e i = p at hx
    rcases p with ⟨⟩ | j | j
    · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      refine mem_interior_of_pos T hw fun k => ?_
      have hk := hlt k
      match k with
      | 0 =>
        change 1 / mr < w 0 at hk
        linarith [div_pos one_pos hmr_pos]
      | 1 => exact hk
      | 2 => exact hk
    · rw [mem_subTri_interior_pos T hs_up_pos (haUp j)] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      have hj_le : (j.1 : ℝ) ≤ mr - 1 := by
        have h1 : j.1 + 1 ≤ m := j.2
        have h2 : (j.1 : ℝ) + 1 ≤ mr := by dsimp only [mr]; exact_mod_cast h1
        linarith
      refine mem_interior_of_pos T hw fun k => ?_
      have hk := hlt k
      match k with
      | 0 => exact hk
      | 1 =>
        change (j.1 : ℝ) / mr < w 1 at hk
        have hnn : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
        linarith
      | 2 =>
        change (mr - 1 - (j.1 : ℝ)) / mr < w 2 at hk
        have hnn : (0 : ℝ) ≤ (mr - 1 - (j.1 : ℝ)) / mr :=
          div_nonneg (by linarith) (le_of_lt hmr_pos)
        linarith
    · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j)] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      have hj_le : (j.1 : ℝ) + 2 ≤ mr := by
        have h1 : j.1 + 2 ≤ m := by omega
        dsimp only [mr]
        exact_mod_cast h1
      rw [Fin.sum_univ_three] at hw
      have h0 : w 0 < 1 / mr := hlt 0
      have h1 : w 1 < ((j.1 : ℝ) + 1) / mr := hlt 1
      have h2 : w 2 < (mr - 1 - (j.1 : ℝ)) / mr := hlt 2
      have hsum12 : ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hsum02 : 1 / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (j.1 : ℝ) / mr := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hsum01 : 1 / mr + ((j.1 : ℝ) + 1) / mr = 1 - (mr - 2 - (j.1 : ℝ)) / mr := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hnn1 : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
      have hnn2 : (0 : ℝ) ≤ (mr - 2 - (j.1 : ℝ)) / mr :=
        div_nonneg (by linarith) (le_of_lt hmr_pos)
      refine mem_interior_of_pos T (by rw [Fin.sum_univ_three]; exact hw) fun k => ?_
      match k with
      | 0 => linarith
      | 1 => linarith
      | 2 => linarith
  · intro i₁ i₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have he_ne : e i₁ ≠ e i₂ := fun h => hne (e.injective h)
    have hdisj_idx : ∀ p₁ p₂ : idx, p₁ ≠ p₂ →
        x ∈ (tile p₁).interior → x ∈ (tile p₂).interior → False := by
      intro p₁ p₂ hp hx1 hx2
      rcases p₁ with ⟨⟩ | j₁ | j₁ <;> rcases p₂ with ⟨⟩ | j₂ | j₂
      · exact hp rfl
      · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hb0 : 1 / mr < w₁ 0 := h1 0
        have hu1 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have hu2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        have hsum : 1 / mr + (j₂.1 : ℝ) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        linarith
      · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hb0 : 1 / mr < w₁ 0 := h1 0
        have hi0 : w₁ 0 < 1 / mr := h2 0
        linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hb0 : 1 / mr < w₁ 0 := h2 0
        have hu1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have hu2 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have hsum : 1 / mr + (j₁.1 : ℝ) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hjne : j₁.1 ≠ j₂.1 := fun h => hp (by rw [Fin.ext h])
        have h0_1 : 0 < w₁ 0 := h1 0
        have h1_1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have h2_1 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have h1_2 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have h2_2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        rcases lt_or_gt_of_ne hjne with hlt | hgt
        · have hle : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hlt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : ((j₁.1 : ℝ) + 1) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
        · have hle : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : ((j₂.1 : ℝ) + 1) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hu1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have hu2 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have hi1 : w₁ 1 < ((j₂.1 : ℝ) + 1) / mr := h2 1
        have hi2 : w₁ 2 < (mr - 1 - (j₂.1 : ℝ)) / mr := h2 2
        rcases le_or_gt j₁.1 j₂.1 with hle | hgt
        · have hle' : (j₁.1 : ℝ) ≤ (j₂.1 : ℝ) := by exact_mod_cast hle
          have hdiv : (mr - 1 - (j₂.1 : ℝ)) / mr ≤ (mr - 1 - (j₁.1 : ℝ)) / mr :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hmr_pos)
          linarith
        · have hle' : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle' (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hi0 : w₁ 0 < 1 / mr := h1 0
        have hb0 : 1 / mr < w₁ 0 := h2 0
        linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hi1 : w₁ 1 < ((j₁.1 : ℝ) + 1) / mr := h1 1
        have hi2 : w₁ 2 < (mr - 1 - (j₁.1 : ℝ)) / mr := h1 2
        have hu1 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have hu2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        rcases le_or_gt j₂.1 j₁.1 with hle | hgt
        · have hle' : (j₂.1 : ℝ) ≤ (j₁.1 : ℝ) := by exact_mod_cast hle
          have hdiv : (mr - 1 - (j₁.1 : ℝ)) / mr ≤ (mr - 1 - (j₂.1 : ℝ)) / mr :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hmr_pos)
          linarith
        · have hle' : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle' (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hjne : j₁.1 ≠ j₂.1 := fun h => hp (by rw [Fin.ext h])
        have h0_1 : w₁ 0 < 1 / mr := h1 0
        have h1_1 : w₁ 1 < ((j₁.1 : ℝ) + 1) / mr := h1 1
        have h2_1 : w₁ 2 < (mr - 1 - (j₁.1 : ℝ)) / mr := h1 2
        have h1_2 : w₁ 1 < ((j₂.1 : ℝ) + 1) / mr := h2 1
        have h2_2 : w₁ 2 < (mr - 1 - (j₂.1 : ℝ)) / mr := h2 2
        rcases lt_or_gt_of_ne hjne with hlt | hgt
        · have hle : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hlt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : 1 / mr + (j₂.1 : ℝ) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
        · have hle : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : 1 / mr + (j₁.1 : ℝ) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
    exact hdisj_idx (e i₁) (e i₂) he_ne hx₁ hx₂
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      generalize e i = p at hx
      rcases p with ⟨⟩ | j | j
      · rw [mem_subTri_closedInterior_pos T hs_big_pos haBig] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        refine mem_closedInterior_of_nonneg T hw fun k => ?_
        have hk := hle k
        match k with
        | 0 =>
          change 1 / mr ≤ w 0 at hk
          linarith [div_pos one_pos hmr_pos]
        | 1 => exact hk
        | 2 => exact hk
      · rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp j)] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        have hj_le : (j.1 : ℝ) ≤ mr - 1 := by
          have h1 : j.1 + 1 ≤ m := j.2
          have h2 : (j.1 : ℝ) + 1 ≤ mr := by dsimp only [mr]; exact_mod_cast h1
          linarith
        refine mem_closedInterior_of_nonneg T hw fun k => ?_
        have hk := hle k
        match k with
        | 0 => exact hk
        | 1 =>
          change (j.1 : ℝ) / mr ≤ w 1 at hk
          have hnn : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
          linarith
        | 2 =>
          change (mr - 1 - (j.1 : ℝ)) / mr ≤ w 2 at hk
          have hnn : (0 : ℝ) ≤ (mr - 1 - (j.1 : ℝ)) / mr :=
            div_nonneg (by linarith) (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_closedInterior_neg T hs_inv_neg (haInv j)] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        have hj_le : (j.1 : ℝ) + 2 ≤ mr := by
          have h1 : j.1 + 2 ≤ m := by omega
          dsimp only [mr]
          exact_mod_cast h1
        rw [Fin.sum_univ_three] at hw
        have h0 : w 0 ≤ 1 / mr := hle 0
        have h1 : w 1 ≤ ((j.1 : ℝ) + 1) / mr := hle 1
        have h2 : w 2 ≤ (mr - 1 - (j.1 : ℝ)) / mr := hle 2
        have hsum12 : ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hsum02 : 1 / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (j.1 : ℝ) / mr := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hsum01 : 1 / mr + ((j.1 : ℝ) + 1) / mr = 1 - (mr - 2 - (j.1 : ℝ)) / mr := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hnn1 : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
        have hnn2 : (0 : ℝ) ≤ (mr - 2 - (j.1 : ℝ)) / mr :=
          div_nonneg (by linarith) (le_of_lt hmr_pos)
        refine mem_closedInterior_of_nonneg T (by rw [Fin.sum_univ_three]; exact hw) fun k => ?_
        match k with
        | 0 => linarith
        | 1 => linarith
        | 2 => linarith
    · rintro ⟨w, hw, hwI, rfl⟩
      have hw0 : 0 ≤ w 0 := (hwI 0).1
      have hw1 : 0 ≤ w 1 := (hwI 1).1
      have hw2 : 0 ≤ w 2 := (hwI 2).1
      have hw1_le : w 1 ≤ 1 := (hwI 1).2
      have hcover : ∃ p : idx, Finset.univ.affineCombination ℝ T.points w ∈ (tile p).closedInterior := by
        by_cases hbig : 1 / mr ≤ w 0
        · refine ⟨Sum.inl (), ?_⟩
          rw [mem_subTri_closedInterior_pos T hs_big_pos haBig]
          refine ⟨w, hw, fun k => ?_, rfl⟩
          match k with
          | 0 => exact hbig
          | 1 => exact hw1
          | 2 => exact hw2
        · push Not at hbig
          by_cases hw1_eq : w 1 = 1
          · let jlast : Fin m := ⟨m - 1, by omega⟩
            refine ⟨Sum.inr (Sum.inl jlast), ?_⟩
            rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp jlast)]
            have hjlast : (jlast.1 : ℝ) = mr - 1 := by
              dsimp only [jlast, mr]
              rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
            refine ⟨w, hw, fun k => ?_, rfl⟩
            match k with
            | 0 => exact hw0
            | 1 =>
              change (jlast.1 : ℝ) / mr ≤ w 1
              rw [hjlast, hw1_eq]
              exact (div_le_one hmr_pos).mpr (by linarith)
            | 2 =>
              change (mr - 1 - (jlast.1 : ℝ)) / mr ≤ w 2
              rw [hjlast]
              have hzero : (mr - 1 - (mr - 1)) / mr = 0 := by ring
              rw [hzero]
              exact hw2
          · have hw1_lt : w 1 < 1 := lt_of_le_of_ne hw1_le hw1_eq
            let jnat : ℕ := Nat.floor (mr * w 1)
            have hjnat_lt : jnat < m := by
              have hlt : mr * w 1 < mr := by nlinarith
              have hlt' : mr * w 1 < (m : ℝ) := hlt
              exact (Nat.floor_lt (mul_nonneg (le_of_lt hmr_pos) hw1)).mpr hlt'
            have hjnat_le : (jnat : ℝ) ≤ mr * w 1 :=
              Nat.floor_le (mul_nonneg (le_of_lt hmr_pos) hw1)
            have hjnat_gt : mr * w 1 < (jnat : ℝ) + 1 := Nat.lt_floor_add_one (mr * w 1)
            have hw1_lo : (jnat : ℝ) / mr ≤ w 1 := (div_le_iff₀ hmr_pos).mpr (by linarith)
            have hw1_hi : w 1 ≤ ((jnat : ℝ) + 1) / mr := (le_div_iff₀ hmr_pos).mpr (by linarith)
            by_cases hup : (mr - 1 - (jnat : ℝ)) / mr ≤ w 2
            · refine ⟨Sum.inr (Sum.inl ⟨jnat, hjnat_lt⟩), ?_⟩
              rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp ⟨jnat, hjnat_lt⟩)]
              refine ⟨w, hw, fun k => ?_, rfl⟩
              match k with
              | 0 => exact hw0
              | 1 => exact hw1_lo
              | 2 => exact hup
            · push Not at hup
              have hjnat_lt' : jnat < m - 1 := by
                by_contra hge
                have hjeq : jnat = m - 1 := by omega
                have hjr : (jnat : ℝ) = mr - 1 := by
                  rw [hjeq, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
                rw [hjr] at hup
                have hzero : (mr - 1 - (mr - 1)) / mr = 0 := by ring
                linarith
              refine ⟨Sum.inr (Sum.inr ⟨jnat, hjnat_lt'⟩), ?_⟩
              rw [mem_subTri_closedInterior_neg T hs_inv_neg (haInv ⟨jnat, hjnat_lt'⟩)]
              refine ⟨w, hw, fun k => ?_, rfl⟩
              match k with
              | 0 => exact le_of_lt hbig
              | 1 => exact hw1_hi
              | 2 => exact le_of_lt hup
      rcases hcover with ⟨p, hp⟩
      exact ⟨e.symm p, by simpa using hp⟩

private lemma strongSimiliCuttable_add_three {n : ℕ} (hn : 1 ≤ n) {T : Triangle ℝ ℝ²}
    (h : StrongSimiliCuttable n T) : StrongSimiliCuttable (n + 3) T := by
  rcases h with ⟨Ts, hsim, hint, hdisj, hunion⟩
  let i0 : Fin n := ⟨0, by omega⟩
  obtain ⟨Us, hUsim, hUint, hUdisj, hUunion⟩ := strongSimiliCuttable_two_mul 2 (le_refl 2) (Ts i0)
  let idx := Fin 4 ⊕ Fin (n - 1)
  let tile : idx → Triangle ℝ ℝ²
    | Sum.inl k => Us k
    | Sum.inr j => Ts ⟨j.1 + 1, by omega⟩
  have hcard : Fintype.card idx = n + 3 := by
    dsimp only [idx]
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega
  let e : Fin (n + 3) ≃ idx := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => tile (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with k | j
    · exact (hUsim k).trans (hsim i0)
    · exact hsim ⟨j.1 + 1, by omega⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with k | j
    · exact (hUint k).trans (hint i0)
    · exact hint ⟨j.1 + 1, by omega⟩
  · intro i₁ i₂ hne
    dsimp only
    have he_ne : e i₁ ≠ e i₂ := fun h => hne (e.injective h)
    generalize e i₁ = p₁ at he_ne ⊢
    generalize e i₂ = p₂ at he_ne ⊢
    rcases p₁ with k₁ | j₁ <;> rcases p₂ with k₂ | j₂
    · have hk : k₁ ≠ k₂ := fun h => he_ne (by rw [h])
      exact hUdisj hk
    · have hne' : i0 ≠ ⟨j₂.1 + 1, by omega⟩ := by
        intro heq
        have : (0 : ℕ) = j₂.1 + 1 := congrArg Fin.val heq
        omega
      exact (hdisj hne').mono_left (hUint k₁)
    · have hne' : (⟨j₁.1 + 1, by omega⟩ : Fin n) ≠ i0 := by
        intro heq
        have : j₁.1 + 1 = 0 := congrArg Fin.val heq
        omega
      exact (hdisj hne').mono_right (hUint k₂)
    · have hj : (⟨j₁.1 + 1, by omega⟩ : Fin n) ≠ ⟨j₂.1 + 1, by omega⟩ := by
        intro heq
        have hval : j₁.1 = j₂.1 := by
          have : j₁.1 + 1 = j₂.1 + 1 := congrArg Fin.val heq
          omega
        exact he_ne (by rw [Fin.ext hval])
      exact hdisj hj
  · rw [← hunion]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      generalize e i = p at hx
      rcases p with k | j
      · refine ⟨i0, ?_⟩
        rw [← hUunion]
        exact Set.mem_iUnion.mpr ⟨k, hx⟩
      · exact ⟨⟨j.1 + 1, by omega⟩, hx⟩
    · rintro ⟨j, hx⟩
      by_cases hj : j.1 = 0
      · have hjeq : j = i0 := Fin.ext hj
        rw [hjeq, ← hUunion] at hx
        rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
        exact ⟨e.symm (Sum.inl k), by simpa [tile] using hk⟩
      · let j' : Fin (n - 1) := ⟨j.1 - 1, by omega⟩
        have hjeq : (⟨j'.1 + 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp [j']; omega)
        refine ⟨e.symm (Sum.inr j'), ?_⟩
        simpa [tile, hjeq] using hx

end Erdos633SimiliCuttableProof

theorem OMA.solution : type_of% @Erdos633.IsSimiliCuttable.of_ne_zero_two_three_five := by
  intro n T hn₀ hn₂ hn₃ hn₅
  by_cases hn1 : n = 1
  · subst hn1
    exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_one T).toIsSimiliCuttable
  · by_cases heven : n % 2 = 0
    · have hm : 2 ≤ n / 2 := by omega
      have heq : 2 * (n / 2) = n := by omega
      rw [← heq]
      exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_two_mul (n / 2) hm T).toIsSimiliCuttable
    · have hge7 : 7 ≤ n := by omega
      have hsub_even : (n - 3) % 2 = 0 := by omega
      have hm : 2 ≤ (n - 3) / 2 := by omega
      have heq1 : 2 * ((n - 3) / 2) = n - 3 := by omega
      have heq2 : (n - 3) + 3 = n := by omega
      have hbase : Erdos633SimiliCuttableProof.StrongSimiliCuttable (n - 3) T := by
        rw [← heq1]
        exact Erdos633SimiliCuttableProof.strongSimiliCuttable_two_mul ((n - 3) / 2) hm T
      rw [← heq2]
      exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_add_three (by omega) hbase).toIsSimiliCuttable
