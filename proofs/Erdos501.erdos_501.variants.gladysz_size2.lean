import FormalConjectures.ErdosProblems.«501»

/-! The two sections of a Borel set yield incompatible bounds by Tonelli's theorem. -/

open Set MeasureTheory
open scoped ENNReal

theorem OMA.solution : type_of% @Erdos501.erdos_501.variants.gladysz_size2 := by
  classical
  intro A hclosed hvolume
  suffices ∃ x y : ℝ, x ≠ y ∧ x ∉ A y ∧ y ∉ A x by
    obtain ⟨x, y, hne, hxy, hyx⟩ := this
    refine ⟨{x, y}, (Set.ncard_pair hne).ge, ?_⟩
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hxy
    · exact hyx
    · exact (hab rfl).elim

  by_contra hbad
  let D (x : ℝ) : Set ℝ := insert x (A x)
  have hDclosed (x : ℝ) : IsClosed (D x) := by
    change IsClosed (insert x (A x))
    rw [← Set.singleton_union]
    exact isClosed_singleton.union (hclosed x)
  have horient {x y : ℝ} (hy : y ∉ D x) : x ∈ D y := by
    by_contra hx
    apply hbad
    refine ⟨x, y, fun h ↦ hy (Set.mem_insert_iff.mpr (Or.inl h.symm)), ?_, ?_⟩
    · exact fun h ↦ hx (Set.mem_insert_iff.mpr (Or.inr h))
    · exact fun h ↦ hy (Set.mem_insert_iff.mpr (Or.inr h))

  let interval (i : ℚ × ℚ) : Set ℝ := Ioo (i.1 : ℝ) (i.2 : ℝ)
  let left (i : ℚ × ℚ) : Set ℝ := closure {x | interval i ⊆ (D x)ᶜ}
  let B : Set (ℝ × ℝ) := ⋃ i : ℚ × ℚ, left i ×ˢ interval i
  have hB : MeasurableSet B :=
    MeasurableSet.iUnion fun _ ↦ isClosed_closure.measurableSet.prod measurableSet_Ioo
  have hHorizontal (y : ℝ) : (fun x : ℝ ↦ (x, y)) ⁻¹' B ⊆ D y := by
    intro x hx
    have hx' : (x, y) ∈ B := hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
    have hi' : x ∈ left i ∧ y ∈ interval i := hi
    have hsub : {z | interval i ⊆ (D z)ᶜ} ⊆ D y := fun z hz ↦
      horient (hz hi'.2)
    exact closure_minimal hsub (hDclosed y) hi'.1
  have hVertical (x : ℝ) : (D x)ᶜ ⊆ Prod.mk x ⁻¹' B := by
    intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hDclosed x).isOpen_compl y hy
    obtain ⟨a, hay, ha⟩ := exists_rat_btwn (show y - ε < y by linarith)
    obtain ⟨b, hb, hby⟩ := exists_rat_btwn (show y < y + ε by linarith)
    have hsub : interval (a, b) ⊆ (D x)ᶜ := by
      intro z hz
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      change (a : ℝ) < z ∧ z < (b : ℝ) at hz
      constructor <;> linarith [hz.1, hz.2]
    exact Set.mem_iUnion.mpr ⟨(a, b), ⟨subset_closure hsub, ⟨ha, hb⟩⟩⟩

  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 3)
  have hμ : μ univ = 3 := by norm_num [μ, Measure.restrict_apply, Real.volume_Icc]
  have hDsmall (x : ℝ) : μ (D x) ≤ 1 := by
    have hvol : volume (D x) ≤ volume (A x) := by
      change volume (insert x (A x)) ≤ volume (A x)
      rw [← Set.singleton_union]
      exact (measure_union_le _ _).trans_eq (by simp)
    exact (Measure.restrict_le_self (s := Icc (0 : ℝ) 3) (μ := volume) (D x)).trans
      (hvol.trans (hvolume x).le)
  have hDlarge (x : ℝ) : (2 : ℝ≥0∞) ≤ μ ((D x)ᶜ) := by
    have hsplit := measure_add_measure_compl (μ := μ) (hDclosed x).measurableSet
    have hsum : (3 : ℝ≥0∞) ≤ μ ((D x)ᶜ) + 1 := by
      rw [← hμ, ← hsplit, add_comm (μ ((D x)ᶜ))]
      exact add_le_add (hDsmall x) le_rfl
    calc
      (2 : ℝ≥0∞) = 3 - 1 := by
        rw [show (3 : ℝ≥0∞) = 2 + 1 by norm_num]
        exact (ENNReal.add_sub_cancel_right ENNReal.one_ne_top).symm
      _ ≤ μ ((D x)ᶜ) := tsub_le_iff_right.mpr hsum
  have hLower : (6 : ℝ≥0∞) ≤ μ.prod μ B := by
    rw [Measure.prod_apply hB]
    calc
      (6 : ℝ≥0∞) = ∫⁻ _x, (2 : ℝ≥0∞) ∂μ := by norm_num [lintegral_const, hμ]
      _ ≤ _ := lintegral_mono fun x ↦ (hDlarge x).trans (measure_mono (hVertical x))
  have hUpper : μ.prod μ B ≤ 3 := by
    rw [Measure.prod_apply_symm hB]
    calc
      _ ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂μ :=
        lintegral_mono fun y ↦ (measure_mono (hHorizontal y)).trans (hDsmall y)
      _ = 3 := by simp [lintegral_const, hμ]
  have hcontra := hLower.trans hUpper
  norm_num at hcontra