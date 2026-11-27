import FormalConjectures.ErdosProblems.«501»

/-! Hechler's counterexample uses a well-order of the reals with countable initial segments. -/

open Set MeasureTheory
open scoped Cardinal ENNReal

universe u

theorem OMA.hechler_CH_in_type_zero (h : (ℵ₁ : Cardinal.{u}) = 𝔠) :
    (ℵ₁ : Cardinal.{0}) = 𝔠 := by
  have hlift : Cardinal.lift.{u} (ℵ₁ : Cardinal.{0}) =
      Cardinal.lift.{u} (𝔠 : Cardinal.{0}) := by
    simpa only [Cardinal.lift_aleph, Ordinal.lift_one, Cardinal.lift_continuum] using h
  exact Cardinal.lift_inj.mp hlift

theorem OMA.solution : type_of% @Erdos501.erdos_501.variants.hechler_CH := by
  classical
  intro hCH
  let α := (ℵ₁ : Cardinal).ord.ToType
  have hcard : #ℝ = #α := by
    change #ℝ = #((ℵ₁ : Cardinal).ord.ToType)
    rw [Cardinal.mk_real, Cardinal.mk_toType, Cardinal.card_ord]
    exact (OMA.hechler_CH_in_type_zero hCH).symm
  obtain ⟨e⟩ := Cardinal.eq.mp hcard
  let level (x : ℝ) : ℕ := ⌈|x|⌉₊
  let A (x : ℝ) : Set ℝ := {y | e y < e x ∧ level y ≤ level x}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mpr ⟨(level x : ℝ), ?_⟩
    intro y hy
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact (Nat.le_ceil |y|).trans (by exact_mod_cast hy.2)
  · intro x
    have hiio : (Iio (e x)).Countable := by
      apply Cardinal.le_aleph0_iff_set_countable.mp
      apply Cardinal.lt_aleph_one_iff.mp
      have hlt := Cardinal.mk_Iio_lt (e x) (by simp [α])
      simpa [α, Cardinal.mk_toType] using hlt
    have hA : (A x).Countable :=
      (hiio.preimage e.injective).mono (fun y hy => hy.1)
    change volume (A x) < 1
    rw [hA.measure_zero volume]
    norm_num
  · rintro ⟨X, hX, hIndep⟩
    have decreases {x y : ℝ} (hx : x ∈ X) (hy : y ∈ X) (hxy : e x < e y) :
        level y < level x := by
      apply lt_of_not_ge
      intro hle
      exact hIndep hx hy (fun h => hxy.ne (congrArg e h)) ⟨hxy, hle⟩
    obtain ⟨i, hi, hmin⟩ := (wellFounded_lt (α := α)).has_min (e '' X) (hX.nonempty.image e)
    obtain ⟨x₀, hx₀, rfl⟩ := hi
    have hmaps : MapsTo level X (Iic (level x₀)) := by
      intro x hx
      by_cases hxx : x = x₀
      · subst x
        exact Set.mem_Iic.mpr le_rfl
      have hinj : e x₀ ≠ e x := fun h => hxx (e.injective h).symm
      have hle : e x₀ ≤ e x := le_of_not_gt (hmin _ (mem_image_of_mem e hx))
      exact (decreases hx₀ hx (lt_of_le_of_ne hle hinj)).le
    have hinj : InjOn level X := by
      intro x hx y hy hxy
      by_contra hne
      rcases lt_or_gt_of_ne (fun h => hne (e.injective h)) with h | h
      · exact (decreases hx hy h).ne hxy.symm
      · exact (decreases hy hx h).ne hxy
    exact hX (Set.Finite.of_injOn hmaps hinj (Set.finite_Iic (level x₀)))