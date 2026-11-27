import FormalConjectures.ErdosProblems.«501»

/-! Construct finite independent sets above any prescribed lower bound. -/

open Set MeasureTheory
open scoped ENNReal

theorem OMA.solution : type_of% @Erdos501.erdos_501.variants.erdosHajnal_finite := by
  classical
  intro n A hBound hMeasure
  let B (t : ℝ) (m : ℕ) : Set ℝ :=
    {x | t < x ∧ x < (m : ℝ) ∧ ∀ z ∈ A x, z < (m : ℝ)}
  have monoB (t : ℝ) : Monotone (B t) := by
    intro i j hij x hx
    have hle : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact ⟨hx.1, hx.2.1.trans_le hle, fun z hz => (hx.2.2 z hz).trans_le hle⟩
  have unionB (t : ℝ) : (⋃ m, B t m) = Ioi t := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      exact hm.1
    · intro hx
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp (hBound x)
      obtain ⟨m, hm⟩ := exists_nat_gt (max x R)
      apply Set.mem_iUnion.mpr
      refine ⟨m, hx, (le_max_left x R).trans_lt hm, ?_⟩
      intro z hz
      have habs : |z| ≤ R := by
        simpa [Real.dist_eq] using Metric.mem_closedBall.mp (hR hz)
      exact ((le_abs_self z).trans habs).trans_lt ((le_max_right x R).trans_lt hm)
  have largeB (t : ℝ) (k : ℕ) : ∃ m : ℕ, (k : ℝ≥0∞) < volume (B t m) := by
    have hsup : (⨆ m, volume (B t m)) = ∞ := by
      rw [← (monoB t).measure_iUnion, unionB, Real.volume_Ioi]
    by_contra! h
    have hle := iSup_le h
    rw [hsup] at hle
    exact (not_le_of_gt (ENNReal.natCast_lt_top k)) hle
  have above (k : ℕ) (t : ℝ) : ∃ X : Finset ℝ, X.card = k ∧
      (∀ x ∈ X, t < x) ∧ (X : Set ℝ).Pairwise (fun x y => x ∉ A y) := by
    induction k generalizing t with
    | zero => exact ⟨∅, by simp⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ := largeB t k
      obtain ⟨Y, hYcard, hYabove, hYindep⟩ := ih (m : ℝ)
      have hUnion : volume (⋃ y ∈ Y, A y) ≤ (k : ℝ≥0∞) := by
        calc
          volume (⋃ y ∈ Y, A y) ≤ ∑ y ∈ Y, volume (A y) :=
            measure_biUnion_finset_le Y A
          _ ≤ ∑ y ∈ Y, (1 : ℝ≥0∞) := Finset.sum_le_sum (fun y _ => (hMeasure y).le)
          _ = (k : ℝ≥0∞) := by simp [hYcard]
      obtain ⟨x, hx, hxAvoid⟩ := Set.not_subset.mp
        (fun (hSub : B t m ⊆ ⋃ y ∈ Y, A y) => (not_le_of_gt hm) ((measure_mono hSub).trans hUnion))
      have hxNew : x ∉ Y := fun hxy => (not_lt_of_ge (hYabove x hxy).le) hx.2.1
      refine ⟨insert x Y, by simp [hxNew, hYcard], ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx.1
        · exact hx.1.trans (hx.2.1.trans (hYabove z hz))
      · rw [Finset.coe_insert, Set.pairwise_insert]
        refine ⟨hYindep, fun y hy _ => ⟨?_, ?_⟩⟩
        · exact fun hxy => hxAvoid (Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hxy⟩⟩)
        · exact fun hyx => (not_lt_of_ge (hYabove y hy).le) (hx.2.2 y hyx)
  obtain ⟨X, hX, _, hIndep⟩ := above n 0
  exact ⟨X, hX.ge, hIndep⟩