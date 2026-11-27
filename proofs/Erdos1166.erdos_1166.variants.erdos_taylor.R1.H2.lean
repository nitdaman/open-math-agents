import OMAReductions.R_Erdos1166_erdos_1166_variants_erdos_taylor_R1

-- Step Erdos1166.erdos_1166.variants.erdos_taylor.R1.H2: hypothesis H2 of reduction Erdos1166.erdos_1166.variants.erdos_taylor.R1
-- Credit: @koolkao

-- Proof: the site of maximal local time is first visited at some time j <= n; the walk restarted at j
-- returns to its start at least k times by time n. The first n steps after j have the same joint law
-- as the first n steps (product of equal marginals), so a union bound over j = 0..n gives the claim.

open MeasureTheory
open scoped ProbabilityTheory ENNReal
open Erdos1165 Erdos1166

namespace OMA.H2Proof

lemma position_congr {Ω Ω' : Type*} {X : ℕ → Ω → ℤ × ℤ} {Y : ℕ → Ω' → ℤ × ℤ} {ω : Ω} {ω' : Ω'}
    {n m : ℕ} (h : ∀ i < n, X i ω = Y i ω') (hm : m ≤ n) :
    position X m ω = position Y m ω' :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

lemma localTime_congr {Ω Ω' : Type*} {X : ℕ → Ω → ℤ × ℤ} {Y : ℕ → Ω' → ℤ × ℤ} {ω : Ω}
    {ω' : Ω'} {n : ℕ} (x : ℤ × ℤ) (h : ∀ i < n, X i ω = Y i ω') :
    localTime X n ω x = localTime Y n ω' x := by
  unfold localTime
  congr 1
  refine Finset.filter_congr fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  rw [position_congr h (by omega)]

lemma position_shift {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (j m : ℕ) :
    position X (j + m) ω = position X j ω + position (fun i ↦ X (j + i)) m ω :=
  Finset.sum_range_add _ _ _

lemma subset_union {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n k : ℕ) :
    {ω | k ≤ maxLocalTime X n ω} ⊆
      ⋃ j ∈ Finset.range (n + 1), {ω | k ≤ localTime (fun i ↦ X (j + i)) n ω 0} := by
  intro ω hω
  rw [Set.mem_setOf_eq] at hω
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup (Finset.range (n + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩ fun k ↦ localTime X n ω (position X k ω)
  set x := position X i ω with hx
  set A := (Finset.range (n + 1)).filter fun m ↦ position X m ω = x with hA
  have hiA : i ∈ A := Finset.mem_filter.mpr ⟨hi, rfl⟩
  have hne : A.Nonempty := ⟨i, hiA⟩
  set j := A.min' hne with hj
  have hjA : j ∈ A := Finset.min'_mem A hne
  have hjA' := Finset.mem_filter.mp hjA
  have hjn : j < n + 1 := Finset.mem_range.mp hjA'.1
  refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjn, ?_⟩
  rw [Set.mem_setOf_eq]
  have hk : k ≤ A.card := by
    have : maxLocalTime X n ω = A.card := hmax
    omega
  refine hk.trans (Finset.card_le_card_of_injOn (fun a ↦ a - j) ?_ ?_)
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hja : j ≤ a := Finset.min'_le A a ha
    have han : a < n + 1 := Finset.mem_range.mp ha'.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (show a - j < n + 1 by omega), ?_⟩
    have hs := position_shift X ω j (a - j)
    rw [show j + (a - j) = a by omega] at hs
    have e : position (fun i ↦ X (j + i)) (a - j) ω = position X a ω - position X j ω := by
      rw [hs]
      abel
    rw [e, ha'.2, hjA'.2, sub_self]
  · intro a ha b hb hab
    have hja : j ≤ a := Finset.min'_le A a ha
    have hjb : j ≤ b := Finset.min'_le A b hb
    have hab' : a - j = b - j := hab
    omega

/-- The restriction of the steps to a finite window, extended by zero. -/
def window (n : ℕ) (i : ℕ) (y : Fin n → ℤ × ℤ) : ℤ × ℤ :=
  if h : i < n then y ⟨i, h⟩ else 0

lemma map_window {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    Measure.map (fun ω (i : Fin n) ↦ X (j + i) ω) ℙ =
      Measure.pi (fun _ : Fin n ↦ Measure.map (X 0) ℙ) := by
  have hind : ProbabilityTheory.iIndepFun (fun i : Fin n ↦ X (j + i)) ℙ :=
    hX.indep.precomp (g := fun i : Fin n ↦ j + (i : ℕ)) fun a b h ↦ Fin.ext (by simpa using h)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    fun i ↦ (hX.measurable _).aemeasurable).mp hind]
  congr 1
  funext i
  exact Eq.trans (hX.isUniform (j + i)) (Eq.symm (hX.isUniform 0))

lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n k j : ℕ) :
    ℙ {ω | k ≤ localTime (fun i ↦ X (j + i)) n ω 0} = ℙ {ω | k ≤ localTime X n ω 0} := by
  set T : Set (Fin n → ℤ × ℤ) := {y | k ≤ localTime (fun i y ↦ window n i y) n y 0} with hT
  have hTm : MeasurableSet T := (Set.to_countable T).measurableSet
  have hpre : ∀ j', {ω | k ≤ localTime (fun i ↦ X (j' + i)) n ω 0} =
      (fun ω (i : Fin n) ↦ X (j' + i) ω) ⁻¹' T := by
    intro j'
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hT]
    rw [localTime_congr 0 (Y := fun i y ↦ window n i y) (ω' := fun i : Fin n ↦ X (j' + i) ω)
      fun i hi ↦ by simp [window, hi]]
  have hmeas : ∀ j', Measurable (fun ω (i : Fin n) ↦ X (j' + i) ω) := fun j' ↦
    measurable_pi_iff.mpr fun i ↦ hX.measurable _
  have h0 : {ω | k ≤ localTime X n ω 0} = {ω | k ≤ localTime (fun i ↦ X (0 + i)) n ω 0} := by
    simp only [Nat.zero_add]
  rw [h0, hpre, hpre, ← Measure.map_apply (hmeas j) hTm, ← Measure.map_apply (hmeas 0) hTm,
    map_window hX, map_window hX]

theorem h2 : OMA.R_Erdos1166_erdos_1166_variants_erdos_taylor_R1.H2 := by
  intro Ω _ _ X hX n k
  calc ℙ {ω | k ≤ maxLocalTime X n ω}
      ≤ ℙ (⋃ j ∈ Finset.range (n + 1), {ω | k ≤ localTime (fun i ↦ X (j + i)) n ω 0}) :=
        measure_mono (subset_union X n k)
    _ ≤ ∑ j ∈ Finset.range (n + 1), ℙ {ω | k ≤ localTime (fun i ↦ X (j + i)) n ω 0} :=
        measure_biUnion_finset_le _ _
    _ = ∑ _j ∈ Finset.range (n + 1), ℙ {ω | k ≤ localTime X n ω 0} :=
        Finset.sum_congr rfl fun j _ ↦ prob_shift hX n k j
    _ = ((n : ℝ≥0∞) + 1) * ℙ {ω | k ≤ localTime X n ω 0} := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

end OMA.H2Proof

theorem OMA.solution : OMA.R_Erdos1166_erdos_1166_variants_erdos_taylor_R1.H2 := by
  exact OMA.H2Proof.h2

