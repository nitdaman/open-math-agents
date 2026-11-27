import FormalConjectures.Books.UniformDistributionOfSequences.Equidistribution

-- Problem: Equidistributed Sequences — isAccumulationPoint three halves pow infinite
-- Upstream: formal-conjectures FormalConjectures/Books/UniformDistributionOfSequences/Equidistribution.lean:104 (declaration Equidistribution.isAccumulationPoint_three_halves_pow_infinite)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# `(3/2)^n` has infinitely many accumulation points modulo `1` (Vijayaraghavan)

Write `f n` for the fractional part of `(3/2)^n` and `S` for its set of accumulation points.
Suppose `S` is finite.

* Compactness: for every `ε > 0`, all but finitely many `f n` are within `ε` of some point of
  `S`. Otherwise infinitely many `f n` (pairwise distinct, in `[0, 1]`) stay `ε` away from
  `S`; they have an accumulation point, which lies in `S` and is within `ε` of one of them.
* Arithmetic: `2 * f (n + 1) - 3 * f n` is an integer. The finitely many numbers
  `2 * β - 3 * α` with `α, β ∈ S` are uniformly separated from the integers they are not
  equal to. So if `s n ∈ S` is within a small `ε` of `f n`, the integer
  `2 * f (n + 1) - 3 * f n` must equal `2 * s (n + 1) - 3 * s n`, that is
  `f (n + 1) - s (n + 1) = 3 / 2 * (f n - s n)` for all large `n`.
* The error `f n - s n` is bounded and is multiplied by `3 / 2` at each step, so it is `0`
  from some point on: `f n ∈ S` for all large `n`. But the `f n` are pairwise distinct and
  `S` is finite, a contradiction.
-/

namespace OMAaux

/-- Around any real number, integers other than the number itself keep a positive distance. -/
lemma sep_one (d : ℝ) : ∃ δ > 0, ∀ m : ℤ, |(m : ℝ) - d| < δ → (m : ℝ) = d := by
  by_cases h : Int.fract d = 0
  · refine ⟨1, one_pos, fun m hm => ?_⟩
    have hd : d = (⌊d⌋ : ℝ) := by
      have h1 := Int.floor_add_fract d
      rw [h, add_zero] at h1
      exact h1.symm
    rw [hd] at hm
    have h2 : |((m - ⌊d⌋ : ℤ) : ℝ)| < 1 := by
      push_cast
      exact hm
    have h3 : |m - ⌊d⌋| < 1 := by exact_mod_cast h2
    have h4 : m - ⌊d⌋ = 0 := Int.abs_lt_one_iff.mp h3
    have h5 : m = ⌊d⌋ := by omega
    rw [hd, h5]
  · have h0 : 0 < Int.fract d := lt_of_le_of_ne (Int.fract_nonneg d) (Ne.symm h)
    have h1 : Int.fract d < 1 := Int.fract_lt_one d
    refine ⟨min (Int.fract d) (1 - Int.fract d), lt_min h0 (by linarith), fun m hm => ?_⟩
    exfalso
    have hd : (⌊d⌋ : ℝ) + Int.fract d = d := Int.floor_add_fract d
    rcases le_or_gt m ⌊d⌋ with hle | hgt
    · have h2 : (m : ℝ) ≤ ⌊d⌋ := by exact_mod_cast hle
      have h3 : Int.fract d ≤ |(m : ℝ) - d| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      exact absurd (lt_of_lt_of_le hm (min_le_left _ _)) (not_lt.mpr h3)
    · have h2 : (⌊d⌋ : ℝ) + 1 ≤ m := by exact_mod_cast hgt
      have h3 : 1 - Int.fract d ≤ |(m : ℝ) - d| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      exact absurd (lt_of_lt_of_le hm (min_le_right _ _)) (not_lt.mpr h3)

/-- A uniform version of `sep_one` for finitely many real numbers. -/
lemma exists_sep (T : Finset ℝ) :
    ∃ δ > 0, ∀ d ∈ T, ∀ m : ℤ, |(m : ℝ) - d| < δ → (m : ℝ) = d := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a T ha ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    obtain ⟨δa, hδa, ha'⟩ := sep_one a
    refine ⟨min δ δa, lt_min hδ hδa, ?_⟩
    intro d hd m hm
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact ha' m (lt_of_lt_of_le hm (min_le_right _ _))
    · exact h d hd m (lt_of_lt_of_le hm (min_le_left _ _))

/-- An injective sequence in `[0, 1]` is eventually within `ε` of its accumulation points. -/
lemma eventually_near (f : ℕ → ℝ) (hinj : Function.Injective f)
    (h01 : ∀ n, f n ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ s, Equidistribution.IsAccumulationPoint s f ∧ |f n - s| < ε := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hB := Nat.frequently_atTop_iff_infinite.mp hcon
  have hinf := hB.image hinj.injOn
  have hsub : f '' {n : ℕ | ¬∃ s, Equidistribution.IsAccumulationPoint s f ∧ |f n - s| < ε} ⊆
      Set.Icc 0 1 := by
    rintro _ ⟨n, -, rfl⟩
    exact h01 n
  obtain ⟨x, -, hx⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc hsub
  have hx' := mem_closure_iff_clusterPt.2 (accPt_principal_iff_clusterPt.1 hx)
  have hxS : Equidistribution.IsAccumulationPoint x f :=
    closure_mono (Set.sdiff_subset_sdiff_left (Set.image_subset_range f _)) hx'
  obtain ⟨b, ⟨⟨n, hn, rfl⟩, -⟩, hb⟩ := Metric.mem_closure_iff.mp hx' ε hε
  apply hn
  refine ⟨x, hxS, ?_⟩
  rw [← Real.dist_eq, dist_comm]
  exact hb

/-- `2 * {(3/2)^(n+1)} - 3 * {(3/2)^n}` is an integer. -/
lemma two_mul_sub (n : ℕ) :
    ∃ m : ℤ, 2 * Int.fract ((3 / 2 : ℝ) ^ (n + 1)) - 3 * Int.fract ((3 / 2 : ℝ) ^ n) = m := by
  refine ⟨3 * ⌊(3 / 2 : ℝ) ^ n⌋ - 2 * ⌊(3 / 2 : ℝ) ^ (n + 1)⌋, ?_⟩
  have h1 := Int.floor_add_fract ((3 / 2 : ℝ) ^ (n + 1))
  have h2 := Int.floor_add_fract ((3 / 2 : ℝ) ^ n)
  have h3 : (3 / 2 : ℝ) ^ (n + 1) = (3 / 2) ^ n * (3 / 2) := pow_succ _ _
  push_cast
  linarith

end OMAaux

theorem OMA.solution :
    type_of% @Equidistribution.isAccumulationPoint_three_halves_pow_infinite := by
  by_contra hfin'
  have hfin := Set.not_infinite.mp hfin'
  have hinj := Equidistribution.fract_three_halves_pow_injective
  have h01 : ∀ n : ℕ, Int.fract ((3 / 2 : ℝ) ^ n) ∈ Set.Icc (0 : ℝ) 1 :=
    fun n => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  -- the finitely many numbers `2 * β - 3 * α` are separated from the integers
  obtain ⟨δ, hδ, hsep⟩ := OMAaux.exists_sep
    ((hfin.toFinset ×ˢ hfin.toFinset).image fun p : ℝ × ℝ => 2 * p.2 - 3 * p.1)
  -- from some `N` on, every term is within `δ / 5` of an accumulation point `s n`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (OMAaux.eventually_near _ hinj h01 (δ / 5) (by positivity))
  choose! s hs using hN
  -- the error is multiplied by `3 / 2` at each step
  have hrec : ∀ n, N ≤ n →
      Int.fract ((3 / 2 : ℝ) ^ (n + 1)) - s (n + 1) =
        3 / 2 * (Int.fract ((3 / 2 : ℝ) ^ n) - s n) := by
    intro n hn
    obtain ⟨m, hm⟩ := OMAaux.two_mul_sub n
    have h1 := hs n hn
    have h2 := hs (n + 1) (by omega)
    have hd : 2 * s (n + 1) - 3 * s n ∈
        (hfin.toFinset ×ˢ hfin.toFinset).image fun p : ℝ × ℝ => 2 * p.2 - 3 * p.1 := by
      refine Finset.mem_image.mpr ⟨(s n, s (n + 1)), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨hfin.mem_toFinset.mpr h1.1, hfin.mem_toFinset.mpr h2.1⟩
    have habs : |(m : ℝ) - (2 * s (n + 1) - 3 * s n)| < δ := by
      have t1 := abs_lt.mp h1.2
      have t2 := abs_lt.mp h2.2
      rw [abs_lt]
      constructor <;> linarith
    have heq := hsep _ hd m habs
    linarith
  have hpow : ∀ j : ℕ, Int.fract ((3 / 2 : ℝ) ^ (N + j)) - s (N + j) =
      (3 / 2) ^ j * (Int.fract ((3 / 2 : ℝ) ^ N) - s N) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← add_assoc, hrec (N + j) (by omega), ih, pow_succ]
      ring
  -- a bounded error that grows geometrically is zero
  have hzero : Int.fract ((3 / 2 : ℝ) ^ N) - s N = 0 := by
    by_contra hne
    have hpos : 0 < |Int.fract ((3 / 2 : ℝ) ^ N) - s N| := abs_pos.mpr hne
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
      (δ / 5 / |Int.fract ((3 / 2 : ℝ) ^ N) - s N|) (by norm_num : (1 : ℝ) < 3 / 2)
    have h3 := (hs (N + j) (by omega)).2
    rw [hpow j, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (3 / 2) ^ j)] at h3
    rw [div_lt_iff₀ hpos] at hj
    linarith
  -- so all late terms are accumulation points, although they are pairwise distinct
  have hmem : ∀ j : ℕ, Int.fract ((3 / 2 : ℝ) ^ (N + j)) ∈
      {x | Equidistribution.IsAccumulationPoint x fun n : ℕ => Int.fract ((3 / 2 : ℝ) ^ n)} := by
    intro j
    have h := hpow j
    rw [hzero, mul_zero] at h
    have h4 : Int.fract ((3 / 2 : ℝ) ^ (N + j)) = s (N + j) := by linarith
    rw [h4]
    exact (hs (N + j) (by omega)).1
  have hinj' : Function.Injective fun j : ℕ => Int.fract ((3 / 2 : ℝ) ^ (N + j)) := by
    intro a b hab
    have h5 := hinj hab
    omega
  exact Set.infinite_of_injective_forall_mem hinj' hmem hfin
