import FormalConjectures.ErdosProblems.«1166»

-- Reduction Erdos1166.erdos_1166.variants.erdos_taylor.R1 of Erdős Problem 1166 — erdos taylor
-- Credit: @koolkao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The upper half is derived here from H1 and H2 by the first Borel-Cantelli lemma along the
-- dyadic times 2^(j+1) and monotone interpolation in n; the lower half is H3. The hypotheses
-- are stated on probability spaces in Type; main transfers the target from an arbitrary
-- probability space to the canonical path space by pushing the law of the steps forward.

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real ENNReal

namespace OMA.R_Erdos1166_erdos_1166_variants_erdos_taylor_R1

open Erdos1165 Erdos1166

-- H1 (origin tail bound, the Green function input). For the planar simple random walk the
-- probability of no return to the origin within n steps is asymptotic to pi / log n
-- (Dvoretzky and Erdős 1951; Erdős and Taylor 1960; Lawler and Limic, Random Walk: A Modern
-- Introduction, Section 4.4). By the renewal property the number of returns before n is
-- dominated by a geometric variable, so the local time at the origin exceeds
-- (1 + δ) (log n)^2 / pi with probability at most C n^(-(1 + δ/2)).
def H1 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ,
      (1 + δ) * Real.log n ^ 2 / π ≤ k →
        ℙ {ω | k ≤ localTime X n ω 0} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 + δ / 2)))

-- H2 (union bound over first visit times). If some site has local time at least k by time n,
-- let j be its first visit time: the walk then makes k visits to its position at time j within
-- times j..n. By the Markov property at the fixed time j, the increments after j form a fresh
-- walk, so each of the n + 1 events has probability at most that of k visits to the origin by
-- time n. This holds for every walk with i.i.d. steps.
def H2 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ n k : ℕ,
      ℙ {ω | k ≤ maxLocalTime X n ω} ≤ ((n : ℝ≥0∞) + 1) * ℙ {ω | k ≤ localTime X n ω 0}

-- H3 (lower half of Erdős and Taylor 1960). Almost surely the maximal local time is eventually
-- at least (1/(4 pi) - ε) (log n)^2. Erdős and Taylor 1960, p. 162; Dembo, Peres, Rosen and
-- Zeitouni, Acta Math. 186 (2001), even give the constant 1/pi; see also Révész, Random Walk in
-- Random and Non-Random Environments, Chapter 22.
def H3 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ ε : ℝ, 0 < ε →
      ∀ᵐ ω, ∀ᶠ n : ℕ in atTop, (1 / (4 * π) - ε) * Real.log n ^ 2 ≤ maxLocalTime X n ω

lemma localTime_mono {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) (x : ℤ × ℤ) {n m : ℕ}
    (h : n ≤ m) : localTime X n ω x ≤ localTime X m ω x :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

lemma maxLocalTime_mono {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) {n m : ℕ}
    (h : n ≤ m) : maxLocalTime X n ω ≤ maxLocalTime X m ω :=
  Finset.sup_le fun k _ ↦ (localTime_mono X ω _ h).trans (localTime_le_maxLocalTime X m ω _)

lemma real_bound {δ C : ℝ} (hδ : 0 < δ) (j : ℕ) :
    ((2 : ℝ) ^ (j + 1) + 1) * (C * ((2 : ℝ) ^ (j + 1)) ^ (-(1 + δ / 2))) ≤
      2 * |C| * ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by
  have hpos : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  have h1 : ((2 : ℝ) ^ (j + 1)) ^ (-(1 + δ / 2)) =
      ((2 : ℝ) ^ (j + 1))⁻¹ * ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by
    rw [show (-(1 + δ / 2)) = (-1 : ℝ) + (-(δ / 2)) by ring, Real.rpow_add hpos,
      Real.rpow_neg_one]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [h1]
  have hr : 0 ≤ ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by positivity
  have hq : ((2 : ℝ) ^ (j + 1) + 1) * ((2 : ℝ) ^ (j + 1))⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hq0 : 0 ≤ ((2 : ℝ) ^ (j + 1) + 1) * ((2 : ℝ) ^ (j + 1))⁻¹ := by positivity
  calc ((2 : ℝ) ^ (j + 1) + 1) * (C * (((2 : ℝ) ^ (j + 1))⁻¹ * ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1)))
      = (((2 : ℝ) ^ (j + 1) + 1) * ((2 : ℝ) ^ (j + 1))⁻¹) * C *
          ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by ring
    _ ≤ (((2 : ℝ) ^ (j + 1) + 1) * ((2 : ℝ) ^ (j + 1))⁻¹) * |C| *
          ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by
        gcongr
        exact le_abs_self C
    _ ≤ 2 * |C| * ((2 : ℝ) ^ (-(δ / 2))) ^ (j + 1) := by
        gcongr

lemma upper_dyadic (h1 : H1) (h2 : H2) {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω, ∀ᶠ j : ℕ in atTop, (maxLocalTime X (2 ^ (j + 1)) ω : ℝ) <
      (1 + δ) * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / π := by
  obtain ⟨C, hC⟩ := h1 hX δ hδ
  set r : ℝ := (2 : ℝ) ^ (-(δ / 2)) with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let s : ℕ → Set Ω := fun j ↦ {ω | (1 + δ) * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / π ≤
    (maxLocalTime X (2 ^ (j + 1)) ω : ℝ)}
  have hs : ∀ j, ℙ (s j) ≤ ENNReal.ofReal (2 * |C| * r ^ (j + 1)) := by
    intro j
    have hn : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    set k := ⌈(1 + δ) * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / π⌉₊ with hk
    have hse : s j = {ω | k ≤ maxLocalTime X (2 ^ (j + 1)) ω} := by
      ext ω
      simp only [s, Set.mem_setOf_eq, hk, Nat.ceil_le]
    rw [hse]
    refine (h2 hX (2 ^ (j + 1)) k).trans ?_
    refine (mul_le_mul' le_rfl (hC (2 ^ (j + 1)) hn k (Nat.le_ceil _))).trans ?_
    have hcast : (((2 ^ (j + 1) : ℕ) : ℝ≥0∞) + 1) =
        ENNReal.ofReal ((2 : ℝ) ^ (j + 1) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one]
      simp
    rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    exact real_bound hδ j
  have hsum : ∑' j, ℙ (s j) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity)]
    · exact ENNReal.ofReal_ne_top
    · exact ((summable_geometric_of_lt_one hr0 hr1).mul_left r).mul_left (2 * |C|) |>.congr
        (fun j ↦ by ring)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with j hj
  exact lt_of_not_ge hj

lemma interp (f : ℕ → ℕ) (hf : Monotone f) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ᶠ j : ℕ in atTop, (f (2 ^ (j + 1)) : ℝ) <
      (1 + δ) * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 / π) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (1 + δ) ^ 2 * Real.log n ^ 2 / π := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp h
  set J2 := max J (⌈3 / δ⌉₊ + 1)
  refine eventually_atTop.mpr ⟨2 ^ J2, fun n hn ↦ ?_⟩
  set j := Nat.log 2 n
  have hjJ : J2 ≤ j := Nat.le_log_of_pow_le (by norm_num) hn
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ J2 := by positivity
    omega
  have hlow : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn0
  have hup : n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hfj := hJ j (le_trans (le_max_left _ _) hjJ)
  have hfn : f n ≤ f (2 ^ (j + 1)) := hf hup.le
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = (j + 1) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hlog2 : (j : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hlow
  have hj3 : 3 / δ ≤ (j : ℝ) := by
    have h1 : ⌈3 / δ⌉₊ + 1 ≤ j := le_trans (le_max_right _ _) hjJ
    have h2 : (3 / δ) ≤ (⌈3 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈3 / δ⌉₊ : ℕ) : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h1
    linarith
  have hj1 : (1 : ℝ) ≤ j := by
    have : 1 ≤ j := le_trans (by omega) hjJ
    exact_mod_cast this
  have hdj : 3 ≤ δ * j := by
    have := (div_le_iff₀ hδ).mp hj3
    linarith
  have hsq : ((j : ℝ) + 1) ^ 2 ≤ (1 + δ) * (j : ℝ) ^ 2 := by nlinarith
  have hjL : 0 ≤ (j : ℝ) * Real.log 2 := by positivity
  have hmain : ((j + 1) * Real.log 2) ^ 2 ≤ (1 + δ) * Real.log n ^ 2 := by
    have : ((j : ℝ) * Real.log 2) ^ 2 ≤ Real.log n ^ 2 := pow_le_pow_left₀ hjL hlog2 2
    calc ((j + 1) * Real.log 2) ^ 2 = ((j : ℝ) + 1) ^ 2 * Real.log 2 ^ 2 := by ring
      _ ≤ (1 + δ) * (j : ℝ) ^ 2 * Real.log 2 ^ 2 := by gcongr
      _ = (1 + δ) * ((j : ℝ) * Real.log 2) ^ 2 := by ring
      _ ≤ (1 + δ) * Real.log n ^ 2 := by gcongr
  rw [hlog1] at hfj
  have hfn' : (f n : ℝ) ≤ f (2 ^ (j + 1)) := by exact_mod_cast hfn
  have hpi : 0 < π := Real.pi_pos
  calc (f n : ℝ) ≤ f (2 ^ (j + 1)) := hfn'
    _ ≤ (1 + δ) * ((j + 1) * Real.log 2) ^ 2 / π := hfj.le
    _ ≤ (1 + δ) * ((1 + δ) * Real.log n ^ 2) / π := by gcongr
    _ = (1 + δ) ^ 2 * Real.log n ^ 2 / π := by ring

lemma canonical (h1 : H1) (h2 : H2) (h3 : H3) {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ᵐ ω, ∀ ε : ℝ, 0 < ε →
      (∀ᶠ n : ℕ in atTop, 1 / (4 * π) - ε ≤ (maxLocalTime X n ω : ℝ) / Real.log n ^ 2) ∧
      (∀ᶠ n : ℕ in atTop, (maxLocalTime X n ω : ℝ) / Real.log n ^ 2 ≤ 1 / π + ε) := by
  have hpi : 0 < π := Real.pi_pos
  have key : ∀ᵐ ω, ∀ m : ℕ,
      (∀ᶠ n : ℕ in atTop, (1 / (4 * π) - 1 / ((m : ℝ) + 1)) * Real.log n ^ 2 ≤
        maxLocalTime X n ω) ∧
      (∀ᶠ n : ℕ in atTop, (maxLocalTime X n ω : ℝ) ≤
        (1 / π + 1 / ((m : ℝ) + 1)) * Real.log n ^ 2) := by
    rw [ae_all_iff]
    intro m
    set e : ℝ := 1 / ((m : ℝ) + 1) with he_def
    have he : 0 < e := by positivity
    set δ : ℝ := min 1 (e * π / 3) with hδ_def
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ ≤ e * π / 3 := min_le_right _ _
    filter_upwards [h3 hX e he, upper_dyadic h1 h2 hX hδ] with ω hl hu
    refine ⟨hl, ?_⟩
    filter_upwards [interp (fun n ↦ maxLocalTime X n ω) (fun a b hab ↦ maxLocalTime_mono X ω hab)
      hδ hu] with n hn
    refine hn.trans ?_
    have hsq : (1 + δ) ^ 2 ≤ 1 + e * π := by nlinarith
    have hl0 : 0 ≤ Real.log n ^ 2 := sq_nonneg _
    rw [div_le_iff₀ hpi]
    have hpi1 : 1 / π * π = 1 := by rw [one_div, inv_mul_cancel₀ hpi.ne']
    have : (1 / π + e) * Real.log n ^ 2 * π = (1 + e * π) * Real.log n ^ 2 := by
      calc (1 / π + e) * Real.log n ^ 2 * π = (1 / π * π + e * π) * Real.log n ^ 2 := by ring
        _ = (1 + e * π) * Real.log n ^ 2 := by rw [hpi1]
    rw [this]
    gcongr
  filter_upwards [key] with ω hω
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨hl, hu⟩ := hω m
  constructor
  · filter_upwards [hl, eventually_ge_atTop 2] with n hn h2n
    have hlog : 0 < Real.log n ^ 2 := by
      have : (1 : ℝ) < n := by exact_mod_cast h2n
      have := Real.log_pos this
      positivity
    rw [le_div_iff₀ hlog]
    refine le_trans ?_ hn
    gcongr
  · filter_upwards [hu, eventually_ge_atTop 2] with n hn h2n
    have hlog : 0 < Real.log n ^ 2 := by
      have : (1 : ℝ) < n := by exact_mod_cast h2n
      have := Real.log_pos this
      positivity
    rw [div_le_iff₀ hlog]
    refine hn.trans ?_
    gcongr

theorem main : H1 → H2 → H3 → type_of% @Erdos1166.erdos_1166.variants.erdos_taylor := by
  intro h1 h2 h3 Ω _ _ X hX
  have hF : Measurable (fun ω i ↦ X i ω) := measurable_pi_iff.mpr hX.measurable
  letI : MeasureSpace (ℕ → ℤ × ℤ) := ⟨Measure.map (fun ω i ↦ X i ω) ℙ⟩
  haveI : IsProbabilityMeasure (ℙ : Measure (ℕ → ℤ × ℤ)) := by
    constructor
    change Measure.map (fun ω i ↦ X i ω) ℙ Set.univ = 1
    rw [Measure.map_apply hF MeasurableSet.univ]
    simp
  have hX' : IsSimpleRandomWalkSteps (fun i (ω' : ℕ → ℤ × ℤ) ↦ ω' i) := by
    refine ⟨fun k ↦ measurable_pi_apply k, ?_, ?_⟩
    · rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro S sets hs
      have key := hX.indep.measure_inter_preimage_eq_mul S hs
      have hm : ∀ T : Set (ℕ → ℤ × ℤ), MeasurableSet T →
          (ℙ : Measure (ℕ → ℤ × ℤ)) T = ℙ ((fun ω i ↦ X i ω) ⁻¹' T) := fun T hT ↦
        Measure.map_apply hF hT
      rw [hm _ (Finset.measurableSet_biInter S fun i hi ↦ measurable_pi_apply i (hs i hi))]
      rw [Finset.prod_congr rfl fun i hi ↦ hm _ (measurable_pi_apply i (hs i hi))]
      simp only [Set.preimage_iInter₂]
      exact key
    · intro k
      exact (Measure.map_map (measurable_pi_apply k) hF).trans (hX.isUniform k)
  exact ae_of_ae_map hF.aemeasurable (canonical h1 h2 h3 hX')

end OMA.R_Erdos1166_erdos_1166_variants_erdos_taylor_R1
