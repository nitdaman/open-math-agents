import OMAReductions.R_Erdos442_erdos_442_variants_tao_R1
import Mathlib

/-! Derive the logarithmic growth of Tao’s squarefree set from matched reciprocal-mass bounds.
The auxiliary lower estimate uses the same argument as the divisor-sum step. -/

-- Step Erdos442.erdos_442.variants.tao.R1.H1: hypothesis H1 of reduction Erdos442.erdos_442.variants.tao.R1
-- Credit: @dk8827
-- H1 := ∀ (t : ℕ → ℝ) (A : Set ℕ),     (∀ k, t k = Real.exp (Real.exp ((k : ℝ) ^ 2))) →     (∀ n, n ∈ A ↔ Squarefree n ∧ ∃ k : ℕ, 1 ≤ k ∧       t k < (n : ℝ) ∧ (n : ℝ) ≤ t (k + 1) ∧       (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)).card ≤ k ∧       (n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ))).card ≤ 1) →     ∃ f : ℝ → ℝ, f =o[atTop] (1 : ℝ → ℝ) ∧       ∀ᶠ x : ℝ in atTop,         let L := Erdos442.Real.maxLogOne         ∑ n ∈ (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ), (1 : ℝ) / n =           Real.exp ((1 / 2 + f x) * √(L (L x)) * L (L (L x)))  /-- The separate divisor-mass estimate for the same explicit set. The divisor weight can be its value rather than Euler's totient. -/

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology

namespace OMA.TaoAsymptotic



lemma abel_reciprocal (c : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2) volume a b ∧
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c n / (n : ℝ) =
      (∑ n ∈ Finset.Icc 0 ⌊b⌋₊, c n) / b - (∑ n ∈ Finset.Icc 0 ⌊a⌋₊, c n) / a +
        ∫ t in a..b, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2 := by
  let f (t : ℝ) := t⁻¹
  have hne (t : ℝ) (ht : t ∈ Set.Icc a b) : t ≠ 0 := (ha.trans_le ht.1).ne'
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt f (-(t ^ 2)⁻¹) t :=
    hasDerivAt_inv (hne t ht)
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := by
    have h : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Icc a b) := by fun_prop
    exact h.inv₀ (fun t ht => pow_ne_zero _ (hne t ht))
  have hg : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := hc.integrableOn_Icc
  have hfd : IntegrableOn (deriv f) (Set.Icc a b) :=
    (hc.neg.congr (fun t ht => (hd t ht).deriv)).integrableOn_Icc
  have hi : IntervalIntegrable (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have he : (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2) =
        fun t : ℝ => (t ^ 2)⁻¹ * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) := by
      funext t
      rw [div_eq_mul_inv, mul_comm]
    rw [he]
    exact integrableOn_mul_sum_Icc c ha.le hg
  refine ⟨hi, ?_⟩
  have hf := sum_mul_eq_sub_sub_integral_mul c (f := f) ha.le hab
    (fun t ht => (hd t ht).differentiableAt) hfd
  rw [← intervalIntegral.integral_of_le hab] at hf
  have hint :
      (∫ t in a..b, deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
        -(∫ t in a..b, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    change deriv f t * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) = -((∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2)
    rw [(hd t ht).deriv, neg_mul, div_eq_mul_inv, mul_comm ((t ^ 2)⁻¹)]
  rw [hint] at hf
  simpa only [f, div_eq_mul_inv, mul_comm, sub_neg_eq_add] using hf

lemma prime_reciprocal_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2) volume a b ∧
    ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p =
      (Nat.primeCounting ⌊b⌋₊ : ℝ) / b - (Nat.primeCounting ⌊a⌋₊ : ℝ) / a +
        ∫ t in a..b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
  classical
  let c (n : ℕ) : ℝ := if n.Prime then 1 else 0
  have hc (N : ℕ) : (∑ p ∈ Finset.Icc 0 N, c p) = (Nat.primeCounting N : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    simp only [c, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Nat.range_succ_eq_Icc_zero, Nat.primesLE, Nat.primesBelow]
  obtain ⟨hint, heq⟩ := abel_reciprocal c ha hab
  refine ⟨?_, ?_⟩
  · simpa only [hc] using hint
  simp only [hc] at heq
  rw [← heq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p.Prime <;> simp [h, c]

lemma eventual_chebyshev_pair :
    ∃ y : ℝ, 1 < y ∧ ∀ t ≥ y,
      Real.log 2 / 2 * t / Real.log t ≤ (Nat.primeCounting ⌊t⌋₊ : ℝ) ∧
        (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (Real.log 4 + 1) * t / Real.log t := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : ∀ᶠ t : ℝ in atTop,
      Real.log 2 / 2 * t / Real.log t ≤ (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
    filter_upwards [eventually_ge_atTop (8 : ℝ), Real.isLittleO_log_id_atTop.bound
      (show 0 < Real.log 2 / 4 by positivity)] with t ht h
    have ht1 : 1 < t := by linarith
    have ht0 : 0 < t := by linarith
    have hlog := Real.log_pos ht1
    change ‖Real.log t‖ ≤ (Real.log 2 / 4) * ‖t‖ at h
    rw [Real.norm_of_nonneg hlog.le, Real.norm_of_nonneg ht0.le] at h
    have hcomp := Real.log_le_log (show 0 < t + 2 by positivity) (show t + 2 ≤ 2 * t by linarith)
    rw [Real.log_mul (by norm_num) ht0.ne'] at hcomp
    apply le_trans ?_ (Chebyshev.pi_ge' ht1)
    apply div_le_div_of_nonneg_right _ hlog.le
    have he := mul_le_mul_of_nonneg_right ht hl2.le
    nlinarith only [h, hcomp, he]
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (hl.and (Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num)))
  exact ⟨max a 2, (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right a 2),
    fun t ht => ha t ((le_max_left a 2).trans ht)⟩

theorem prime_reciprocal_interval_bounds :
    ∃ y : ℝ, 1 < y ∧ ∀ a b : ℝ, y ≤ a → a ≤ b →
      let w := ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p
      let z := Real.log (Real.log b) - Real.log (Real.log a)
      Real.log 2 / 2 * z - (Real.log 4 + 1) / Real.log a ≤ w ∧
        w ≤ (Real.log 4 + 1) * z + (Real.log 4 + 1) / Real.log a := by
  obtain ⟨y, hy, hY⟩ := eventual_chebyshev_pair
  refine ⟨y, hy, ?_⟩
  intro a b ha hab
  have ha1 : 1 < a := hy.trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hb0 : 0 < b := ha0.trans_le hab
  let c := Real.log 2 / 2
  let C := Real.log 4 + 1
  have hc0 : 0 < c := by dsimp [c]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hC0 : 0 < C := by dsimp [C]; linarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)]
  let T (t : ℝ) := (Nat.primeCounting ⌊t⌋₊ : ℝ)
  let g (t : ℝ) := t⁻¹ / Real.log t
  obtain ⟨hi, heq⟩ := prime_reciprocal_abel ha0 hab
  have h1 (t : ℝ) (ht : t ∈ Set.Icc a b) : 1 < t := ha1.trans_le ht.1
  have hg : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.div
    · exact continuousOn_id.inv₀ (fun t ht => (zero_lt_one.trans (h1 t ht)).ne')
    · apply Real.continuousOn_log.mono
      intro t ht
      exact Set.mem_compl_singleton_iff.mpr (zero_lt_one.trans (h1 t ht)).ne'
    · exact fun t ht => (Real.log_pos (h1 t ht)).ne'
  have hgi : IntervalIntegrable g volume a b := by
    apply hg.intervalIntegrable_of_Icc hab
  have hfac (d t : ℝ) (ht : 1 < t) : d * g t = (d * t / Real.log t) / t ^ 2 := by
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hlog := Real.log_pos ht
    dsimp [g]
    field_simp
  have hIntL : c * (∫ t in a..b, g t) ≤ ∫ t in a..b, T t / t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab (hgi.const_mul c) hi
    intro t ht
    rw [hfac c t (h1 t ht)]
    exact div_le_div_of_nonneg_right (hY t (ha.trans ht.1)).1 (sq_nonneg _)
  have hIntU : (∫ t in a..b, T t / t ^ 2) ≤ C * ∫ t in a..b, g t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab hi (hgi.const_mul C)
    intro t ht
    rw [hfac C t (h1 t ht)]
    exact div_le_div_of_nonneg_right (hY t (ha.trans ht.1)).2 (sq_nonneg _)
  have hgi_eq : (∫ t in a..b, g t) = Real.log (Real.log b) - Real.log (Real.log a) :=
    integral_inv_div_log ha1 hb1
  rw [hgi_eq] at hIntL hIntU
  have hTA : T a / a ≤ C / Real.log a := by
    apply (div_le_iff₀ ha0).mpr
    rw [div_mul_eq_mul_div]
    exact (hY a ha).2
  have hTB : T b / b ≤ C / Real.log a := by
    calc
      _ ≤ C / Real.log b := by
        apply (div_le_iff₀ hb0).mpr
        rw [div_mul_eq_mul_div]
        exact (hY b (ha.trans hab)).2
      _ ≤ _ := div_le_div_of_nonneg_left hC0.le (Real.log_pos ha1) (Real.log_le_log ha0 hab)
  have hTA0 : 0 ≤ T a / a := by dsimp [T]; positivity
  have hTB0 : 0 ≤ T b / b := by dsimp [T]; positivity
  change _ ≤ _ ∧ _ ≤ _
  rw [heq]
  constructor
  · change c * (Real.log (Real.log b) - Real.log (Real.log a)) - C / Real.log a ≤ _
    linarith only [hIntL, hTA, hTB0]
  · change _ ≤ C * (Real.log (Real.log b) - Real.log (Real.log a)) + C / Real.log a
    linarith only [hIntU, hTB, hTA0]

noncomputable def primeMass (x : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p

lemma prime_mass_sub_eq {a b : ℝ} (hab : a ≤ b) :
    primeMass b - primeMass a =
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
  classical
  have hsub : Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊b⌋₊ := by
    intro p hp
    obtain ⟨hle, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.floor_le_floor hab), hpp⟩
  have he : Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊ =
      (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
    by_cases h : p.Prime <;> simp [h, not_le, and_comm]
  rw [← he, primeMass, primeMass]
  exact (eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hsub)).symm

lemma prime_mass_mono : Monotone primeMass := by
  intro a b hab
  have h := prime_mass_sub_eq hab
  exact sub_nonneg.mp (h ▸ Finset.sum_nonneg (fun _ _ => by positivity))

lemma prime_mass_nonneg (x : ℝ) : 0 ≤ primeMass x := Finset.sum_nonneg (fun _ _ => by positivity)

lemma prime_mass_between {a b : ℝ} (hab : a ≤ b) :
    (∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ => a < (p : ℝ)), (1 : ℝ) / p) =
      primeMass b - primeMass a := by
  classical
  rw [prime_mass_sub_eq hab]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
  by_cases h : p.Prime
  · have hp : ⌊a⌋₊ < p ↔ a < (p : ℝ) :=
      lt_iff_lt_of_le_iff_le (Nat.le_floor_iff' h.ne_zero)
    tauto
  · tauto

theorem prime_mass_log_log_comparison :
    ∃ y : ℝ, Real.exp 1 ≤ y ∧ ∀ a b : ℝ, y ≤ a → a ≤ b →
      let z := Real.log (Real.log b) - Real.log (Real.log a)
      Real.log 2 / 2 * z - (Real.log 4 + 1) ≤ primeMass b - primeMass a ∧
        primeMass b - primeMass a ≤ (Real.log 4 + 1) * z + (Real.log 4 + 1) := by
  obtain ⟨y, hy, h⟩ := prime_reciprocal_interval_bounds
  refine ⟨max y (Real.exp 1), le_max_right _ _, ?_⟩
  intro a b ha hab
  have hya := (le_max_left y (Real.exp 1)).trans ha
  have hloga : 1 ≤ Real.log a := by
    have hle : Real.exp 1 ≤ a := (le_max_right y (Real.exp 1)).trans ha
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hle
  have hC : 0 ≤ Real.log 4 + 1 := by linarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)]
  have hA : (Real.log 4 + 1) / Real.log a ≤ Real.log 4 + 1 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log a)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hloga hC
  rw [prime_mass_sub_eq hab]
  have hh := h a b hya hab
  exact ⟨(sub_le_sub_left hA _).trans hh.1, hh.2.trans (add_le_add_right hA _)⟩


lemma weighted_subsets_recurrence {α : Type} [DecidableEq α] (S : Finset α)
    (w : α → ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * (∑ T ∈ S.powersetCard (k + 1), ∏ a ∈ T, w a) =
      ∑ T ∈ S.powersetCard k, (∏ a ∈ T, w a) * (∑ a ∈ S \ T, w a) := by
  classical
  let I := (S.powersetCard k).sigma (fun T => S \ T)
  let J := (S.powersetCard (k + 1)).sigma (fun T => T)
  let i (p : Σ _ : Finset α, α) : Σ _ : Finset α, α := ⟨insert p.2 p.1, p.2⟩
  let j (p : Σ _ : Finset α, α) : Σ _ : Finset α, α := ⟨p.1.erase p.2, p.2⟩
  have hi (p : Σ _ : Finset α, α) (hp : p ∈ I) : i p ∈ J := by
    obtain ⟨hP, hp⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hP
    obtain ⟨hpS, hpP⟩ := Finset.mem_sdiff.mp hp
    refine Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · exact Finset.insert_subset_iff.mpr ⟨hpS, hsub⟩
    · rw [Finset.card_insert_of_notMem hpP, hc]
  have hj (p : Σ _ : Finset α, α) (hp : p ∈ J) : j p ∈ I := by
    obtain ⟨hP, hp⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hP
    refine Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨(Finset.erase_subset _ _).trans hsub, ?_⟩,
      Finset.mem_sdiff.mpr ⟨hsub hp, Finset.notMem_erase _ _⟩⟩
    rw [Finset.card_erase_of_mem hp, hc, Nat.add_sub_cancel]
  have hi' (p : Σ _ : Finset α, α) (hp : p ∈ I) : j (i p) = p := by
    have hnot := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp).2).2
    cases p with
    | mk T a =>
      change (⟨(insert a T).erase a, a⟩ : Σ _ : Finset α, α) = ⟨T, a⟩
      rw [Finset.erase_insert hnot]
  have hj' (p : Σ _ : Finset α, α) (hp : p ∈ J) : i (j p) = p := by
    have hmem := (Finset.mem_sigma.mp hp).2
    cases p with
    | mk T a =>
      change (⟨insert a (T.erase a), a⟩ : Σ _ : Finset α, α) = ⟨T, a⟩
      rw [Finset.insert_erase hmem]
  symm
  calc
    _ = ∑ p ∈ I, (∏ a ∈ p.1, w a) * w p.2 := by
      simp only [I, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mul_sum]
    _ = ∑ p ∈ J, ∏ a ∈ p.1, w a := by
      refine Finset.sum_nbij' i j hi hj hi' hj' ?_
      intro p hp
      have hn := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp).2).2
      change _ = ∏ a ∈ insert p.2 p.1, w a
      rw [Finset.prod_insert hn, mul_comm]
    _ = _ := by
      simp only [J, Finset.sum_sigma, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.mp hT).2]

theorem weighted_subsets_factorial_lower {α : Type} [DecidableEq α] (w : α → ℝ)
    (S : Finset α) (k : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hW : ∀ a ∈ S, 0 ≤ w a ∧ w a ≤ M)
    (hL : 0 ≤ (∑ a ∈ S, w a) - (k : ℝ) * M) :
    ((∑ a ∈ S, w a) - (k : ℝ) * M) ^ k ≤
      (k.factorial : ℝ) * (∑ T ∈ S.powersetCard k, ∏ a ∈ T, w a) := by
  let r := (∑ a ∈ S, w a) - (k : ℝ) * M
  have hstep : ∀ j ≤ k, r ^ j ≤ (j.factorial : ℝ) * (∑ T ∈ S.powersetCard j, ∏ a ∈ T, w a) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hrec := weighted_subsets_recurrence S w j
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
      calc
        _ ≤ ((j.factorial : ℝ) * (∑ T ∈ S.powersetCard j, ∏ a ∈ T, w a)) * r :=
          mul_le_mul_of_nonneg_right (ih (Nat.le_of_succ_le hj)) hL
        _ = (j.factorial : ℝ) * (∑ T ∈ S.powersetCard j, (∏ a ∈ T, w a) * r) := by
          rw [mul_assoc, Finset.sum_mul]
        _ ≤ (j.factorial : ℝ) * (∑ T ∈ S.powersetCard j,
            (∏ a ∈ T, w a) * ∑ a ∈ S \ T, w a) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro T hT
          obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hT
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun a ha => (hW a (hsub ha)).1))
          have hSum : (∑ a ∈ T, w a) ≤ (j : ℝ) * M := by
            calc
              _ ≤ ∑ a ∈ T, M := Finset.sum_le_sum (fun a ha => (hW a (hsub ha)).2)
              _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hc]
          have hjk : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_succ_le hj)
          have hM' := mul_le_mul_of_nonneg_right hjk hM
          have hsplit := Finset.sum_sdiff hsub (f := w)
          dsimp [r]
          linarith only [hSum, hM', hsplit]
        _ = _ := by rw [← hrec]; ring
  exact hstep k le_rfl


noncomputable def doubleExp (x : ℝ) : ℝ := Real.exp (Real.exp x)

lemma doubleExp_pos (x : ℝ) : 0 < doubleExp x := Real.exp_pos _

lemma doubleExp_mono : StrictMono doubleExp := Real.exp_strictMono.comp Real.exp_strictMono

lemma log_log_doubleExp (x : ℝ) : Real.log (Real.log (doubleExp x)) = x := by
  simp [doubleExp]

lemma le_doubleExp (x : ℝ) : x ≤ doubleExp x := by
  have h1 := Real.add_one_le_exp x
  have h2 := Real.add_one_le_exp (Real.exp x)
  dsimp [doubleExp]
  linarith

lemma doubleExp_to_pow_le (k : ℕ) :
    doubleExp ((k : ℝ) ^ 2 - k) ^ k ≤ doubleExp ((k : ℝ) ^ 2) := by
  rw [doubleExp, doubleExp, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  rw [Real.exp_sub, ← mul_div_assoc]
  have hk : (k : ℝ) ≤ Real.exp (k : ℝ) := by linarith [Real.add_one_le_exp (k : ℝ)]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  exact mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le |>.trans_eq (mul_comm _ _)

lemma doubleExp_shift_sq (x : ℝ) : doubleExp (x - 1) ^ 2 ≤ doubleExp x := by
  rw [doubleExp, doubleExp, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_ofNat, Real.exp_sub, ← mul_div_assoc]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  exact (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le).trans_eq (mul_comm _ _)

lemma exp_neg_four_mul_le_degree_ratio {a r B : ℝ} {k j : ℕ}
    (hB : 0 ≤ B) (hk : 0 < k) (hj : j ≤ k)
    (ha : (k : ℝ) ^ 2 / 2 ≤ a) (hr : a - B * k ≤ r) (hbig : 4 * B ≤ (k : ℝ)) :
    Real.exp (-4 * B) * a ^ j ≤ r ^ j := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha0 : 0 < a := (by positivity : 0 < (k : ℝ) ^ 2 / 2).trans_le ha
  let d := B * (k : ℝ) / a
  have hd0 : 0 ≤ d := div_nonneg (mul_nonneg hB hk0.le) ha0.le
  have hd2 : d ≤ 1 / 2 := by
    apply (div_le_iff₀ ha0).mpr
    have hmul := mul_le_mul_of_nonneg_right hbig hk0.le
    nlinarith only [hmul, ha]
  have hdk : d * (k : ℝ) ≤ 2 * B := by
    dsimp [d]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha0).mpr
    have hmul := mul_le_mul_of_nonneg_left ha hB
    nlinarith only [hmul]
  have he : Real.exp (-2 * d) ≤ 1 - d := by
    have hden : 0 < 1 - d := by linarith
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
    rw [Real.log_inv] at hlog
    have hq : (1 - d)⁻¹ - 1 ≤ 2 * d := by
      have hq' : (1 - d)⁻¹ - 1 = d / (1 - d) := by field_simp; ring
      rw [hq']
      apply (div_le_iff₀ hden).mpr
      have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ 2 * (1 - d) by linarith) hd0
      nlinarith only [hmul]
    rw [← Real.exp_log hden]
    exact Real.exp_le_exp.mpr (by linarith only [hlog, hq])
  have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hdj := (mul_le_mul_of_nonneg_left hj' hd0).trans hdk
  have hbase : a * Real.exp (-2 * d) ≤ r := by
    calc
      _ ≤ a * (1 - d) := mul_le_mul_of_nonneg_left he ha0.le
      _ = a - B * k := by dsimp [d]; field_simp
      _ ≤ _ := hr
  calc
    _ ≤ Real.exp ((j : ℝ) * (-2 * d)) * a ^ j :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith only [hdj])) (by positivity)
    _ = (a * Real.exp (-2 * d)) ^ j := by rw [mul_pow, Real.exp_nat_mul, mul_comm]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase _


lemma squarefree_product_of_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hne => ?_)
    (fun p hp => (hs p hp).squarefree)
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hne)

lemma tao_mass_from_prime_products (t : ℕ → ℝ) (A : Set ℕ)
    (hA : ∀ n, n ∈ A ↔ Squarefree n ∧ ∃ k : ℕ, 1 ≤ k ∧
      t k < (n : ℝ) ∧ (n : ℝ) ≤ t (k + 1) ∧
      (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)).card ≤ k ∧
      (n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ))).card ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) {u v x : ℝ} (hu : u ≤ t k)
    (hcut : u ^ k * v ≤ t (k + 1)) (hx : u ^ k * v ≤ x) :
    let P := Nat.primesLE ⌊u⌋₊
    let Q := (Nat.primesLE ⌊v⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
    let S := (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ).toFinset
    (∑ T ∈ P.powersetCard k, ∏ p ∈ T, (1 : ℝ) / p) * (∑ p ∈ Q, (1 : ℝ) / p) ≤
      ∑ n ∈ S, (1 : ℝ) / n := by
  classical
  dsimp
  let P := Nat.primesLE ⌊u⌋₊
  let Q := (Nat.primesLE ⌊v⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
  let S := (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ).toFinset
  let F := P.powersetCard k ×ˢ Q
  let f (w : Finset ℕ × ℕ) := (∏ p ∈ w.1, p) * w.2
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ (p : ℝ) ≤ u := by
    obtain ⟨hle, hpr⟩ := Nat.mem_primesLE.mp hp
    exact ⟨hpr, (Nat.le_floor_iff' hpr.ne_zero).mp hle⟩
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime ∧ t k < (p : ℝ) ∧ (p : ℝ) ≤ v := by
    obtain ⟨hP', hgt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hle, hpr⟩ := Nat.mem_primesLE.mp hP'
    exact ⟨hpr, hgt, (Nat.le_floor_iff' hpr.ne_zero).mp hle⟩
  have hnot (w : Finset ℕ × ℕ) (hw : w ∈ F) : w.2 ∉ w.1 := by
    intro h
    exact (not_lt_of_ge ((hP _ ((Finset.mem_powersetCard.mp (Finset.mem_product.mp hw).1).1 h)).2.trans hu))
      (hQ _ (Finset.mem_product.mp hw).2).2.1
  have hpr (w : Finset ℕ × ℕ) (hw : w ∈ F) (p : ℕ) (hp : p ∈ insert w.2 w.1) :
      p.Prime := by
    rcases Finset.mem_insert.mp hp with he | h
    · rw [he]
      exact (hQ _ (Finset.mem_product.mp hw).2).1
    · exact (hP _ ((Finset.mem_powersetCard.mp (Finset.mem_product.mp hw).1).1 h)).1
  have hProd (w : Finset ℕ × ℕ) (hw : w ∈ F) : (∏ p ∈ insert w.2 w.1, p) = f w := by
    rw [Finset.prod_insert (hnot w hw)]
    exact mul_comm _ _
  have hfactor (w : Finset ℕ × ℕ) (hw : w ∈ F) : (f w).primeFactors = insert w.2 w.1 := by
    rw [← hProd w hw]
    exact Nat.primeFactors_prod (hpr w hw)
  have hsf (w : Finset ℕ × ℕ) (hw : w ∈ F) : Squarefree (f w) := by
    rw [← hProd w hw]
    exact squarefree_product_of_primes _ (hpr w hw)
  have hi : Set.InjOn f (↑F : Set (Finset ℕ × ℕ)) := by
    intro w hw z hz h
    have he : insert w.2 w.1 = insert z.2 z.1 := by
      rw [← hfactor w hw, ← hfactor z hz, h]
    have hp : w.2 = z.2 := by
      rcases Finset.mem_insert.mp (he ▸ Finset.mem_insert_self w.2 w.1) with heq | heq
      · exact heq
      · have hle := (hP _ ((Finset.mem_powersetCard.mp (Finset.mem_product.mp hz).1).1 heq)).2
        exact (not_lt_of_ge (hle.trans hu) (hQ _ (Finset.mem_product.mp hw).2).2.1).elim
    have hT : w.1 = z.1 := by
      have hErase := congrArg (fun T : Finset ℕ => T.erase w.2) he
      rw [Finset.erase_insert (hnot w hw), hp, Finset.erase_insert (hnot z hz)] at hErase
      exact hErase
    exact Prod.ext hT hp
  have hsubset : F.image f ⊆ S := by
    intro n hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hF, hq⟩ := Finset.mem_product.mp hw
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hF
    obtain ⟨hp, hp_lo, hp_hi⟩ := hQ _ hq
    have hm : 0 < ∏ p ∈ w.1, p := Finset.prod_pos fun p hp => (hP p (hsub hp)).1.pos
    have hn0 := (hsf w hw).ne_zero
    have hLow : t k < (f w : ℝ) := by
      have hm1 : (1 : ℝ) ≤ ((∏ p ∈ w.1, p : ℕ) : ℝ) := by exact_mod_cast hm
      have hmul := mul_le_mul_of_nonneg_right hm1 (by positivity : 0 ≤ (w.2 : ℝ))
      exact hp_lo.trans_le (by simpa only [f, Nat.cast_mul, one_mul] using hmul)
    have hm_hi : ((∏ p ∈ w.1, p : ℕ) : ℝ) ≤ u ^ k := by
      rw [Nat.cast_prod]
      calc
        _ ≤ ∏ _ ∈ w.1, u := Finset.prod_le_prod (fun _ _ => by positivity)
          (fun p hp => (hP p (hsub hp)).2)
        _ = _ := by simp [hcard]
    have hHi : (f w : ℝ) ≤ u ^ k * v := by
      dsimp [f]
      rw [Nat.cast_mul]
      exact mul_le_mul hm_hi hp_hi (by positivity)
        ((by positivity : 0 ≤ ((∏ p ∈ w.1, p : ℕ) : ℝ)).trans hm_hi)
    have hlarge : ((f w).primeFactors.filter (fun p : ℕ => t k < (p : ℝ))) = {w.2} := by
      rw [hfactor w hw]
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨he | h, hgt⟩
        · exact he
        · exact (not_lt_of_ge ((hP p (hsub h)).2.trans hu) hgt).elim
      · intro he
        rw [he]
        exact ⟨Or.inl rfl, hp_lo⟩
    have hsmall : ((f w).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)) = w.1 := by
      rw [hfactor w hw]
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨he | h, hle⟩
        · exact (not_lt_of_ge (he ▸ hle) hp_lo).elim
        · exact h
      · intro h
        exact ⟨Or.inr h, (hP p (hsub h)).2.trans hu⟩
    refine Set.mem_toFinset.mpr ⟨(hA _).mpr ⟨hsf w hw, k, hk, hLow, hHi.trans hcut, ?_, ?_⟩, ?_⟩
    · rw [hsmall, hcard]
    · simp [hlarge]
    · exact ⟨Nat.one_le_iff_ne_zero.mpr hn0, (Nat.le_floor_iff' hn0).mpr (hHi.trans hx)⟩
  have hweight (w : Finset ℕ × ℕ) :
      (∏ p ∈ w.1, (1 : ℝ) / p) * ((1 : ℝ) / w.2) = (1 : ℝ) / f w := by
    have he : (∏ p ∈ w.1, (1 : ℝ) / p) = 1 / ((∏ p ∈ w.1, p : ℕ) : ℝ) := by
      simp only [one_div, Finset.prod_inv_distrib]
      rw [Nat.cast_prod]
    rw [he, one_div_mul_one_div]
    simp only [f, Nat.cast_mul]
  change _ ≤ ∑ n ∈ S, (1 : ℝ) / n
  calc
    _ = ∑ w ∈ F, (1 : ℝ) / f w := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      exact hweight (T, p)
    _ = ∑ n ∈ F.image f, (1 : ℝ) / n := by
      symm
      exact Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / n) (g := f) hi
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)


lemma log_le_exp_prime_reciprocal_sum (N : ℕ) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.exp (2 * (∑ p ∈ N.primesLE, (1 : ℝ) / p)) := by
  classical
  let f : ℕ →* ℝ := {
    toFun := fun n => (1 : ℝ) / n
    map_one' := by simp
    map_mul' := by intro n m; simp [Nat.cast_mul, one_div, mul_comm] }
  have hnorm {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(1 : ℝ) / p‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hp' : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    exact (div_lt_one hp').mpr (by exact_mod_cast hp.one_lt)
  obtain ⟨hs, hsum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric (f := f) hnorm (N + 1)
  let s := Finset.Icc 1 N
  let e : ↥s ↪ (N + 1).smoothNumbers :=
    ⟨fun n => ⟨n.val, Nat.mem_smoothNumbers_of_lt (Finset.mem_Icc.mp n.property).1
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp n.property).2)⟩,
    fun a b h => Subtype.ext (congrArg (fun n : (N + 1).smoothNumbers => n.val) h)⟩
  have hpart : (∑ n ∈ s, (1 : ℝ) / n) ≤ ∏ p ∈ (N + 1).primesBelow, (1 - f p)⁻¹ := by
    rw [← hsum.tsum_eq]
    have hle : (∑ n ∈ s.attach.map e, f n) ≤ ∑' n : (N + 1).smoothNumbers, f n :=
      hs.of_norm.sum_le_tsum _ (fun _ _ => by change 0 ≤ (1 : ℝ) / _; positivity)
    rw [Finset.sum_map] at hle
    change (∑ n ∈ s.attach, (1 : ℝ) / (n.val : ℝ)) ≤ _ at hle
    rw [Finset.sum_attach s (fun n : ℕ => (1 : ℝ) / n)] at hle
    exact hle
  have hexp (p : ℕ) (hp : p ∈ (N + 1).primesBelow) :
      (1 - f p)⁻¹ ≤ Real.exp (2 * ((1 : ℝ) / p)) := by
    let q := (1 : ℝ) / p
    have hp' := Nat.prime_of_mem_primesBelow hp
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq : q ≤ 1 / 2 := by
      apply (div_le_div_iff₀ hp0 (by norm_num : (0 : ℝ) < 2)).mpr
      linarith
    have hden : 0 < 1 - q := by linarith
    have hratio : q / (1 - q) ≤ 2 * q := by
      apply (div_le_iff₀ hden).mpr
      have h : 1 ≤ 2 * (1 - q) := by linarith
      calc
        q = q * 1 := by ring
        _ ≤ q * (2 * (1 - q)) := mul_le_mul_of_nonneg_left h hq0
        _ = _ := by ring
    change (1 - q)⁻¹ ≤ Real.exp (2 * q)
    calc
      _ = q / (1 - q) + 1 := by field_simp; ring
      _ ≤ Real.exp (q / (1 - q)) := Real.add_one_le_exp _
      _ ≤ _ := Real.exp_le_exp.mpr hratio
  calc
    _ ≤ (harmonic N : ℝ) := log_add_one_le_harmonic N
    _ = ∑ n ∈ s, (1 : ℝ) / n := by
      simp only [s, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ ∏ p ∈ (N + 1).primesBelow, (1 - f p)⁻¹ := hpart
    _ ≤ ∏ p ∈ (N + 1).primesBelow, Real.exp (2 * ((1 : ℝ) / p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        have h := hnorm (Nat.prime_of_mem_primesBelow hp)
        have habs : f p ≤ ‖f p‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
        linarith
      · exact hexp
    _ = _ := by
      rw [← Real.exp_sum, ← Finset.mul_sum]
      rfl
lemma small_prime_subsets_lower {a B z : ℝ} {j k : ℕ}
    (hB : 0 ≤ B) (hk : 0 < k) (hj : j ≤ k)
    (ha : (k : ℝ) ^ 2 / 2 ≤ a) (hbig : 4 * B ≤ (k : ℝ))
    (hz : a - B * k ≤ primeMass z - (j : ℝ) / 2) :
    Real.exp (-4 * B) * (a ^ j / (j.factorial : ℝ)) ≤
      ∑ T ∈ (Nat.primesLE ⌊z⌋₊).powersetCard j, ∏ p ∈ T, (1 : ℝ) / p := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hBK := mul_le_mul_of_nonneg_right hbig hk0
  have hr0 : 0 ≤ primeMass z - (j : ℝ) / 2 := by nlinarith only [ha, hz, hBK, sq_nonneg (k : ℝ)]
  have hf : 0 < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hf).mpr
  rw [mul_comm (∑ T ∈ (Nat.primesLE ⌊z⌋₊).powersetCard j, ∏ p ∈ T, (1 : ℝ) / p)]
  apply (exp_neg_four_mul_le_degree_ratio hB hk hj ha hz hbig).trans
  change (primeMass z - (j : ℝ) / 2) ^ j ≤ _
  rw [div_eq_mul_inv]
  apply weighted_subsets_factorial_lower (fun p : ℕ => (1 : ℝ) / p) _ _ (by norm_num)
  · intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : 0 < (p : ℝ) := by linarith
    refine ⟨by positivity, ?_⟩
    rw [← one_div (2 : ℝ)]
    apply (div_le_div_iff₀ hp0 (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  · simpa only [primeMass, div_eq_mul_inv] using hr0

lemma previous_factorial_term {a C : ℝ} {k : ℕ} (hk : 0 < k) (ha : 0 ≤ a) (hC : 0 < C)
    (h : a ≤ C * (k : ℝ) ^ 2) :
    (a ^ k / (k.factorial : ℝ)) / C ≤ (k : ℝ) * (a ^ (k - 1) / ((k - 1).factorial : ℝ)) := by
  have hkstep : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  have hfact : (k.factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by
    have hf := Nat.factorial_succ (k - 1)
    rw [hkstep] at hf
    exact_mod_cast hf
  have hpow : a ^ k = a ^ (k - 1) * a := by
    nth_rw 1 [← hkstep]
    rw [pow_succ]
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hf : 0 < ((k - 1).factorial : ℝ) := by exact_mod_cast (k - 1).factorial_pos
  have heq : a ^ k / (k.factorial : ℝ) =
      (a / (k : ℝ)) * (a ^ (k - 1) / ((k - 1).factorial : ℝ)) := by
    rw [hpow, hfact]
    field_simp
  have ha' : a / (k : ℝ) ≤ C * (k : ℝ) := by
    apply (div_le_iff₀ hk0).mpr
    simpa only [pow_two, mul_assoc] using h
  apply (div_le_iff₀ hC).mpr
  rw [heq]
  calc
    _ ≤ (C * (k : ℝ)) * (a ^ (k - 1) / ((k - 1).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right ha' (by positivity)
    _ = _ := by ring

lemma combine_tao_mass_lower {M y q b c D : ℝ} (hb : 0 < b) (hc : 0 < c) (hD : 0 ≤ D)
    (hbase : b * y ≤ M) (hcurr : c * y * (q - D) ≤ M) :
    ((1 / c + (D + 1) / b)⁻¹) * (1 + q) * y ≤ M := by
  have htotal : 0 < 1 / c + (D + 1) / b :=
    add_pos (by positivity) (div_pos (by linarith) hb)
  have h1 : y ≤ M / b := (le_div_iff₀ hb).mpr (by linarith only [hbase])
  have h2 : y * (q - D) ≤ M / c := (le_div_iff₀ hc).mpr (by nlinarith only [hcurr])
  have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ D + 1 by linarith)
  rw [mul_assoc, inv_mul_eq_div]
  apply (div_le_iff₀ htotal).mpr
  have heq : M * (1 / c + (D + 1) / b) = M / c + (D + 1) * (M / b) := by ring
  rw [heq]
  nlinarith only [h2, h3]
theorem tao_reciprocal_mass_lower (t : ℕ → ℝ) (A : Set ℕ)
    (hT : ∀ k, t k = Real.exp (Real.exp ((k : ℝ) ^ 2)))
    (hA : ∀ n, n ∈ A ↔ Squarefree n ∧ ∃ k : ℕ, 1 ≤ k ∧
      t k < (n : ℝ) ∧ (n : ℝ) ≤ t (k + 1) ∧
      (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)).card ≤ k ∧
      (n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ))).card ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ k : ℕ, 1 ≤ k → t k < x → x ≤ t (k + 1) →
        let S := (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ).toFinset
        let a := ∑ p ∈ Nat.primesLE ⌊t k⌋₊, (1 : ℝ) / p
        let Q := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
        let q := ∑ p ∈ Q, (1 : ℝ) / p
        δ * (1 + q) * (a ^ k / (k.factorial : ℝ)) ≤ ∑ n ∈ S, (1 : ℝ) / n := by
  classical
  obtain ⟨Y, hY, hcomp⟩ := prime_mass_log_log_comparison
  let c := Real.log 2 / 2
  let C := Real.log 4 + 1
  let B := 4 * C + 1
  let U := primeMass Y + 2 * C + 1
  let η := Real.exp (-4 * B)
  let b := η * c / U
  let D := 2 * C
  have hc : 0 < c := by dsimp [c]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hC : 0 < C := by dsimp [C]; linarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)]
  have hB : 0 < B := by dsimp [B]; positivity
  have hU : 0 < U := by dsimp [U]; linarith [prime_mass_nonneg Y]
  have hη : 0 < η := Real.exp_pos _
  have hb : 0 < b := div_pos (mul_pos hη hc) hU
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hY1 : 1 < Y :=
    (show (1 : ℝ) < Real.exp 1 by
      have h : Real.exp 0 < Real.exp 1 := Real.exp_strictMono zero_lt_one
      simpa only [Real.exp_zero] using h).trans_le hY
  have hlogY : 1 ≤ Real.log Y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hY
  have hlY : 0 ≤ Real.log (Real.log Y) := Real.log_nonneg hlogY
  have tCut (n : ℕ) : t n = doubleExp ((n : ℝ) ^ 2) := hT n
  have tPos (n : ℕ) : 0 < t n := tCut n ▸ doubleExp_pos _
  have tMono : StrictMono t := by
    intro i j h
    rw [tCut i, tCut j]
    exact doubleExp_mono (pow_lt_pow_left₀ (by exact_mod_cast h) (by positivity) (by decide))
  have tLog (n : ℕ) : Real.log (Real.log (t n)) = (n : ℝ) ^ 2 := by rw [tCut, log_log_doubleExp]
  let s (n : ℕ) := doubleExp ((n : ℝ) ^ 2 - n)
  have sPos (n : ℕ) : 0 < s n := doubleExp_pos _
  have sLe (n : ℕ) : s n ≤ t n := by
    rw [tCut]
    exact doubleExp_mono.monotone (sub_le_self _ (by positivity))
  have sPow (n : ℕ) : s n ^ n ≤ t n := by rw [tCut]; exact doubleExp_to_pow_le n
  have sLog (n : ℕ) : Real.log (Real.log (s n)) = (n : ℝ) ^ 2 - n := log_log_doubleExp _
  obtain ⟨K, hK⟩ := exists_nat_gt (Y + 4 * B + C / c + 10)
  refine ⟨(1 / η + (D + 1) / b)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  filter_upwards [eventually_gt_atTop (t K)] with x hx
  intro k hk hkx hxk
  have hkK : K ≤ k := by
    by_contra! h
    exact (not_le_of_gt hx) (hxk.trans (tMono.monotone (Nat.succ_le_of_lt h)))
  have hkbig : Y + 4 * B + C / c + 10 < (k : ℝ) := hK.trans_le (Nat.cast_le.mpr hkK)
  have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hkr0 : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hkB : 4 * B ≤ (k : ℝ) := by linarith [div_nonneg hC.le hc.le]
  have hk10 : (10 : ℝ) ≤ (k : ℝ) := by linarith [div_nonneg hC.le hc.le]
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [sq_nonneg ((k : ℝ) - 1)]
  let j := k - 1
  have hjk : j ≤ k := Nat.sub_le _ _
  have hjstep : j + 1 = k := Nat.sub_add_cancel hk
  have hjr : (j : ℝ) = (k : ℝ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hk)
  have hj1 : 1 ≤ j := by
    have h : 2 ≤ k := by exact_mod_cast (show (2 : ℝ) ≤ (k : ℝ) by linarith)
    dsimp [j]
    omega
  have hYj : Y ≤ (j : ℝ) := by
    rw [hjr]
    linarith [div_nonneg hC.le hc.le]
  have hYs (i : ℕ) (hi : j ≤ i) : Y ≤ s i := by
    have hir : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have hi2 : (2 : ℝ) ≤ (i : ℝ) := by rw [hjr] at hir; linarith
    have hprod := mul_nonneg (show (0 : ℝ) ≤ (i : ℝ) by positivity) (sub_nonneg.mpr hi2)
    have hinum : (i : ℝ) ≤ (i : ℝ) ^ 2 - i := by nlinarith only [hprod]
    exact (hYj.trans (hir.trans hinum)).trans (le_doubleExp _)
  have hYtk : Y ≤ t k := (hYs k hjk).trans (sLe k)
  have hYtj : Y ≤ t j := (hYs j le_rfl).trans (sLe j)
  let a := primeMass (t k)
  let q := primeMass x - a
  let S := (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ).toFinset
  let m := ∑ n ∈ S, (1 : ℝ) / n
  let y := a ^ k / (k.factorial : ℝ)
  have hm0 : 0 ≤ m := Finset.sum_nonneg (fun _ _ => by positivity)
  have haL : (k : ℝ) ^ 2 / 2 ≤ a := by
    have hfloor : t k < ((⌊t k⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_floor_add_one (a := t k)
    have hlog : Real.exp ((k : ℝ) ^ 2) ≤ Real.log ((⌊t k⌋₊ + 1 : ℕ) : ℝ) := by
      simpa only [hT k, Real.log_exp] using Real.log_le_log (tPos k) hfloor.le
    have he := Real.exp_le_exp.mp (hlog.trans (log_le_exp_prime_reciprocal_sum ⌊t k⌋₊))
    change (k : ℝ) ^ 2 ≤ 2 * a at he
    linarith
  have ha0 : 0 ≤ a := prime_mass_nonneg _
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have haU : a ≤ U * (k : ℝ) ^ 2 := by
    have he := (hcomp Y (t k) le_rfl hYtk).2
    rw [tLog k] at he
    change a - primeMass Y ≤ C * ((k : ℝ) ^ 2 - Real.log (Real.log Y)) + C at he
    have hprod := mul_nonneg hC.le hlY
    have hcoef : 0 ≤ primeMass Y + C + 1 := by linarith [prime_mass_nonneg Y]
    have hscale := mul_le_mul_of_nonneg_left hk2 hcoef
    dsimp [U]
    nlinarith only [he, hprod, hscale]
  have hsubset (i : ℕ) (hi : j ≤ i) (hik : i ≤ k) :
      η * (a ^ i / (i.factorial : ℝ)) ≤
        ∑ T ∈ (Nat.primesLE ⌊s i⌋₊).powersetCard i, ∏ p ∈ T, (1 : ℝ) / p := by
    have hle : s i ≤ t k := (sLe i).trans (tMono.monotone hik)
    have hs := (hcomp (s i) (t k) (hYs i hi) hle).2
    rw [tLog k, sLog i] at hs
    change a - primeMass (s i) ≤ C * ((k : ℝ) ^ 2 - ((i : ℝ) ^ 2 - i)) + C at hs
    have hir : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
    have hil : (k : ℝ) - 1 ≤ (i : ℝ) := hjr ▸ Nat.cast_le.mpr hi
    have hpw := pow_le_pow_left₀ (show 0 ≤ (k : ℝ) - 1 by linarith) hil 2
    have hd : (k : ℝ) ^ 2 - ((i : ℝ) ^ 2 - i) ≤ 3 * k := by nlinarith only [hpw, hir]
    have hdc := mul_le_mul_of_nonneg_left hd hC.le
    have hCk := mul_le_mul_of_nonneg_left hkone hC.le
    have hbnd : a - B * k ≤ primeMass (s i) - (i : ℝ) / 2 := by
      dsimp [B]
      nlinarith only [hs, hdc, hCk, hir, hkr0]
    exact small_prime_subsets_lower hB.le hk0 hik haL hkB hbnd
  let v := doubleExp ((k : ℝ) ^ 2 - 1)
  have hvj : t j ≤ v := by
    rw [tCut j]
    apply doubleExp_mono.monotone
    rw [hjr]
    nlinarith only [hk10]
  have hvSq : v ^ 2 ≤ t k := by rw [tCut]; exact doubleExp_shift_sq _
  have hprev : c * (k : ℝ) ≤ primeMass v - primeMass (t j) := by
    have he := (hcomp (t j) v hYtj hvj).1
    rw [tLog j, log_log_doubleExp] at he
    change c * ((k : ℝ) ^ 2 - 1 - (j : ℝ) ^ 2) - C ≤ _ at he
    have hCk : C ≤ ((k : ℝ) - 2) * c := (div_le_iff₀ hc).mp (by linarith)
    rw [hjr] at he
    have heq : (k : ℝ) ^ 2 - 1 - ((k : ℝ) - 1) ^ 2 = 2 * k - 2 := by ring
    rw [heq] at he
    nlinarith only [he, hCk]
  have hcut_prev : s j ^ j * v ≤ t (j + 1) := by
    rw [hjstep]
    have hv0 : 0 ≤ v := (doubleExp_pos _).le
    exact (mul_le_mul_of_nonneg_right ((sPow j).trans hvj) hv0).trans
      (by simpa only [pow_two] using hvSq)
  have hprevProduct := tao_mass_from_prime_products t A hA j hj1 (sLe j) hcut_prev
    ((hjstep ▸ hcut_prev : s j ^ j * v ≤ t k).trans hkx.le)
  dsimp only at hprevProduct
  rw [prime_mass_between hvj] at hprevProduct
  have hbase : b * y ≤ m := by
    have hp := previous_factorial_term hk0 ha0 hU haU
    change y / U ≤ (k : ℝ) * (a ^ j / (j.factorial : ℝ)) at hp
    calc
      _ = (η * c) * (y / U) := by dsimp [b]; ring
      _ ≤ (η * c) * ((k : ℝ) * (a ^ j / (j.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (η * (a ^ j / (j.factorial : ℝ))) * (c * (k : ℝ)) := by ring
      _ ≤ (∑ T ∈ (Nat.primesLE ⌊s j⌋₊).powersetCard j, ∏ p ∈ T, (1 : ℝ) / p) *
          (primeMass v - primeMass (t j)) := by
        exact mul_le_mul (hsubset j le_rfl hjk) hprev (by positivity)
          (Finset.sum_nonneg (fun _ _ => by positivity))
      _ ≤ _ := hprevProduct
  have hcurr : η * y * (q - D) ≤ m := by
    by_cases hq : q ≤ D
    · exact (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hη.le hy0) (sub_nonpos.mpr hq)).trans hm0
    let ell := Real.log (Real.log x)
    let u := doubleExp (ell - 1)
    have hx0 : 0 < x := hY0.trans_le (hYtk.trans hkx.le)
    have hx1 : 1 < x := hY1.trans_le (hYtk.trans hkx.le)
    have hxe : doubleExp ell = x := by
      dsimp [doubleExp, ell]
      rw [Real.exp_log (Real.log_pos hx1), Real.exp_log hx0]
    have htu : t k ≤ u := by
      by_contra! h
      have hell : ell - 1 < (k : ℝ) ^ 2 := by
        apply doubleExp_mono.lt_iff_lt.mp
        rw [← tCut]
        exact h
      have hupper := (hcomp (t k) x hYtk hkx.le).2
      change q ≤ C * (ell - Real.log (Real.log (t k))) + C at hupper
      rw [tLog] at hupper
      have hbnd := mul_le_mul_of_nonneg_left (show ell - (k : ℝ) ^ 2 ≤ 1 by linarith) hC.le
      exact hq (by dsimp [D]; linarith only [hupper, hbnd])
    have hux : u ≤ x := by
      rw [← hxe]
      exact doubleExp_mono.monotone (by linarith)
    have huSq : u ^ 2 ≤ x := hxe ▸ doubleExp_shift_sq ell
    have hu0 : 0 ≤ u := (doubleExp_pos _).le
    have huProd : s k ^ k * u ≤ x :=
      (mul_le_mul_of_nonneg_right ((sPow k).trans htu) hu0).trans
        (by simpa only [pow_two] using huSq)
    have hcurrProduct := tao_mass_from_prime_products t A hA k hk (sLe k)
      (huProd.trans hxk) huProd
    dsimp only at hcurrProduct
    rw [prime_mass_between htu] at hcurrProduct
    have hgap := (hcomp u x (hYtk.trans htu) hux).2
    have hlu : Real.log (Real.log u) = ell - 1 := log_log_doubleExp _
    rw [hlu] at hgap
    have hgap' : q - D ≤ primeMass u - a := by
      change primeMass x - primeMass u ≤ C * (ell - (ell - 1)) + C at hgap
      dsimp [q, D]
      linarith only [hgap]
    calc
      _ ≤ (∑ T ∈ (Nat.primesLE ⌊s k⌋₊).powersetCard k, ∏ p ∈ T, (1 : ℝ) / p) *
          (primeMass u - a) := by
        exact mul_le_mul (hsubset k hjk le_rfl) hgap' (sub_nonneg.mpr (le_of_not_ge hq))
          (Finset.sum_nonneg (fun _ _ => by positivity))
      _ ≤ _ := hcurrProduct
  have hq : (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => t k < (p : ℝ)), (1 : ℝ) / p) =
      q := prime_mass_between hkx.le
  dsimp only
  rw [hq]
  exact combine_tao_mass_lower hb hη hD hbase hcurr

open Asymptotics

theorem tao_block_reciprocal_lower (t : ℕ → ℝ)
    (hT : ∀ k, t k = Real.exp (Real.exp ((k : ℝ) ^ 2))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∃ k : ℕ, 1 ≤ k ∧ t k < x ∧ x ≤ t (k + 1) ∧
        let a := ∑ p ∈ Nat.primesLE ⌊t k⌋₊, (1 : ℝ) / p
        2 * (k : ℝ) ≤ a ∧ c * (k : ℝ) ^ 2 ≤ a := by
  have monoT : StrictMono t := by
    intro i j hij
    rw [hT i, hT j]
    exact Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr
      (pow_lt_pow_left₀ (by exact_mod_cast hij) (by positivity) (by decide)))
  have grows (k : ℕ) : (k : ℝ) ≤ t k := by
    rw [hT]
    have h0 := Real.add_one_le_exp ((k : ℝ) ^ 2)
    have h1 := Real.add_one_le_exp (Real.exp ((k : ℝ) ^ 2))
    nlinarith only [h0, h1, sq_nonneg ((k : ℝ) - 1/2)]
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [eventually_gt_atTop (t 4)] with x hx
  have hex : ∃ j : ℕ, x ≤ t j := by
    obtain ⟨j, hj⟩ := exists_nat_gt x
    exact ⟨j, hj.le.trans (grows j)⟩
  let j := Nat.find hex
  have hj : x ≤ t j := Nat.find_spec hex
  have hj4 : 4 < j := by
    by_contra! h
    exact (not_le_of_gt hx) (hj.trans (monoT.monotone h))
  let k := j - 1
  have hk4 : 4 ≤ k := by dsimp [k]; omega
  have hkj : k < j := by dsimp [k]; omega
  have hkjs : k + 1 = j := by dsimp [k]; omega
  refine ⟨k, by omega, lt_of_not_ge (Nat.find_min hex hkj), hkjs.symm ▸ hj, ?_⟩
  let N := ⌊t k⌋₊
  have htk : 0 < t k := by rw [hT]; positivity
  have hfloor : t k < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one (a := t k)
  have hlog : Real.exp ((k : ℝ) ^ 2) ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    have hle := Real.log_le_log htk hfloor.le
    simpa only [hT k, Real.log_exp] using hle
  have hbound := Real.exp_le_exp.mp (hlog.trans (log_le_exp_prime_reciprocal_sum N))
  have hk4' : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
  have hm : 0 ≤ (k : ℝ) * ((k : ℝ) - 4) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hk4')
  dsimp only
  constructor <;> nlinarith only [hbound, hm]

theorem weighted_subsets_factorial_le {α : Type} (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (S : Finset α) (k : ℕ) :
    (k.factorial : ℝ) * (∑ T ∈ S.powersetCard k, ∏ a ∈ T, w a) ≤ (∑ a ∈ S, w a) ^ k := by
  classical
  induction S using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp
    | succ k =>
      have h : (∅ : Finset α).powersetCard (k + 1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [h]
  | @insert a S ha ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hnot (T : Finset α) (hT : T ∈ S.powersetCard k) : a ∉ T :=
        fun ha' => ha ((Finset.mem_powersetCard.mp hT).1 ha')
      have hi : Set.InjOn (insert a) (↑(S.powersetCard k) : Set (Finset α)) := by
        intro T hT U hU he
        have he' := congrArg (fun t : Finset α => t.erase a) he
        rw [Finset.erase_insert (hnot T hT), Finset.erase_insert (hnot U hU)] at he'
        exact he'
      have hd : Disjoint (S.powersetCard (k + 1)) ((S.powersetCard k).image (insert a)) := by
        apply Finset.disjoint_left.mpr
        intro T hT hTa
        obtain ⟨U, hu, hEq⟩ := Finset.mem_image.mp hTa
        subst T
        exact ha ((Finset.mem_powersetCard.mp hT).1 (Finset.mem_insert_self _ _))
      have hsplit :
          (∑ T ∈ (insert a S).powersetCard (k + 1), ∏ b ∈ T, w b) =
            (∑ T ∈ S.powersetCard (k + 1), ∏ b ∈ T, w b) +
              w a * (∑ T ∈ S.powersetCard k, ∏ b ∈ T, w b) := by
        rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hd, Finset.sum_image hi,
          Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun T hT => Finset.prod_insert (hnot T hT))
      let z := ∑ b ∈ S, w b
      have hz : 0 ≤ z := Finset.sum_nonneg (fun b _ => hw b)
      rw [hsplit, Finset.sum_insert ha, add_comm (w a)]
      calc
        _ = ((k + 1).factorial : ℝ) * (∑ T ∈ S.powersetCard (k + 1), ∏ b ∈ T, w b) +
              (((k + 1 : ℕ) : ℝ) * w a) *
                ((k.factorial : ℝ) * (∑ T ∈ S.powersetCard k, ∏ b ∈ T, w b)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ z ^ (k + 1) + (((k + 1 : ℕ) : ℝ) * w a) * z ^ k :=
          add_le_add (ih (k + 1)) (mul_le_mul_of_nonneg_left (ih k) (mul_nonneg (by positivity) (hw a)))
        _ = z ^ (k + 1) + ((k + 1 : ℕ) : ℝ) * z ^ ((k + 1) - 1) * w a := by
          rw [Nat.add_sub_cancel]
          ring
        _ ≤ _ := pow_add_mul_le_add_pow hz (by linarith [hw a]) (k + 1)

lemma reciprocal_sum_le_factor_families (S P Q : Finset ℕ) (hPQ : Disjoint P Q)
    (F G : Finset (Finset ℕ)) (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
        n.primeFactors ∩ P ∈ F ∧ n.primeFactors ∩ Q ∈ G) :
    ∑ n ∈ S, (1 : ℝ) / n ≤
      (∑ T ∈ F, ∏ p ∈ T, (1 : ℝ) / p) * (∑ U ∈ G, ∏ p ∈ U, (1 : ℝ) / p) := by
  classical
  let f (n : ℕ) := (n.primeFactors ∩ P, n.primeFactors ∩ Q)
  let w (r : Finset ℕ × Finset ℕ) : ℝ := (∏ p ∈ r.1, (1 : ℝ) / p) * (∏ p ∈ r.2, (1 : ℝ) / p)
  have parts_union (n : ℕ) (hn : n ∈ S) : (f n).1 ∪ (f n).2 = n.primeFactors := by
    change (n.primeFactors ∩ P) ∪ (n.primeFactors ∩ Q) = n.primeFactors
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr (hS n hn).2.1]
  have hf : Set.InjOn f ↑S := by
    intro n hn m hm hnm
    have h := congrArg (fun r : Finset ℕ × Finset ℕ => r.1 ∪ r.2) hnm
    change (f n).1 ∪ (f n).2 = (f m).1 ∪ (f m).2 at h
    rw [parts_union n hn, parts_union m hm] at h
    exact (Nat.prod_primeFactors_of_squarefree (hS n hn).1).symm.trans
      (h ▸ Nat.prod_primeFactors_of_squarefree (hS m hm).1)
  have hsub : S.image f ⊆ F ×ˢ G := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr (hS n hn).2.2
  have hweight (n : ℕ) (hn : n ∈ S) : w (f n) = (1 : ℝ) / n := by
    have hdis : Disjoint (f n).1 (f n).2 :=
      hPQ.mono Finset.inter_subset_right Finset.inter_subset_right
    dsimp [w]
    rw [← Finset.prod_union hdis, parts_union n hn]
    have hp : (∏ p ∈ n.primeFactors, (p : ℝ)) = (n : ℝ) := by
      rw [← Nat.cast_prod (fun p : ℕ => p) n.primeFactors, Nat.prod_primeFactors_of_squarefree (hS n hn).1]
    simp only [one_div, Finset.prod_inv_distrib, hp]
  calc
    _ = ∑ n ∈ S, w (f n) := Finset.sum_congr rfl (fun n hn => (hweight n hn).symm)
    _ = ∑ a ∈ S.image f, w a := (Finset.sum_image hf).symm
    _ ≤ ∑ a ∈ F ×ˢ G, w a := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by
      dsimp [w]
      positivity)
    _ = _ := by
      rw [Finset.sum_product]
      simp only [w, ← Finset.mul_sum, ← Finset.sum_mul]

lemma powerset_le_eq_biUnion (P : Finset ℕ) (k : ℕ) :
    (P.powerset.filter (fun T => T.card ≤ k)) =
      (Finset.range (k + 1)).biUnion (fun j => P.powersetCard j) := by
  ext T
  rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion]
  constructor
  · rintro ⟨hsub, hcard⟩
    exact ⟨T.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hcard),
      Finset.mem_powersetCard.mpr ⟨hsub, rfl⟩⟩
  · rintro ⟨j, hj, hT⟩
    obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hT
    exact ⟨hsub, hc ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hj)⟩

lemma prime_weights_sum_le {P : Finset ℕ} (j : ℕ) :
    ∑ T ∈ P.powersetCard j, ∏ p ∈ T, (1 : ℝ) / p ≤
      (∑ p ∈ P, (1 : ℝ) / p) ^ j / (j.factorial : ℝ) := by
  have hf : 0 < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  apply (le_div_iff₀ hf).mpr
  rw [mul_comm]
  exact weighted_subsets_factorial_le (fun p : ℕ => (1 : ℝ) / p) (fun _ => by positivity) P j

lemma prime_weights_sum_at_most {P : Finset ℕ} (k : ℕ) :
    ∑ T ∈ P.powerset.filter (fun T => T.card ≤ k), ∏ p ∈ T, (1 : ℝ) / p ≤
      ∑ j ∈ Finset.range (k + 1), (∑ p ∈ P, (1 : ℝ) / p) ^ j / (j.factorial : ℝ) := by
  classical
  rw [powerset_le_eq_biUnion]
  have hd : (↑(Finset.range (k + 1)) : Set ℕ).PairwiseDisjoint (fun j => P.powersetCard j) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro T hTi hTj
    exact hij ((Finset.mem_powersetCard.mp hTi).2.symm.trans (Finset.mem_powersetCard.mp hTj).2)
  rw [Finset.sum_biUnion hd]
  exact Finset.sum_le_sum (fun j _ => prime_weights_sum_le j)

lemma reciprocal_exact_profile_bound (S P Q : Finset ℕ) (hPQ : Disjoint P Q)
    (j b : ℕ)
    (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
      (n.primeFactors ∩ P).card = j ∧ (n.primeFactors ∩ Q).card = b) :
    ∑ n ∈ S, (1 : ℝ) / n ≤
      ((∑ p ∈ P, (1 : ℝ) / p) ^ j / (j.factorial : ℝ)) *
        ((∑ p ∈ Q, (1 : ℝ) / p) ^ b / (b.factorial : ℝ)) := by
  classical
  calc
    _ ≤ (∑ T ∈ P.powersetCard j, ∏ p ∈ T, (1 : ℝ) / p) *
        (∑ U ∈ Q.powersetCard b, ∏ p ∈ U, (1 : ℝ) / p) := by
      apply reciprocal_sum_le_factor_families S P Q hPQ
      intro n hn
      obtain ⟨hsf, hsub, hP, hQ⟩ := hS n hn
      exact ⟨hsf, hsub, Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hP⟩,
        Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hQ⟩⟩
    _ ≤ _ := mul_le_mul (prime_weights_sum_le j) (prime_weights_sum_le b)
      (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)

lemma reciprocal_bounded_profile (S P Q : Finset ℕ) (hPQ : Disjoint P Q)
    (j b : ℕ)
    (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
      (n.primeFactors ∩ P).card ≤ j ∧ (n.primeFactors ∩ Q).card ≤ b) :
    ∑ n ∈ S, (1 : ℝ) / n ≤
      (∑ l ∈ Finset.range (j + 1), (∑ p ∈ P, (1 : ℝ) / p) ^ l / (l.factorial : ℝ)) *
        (∑ l ∈ Finset.range (b + 1), (∑ p ∈ Q, (1 : ℝ) / p) ^ l / (l.factorial : ℝ)) := by
  classical
  calc
    _ ≤ (∑ T ∈ P.powerset.filter (fun T => T.card ≤ j), ∏ p ∈ T, (1 : ℝ) / p) *
        (∑ U ∈ Q.powerset.filter (fun U => U.card ≤ b), ∏ p ∈ U, (1 : ℝ) / p) := by
      apply reciprocal_sum_le_factor_families S P Q hPQ
      intro n hn
      obtain ⟨hsf, hsub, hP, hQ⟩ := hS n hn
      exact ⟨hsf, hsub,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, hP⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, hQ⟩⟩
    _ ≤ _ := mul_le_mul (prime_weights_sum_at_most j) (prime_weights_sum_at_most b)
      (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)

lemma divisor_profile_of_support (P Q : Finset ℕ) {n d k : ℕ}
    (hn : Squarefree n) (hd : d ∣ n) (hsub : n.primeFactors ⊆ P ∪ Q)
    (hP : (n.primeFactors ∩ P).card ≤ k) (hQ : (n.primeFactors ∩ Q).card ≤ 1) :
    Squarefree d ∧ d.primeFactors ⊆ P ∪ Q ∧
      (d.primeFactors ∩ P).card ≤ k ∧ (d.primeFactors ∩ Q).card ≤ 1 := by
  have hm := Nat.primeFactors_mono hd hn.ne_zero
  exact ⟨hn.squarefree_of_dvd hd, hm.trans hsub,
    (Finset.card_le_card (Finset.inter_subset_inter_right hm)).trans hP,
    (Finset.card_le_card (Finset.inter_subset_inter_right hm)).trans hQ⟩

lemma quotient_profile_of_support (P Q : Finset ℕ) {n d k : ℕ}
    (hn : Squarefree n) (hd : d ∣ n) (hsub : n.primeFactors ⊆ P ∪ Q)
    (hP : (n.primeFactors ∩ P).card ≤ k) (hQ : (n.primeFactors ∩ Q).card ≤ 1) :
    Squarefree (n / d) ∧ (n / d).primeFactors ⊆ P ∪ Q ∧
      ((n / d).primeFactors ∩ P).card ≤ k - (d.primeFactors ∩ P).card ∧
      ((n / d).primeFactors ∩ Q).card ≤ 1 - (d.primeFactors ∩ Q).card := by
  have hd0 : d ≠ 0 := by
    intro he
    subst d
    exact hn.ne_zero (zero_dvd_iff.mp hd)
  have hdiff : (n / d).primeFactors = n.primeFactors \ d.primeFactors := by
    simpa only [Nat.gcd_eq_right_iff_dvd.mpr hd] using Nat.primeFactors_div_gcd hn hd0
  have hcount (T : Finset ℕ) : ((n / d).primeFactors ∩ T).card =
      (n.primeFactors ∩ T).card - (d.primeFactors ∩ T).card := by
    have hm : d.primeFactors ∩ T ⊆ n.primeFactors ∩ T :=
      Finset.inter_subset_inter_right (Nat.primeFactors_mono hd hn.ne_zero)
    have he : (n / d).primeFactors ∩ T = (n.primeFactors ∩ T) \ (d.primeFactors ∩ T) := by
      ext x
      rw [hdiff]
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rw [he, Finset.card_sdiff_of_subset hm]
  refine ⟨hn.squarefree_of_dvd (Nat.div_dvd_of_dvd hd), ?_, ?_, ?_⟩
  · rw [hdiff]
    exact Finset.sdiff_subset.trans hsub
  · rw [hcount]
    exact Nat.sub_le_sub_right hP _
  · rw [hcount]
    exact Nat.sub_le_sub_right hQ _

lemma truncated_exponential_le {a : ℝ} (ha : 0 < a) (k : ℕ) (hk : 2 * (k : ℝ) ≤ a) :
    ∑ j ∈ Finset.range (k + 1), a ^ j / (j.factorial : ℝ) ≤ 2 * (a ^ k / (k.factorial : ℝ)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hk' : 2 * (k : ℝ) ≤ a := by
      rw [Nat.cast_succ] at hk
      linarith
    have hstep : 2 * (a ^ k / (k.factorial : ℝ)) ≤ a ^ (k + 1) / ((k + 1).factorial : ℝ) := by
      have hfactorial : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
      have hfactorial' : 0 < ((k + 1).factorial : ℝ) := by exact_mod_cast (k + 1).factorial_pos
      apply (le_div_iff₀ hfactorial').mpr
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      have heq : 2 * (a ^ k / (k.factorial : ℝ)) * (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ)) =
          a ^ k * (2 * ((k + 1 : ℕ) : ℝ)) := by field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left hk (by positivity)
    rw [Finset.sum_range_succ]
    linarith [ih hk']

lemma tao_support_at_cutoff (t : ℕ → ℝ) (ht : StrictMono t) (A : Set ℕ)
    (hA : ∀ n, n ∈ A ↔ Squarefree n ∧ ∃ k : ℕ, 1 ≤ k ∧
      t k < (n : ℝ) ∧ (n : ℝ) ≤ t (k + 1) ∧
      (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k)).card ≤ k ∧
      (n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ))).card ≤ 1)
    (x : ℝ) (k : ℕ) (hx : x ≤ t (k + 1)) (hx0 : 0 ≤ x)
    (n : ℕ) (hn : n ∈ (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ)) :
    let P := Nat.primesLE ⌊t k⌋₊
    let Q := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
    Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
      (n.primeFactors ∩ P).card ≤ k ∧ (n.primeFactors ∩ Q).card ≤ 1 := by
  classical
  dsimp
  let P := Nat.primesLE ⌊t k⌋₊
  let Q := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
  obtain ⟨hsf, i, hi, hil, hiu, hiP, hiQ⟩ := (hA n).mp hn.1
  have hntop : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn.2.2).trans (Nat.floor_le hx0)
  have hi_le : i ≤ k := by
    by_contra! h
    exact (not_lt_of_ge (hntop.trans (hx.trans (ht.monotone (by omega))))) hil
  have Pmem (p : ℕ) (hp : p ∈ n.primeFactors) : p ∈ P ↔ (p : ℝ) ≤ t k := by
    have hp' := (Nat.mem_primeFactors.mp hp).1
    rw [Nat.mem_primesLE, and_iff_left hp', Nat.le_floor_iff' hp'.ne_zero]
  have Qmem (p : ℕ) (hp : p ∈ n.primeFactors) : p ∈ Q ↔ t k < (p : ℝ) := by
    obtain ⟨hp', hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    have hle := (Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) hdvd).trans hn.2.2
    rw [Finset.mem_filter, Nat.mem_primesLE, and_iff_right ⟨hle, hp'⟩]
  have hsub : n.primeFactors ⊆ P ∪ Q := by
    intro p hp
    rcases le_or_gt (p : ℝ) (t k) with h | h
    · exact Finset.mem_union_left _ ((Pmem p hp).mpr h)
    · exact Finset.mem_union_right _ ((Qmem p hp).mpr h)
  have hPf : n.primeFactors ∩ P = n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ t k) := by
    ext p
    rw [Finset.mem_inter, Finset.mem_filter]
    exact and_congr_right (Pmem p)
  have hQf : n.primeFactors ∩ Q = n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ)) := by
    ext p
    simpa only [Finset.mem_inter, Finset.mem_filter] using (and_congr_right (Qmem p))
  refine ⟨hsf, hsub, ?_⟩
  by_cases he : i = k
  · subst i
    exact ⟨by rw [hPf]; exact hiP, by rw [hQf]; exact hiQ⟩
  have hin : i + 1 ≤ k := by omega
  have hncut : (n : ℝ) ≤ t k := hiu.trans (ht.monotone hin)
  have hncard : n.primeFactors.card ≤ k := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := n.primeFactors) (p := fun p : ℕ => (p : ℝ) ≤ t i)
    simp only [not_le] at hsum
    omega
  refine ⟨(Finset.card_le_card Finset.inter_subset_left).trans hncard, ?_⟩
  rw [hQf]
  have hempty : n.primeFactors.filter (fun p : ℕ => t k < (p : ℝ)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp, hpgt⟩ := Finset.mem_filter.mp hp
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) (Nat.mem_primeFactors.mp hp).2.1
    exact (not_lt_of_ge ((Nat.cast_le.mpr hle).trans hncut)) hpgt
  rw [hempty]
  decide

lemma log_reciprocal_mass_close {k : ℕ} {a q M δ U C : ℝ}
    (hk : 1 ≤ k) (hδ : 0 < δ) (hU : 0 < U) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hqU : q ≤ 4 * C * (k : ℝ))
    (haL : (k : ℝ) ^ 2 / 2 ≤ a) (haU : a ≤ U * (k : ℝ) ^ 2)
    (hML : δ * (1 + q) * (a ^ k / (k.factorial : ℝ)) ≤ M)
    (hMU : M ≤ 2 * (1 + q) * (a ^ k / (k.factorial : ℝ))) :
    0 < M ∧
      |Real.log M - (k : ℝ) * Real.log k| ≤
        (|Real.log δ| + |Real.log U| + Real.log 2 + 4 * C + 1) * (k : ℝ) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : 0 < (k : ℝ) := zero_lt_one.trans_le hk1
  have ha0 : 0 < a := (by positivity : 0 < (k : ℝ) ^ 2 / 2).trans_le haL
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hM : 0 < M := (by positivity : 0 < δ * (1 + q) * (a ^ k / (k.factorial : ℝ))).trans_le hML
  have hq1 : 0 < 1 + q := by linarith
  have hi : 0 ≤ Real.log (1 + q) := Real.log_nonneg (by linarith)
  have hlogq : Real.log (1 + q) ≤ q := by linarith [Real.log_le_sub_one_of_pos hq1]
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have haLogL : 2 * Real.log (k : ℝ) - Real.log 2 ≤ Real.log a := by
    have he := Real.log_le_log (by positivity : 0 < (k : ℝ) ^ 2 / 2) haL
    rw [Real.log_div (pow_ne_zero _ hk0.ne') (by norm_num), Real.log_pow] at he
    exact_mod_cast he
  have haLogU : Real.log a ≤ Real.log U + 2 * Real.log (k : ℝ) := by
    have he := Real.log_le_log ha0 haU
    rw [Real.log_mul hU.ne' (pow_ne_zero _ hk0.ne'), Real.log_pow] at he
    exact_mod_cast he
  have hfU : Real.log (k.factorial : ℝ) ≤ (k : ℝ) * Real.log (k : ℝ) := by
    have he := Real.log_le_log hf (show (k.factorial : ℝ) ≤ (k : ℝ) ^ k by
      exact_mod_cast k.factorial_le_pow)
    simpa only [Real.log_pow] using he
  have hfL : (k : ℝ) * Real.log (k : ℝ) - k ≤ Real.log (k.factorial : ℝ) := by
    have hkN : k ≠ 0 := Nat.ne_zero_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
    have h := Stirling.le_log_factorial_stirling hkN
    have hp : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith only [h, hp, hlogk]
  have hML' : Real.log δ + Real.log (1 + q) + (k : ℝ) * Real.log a -
      Real.log (k.factorial : ℝ) ≤ Real.log M := by
    have h := Real.log_le_log (by positivity : 0 < δ * (1 + q) * (a ^ k / (k.factorial : ℝ))) hML
    rw [Real.log_mul (mul_ne_zero hδ.ne' hq1.ne') (div_ne_zero (pow_ne_zero _ ha0.ne') hf.ne'),
        Real.log_mul hδ.ne' hq1.ne', Real.log_div (pow_ne_zero _ ha0.ne') hf.ne', Real.log_pow] at h
    linarith only [h]
  have hMU' : Real.log M ≤ Real.log 2 + Real.log (1 + q) + (k : ℝ) * Real.log a -
      Real.log (k.factorial : ℝ) := by
    have h := Real.log_le_log hM hMU
    rw [Real.log_mul (mul_ne_zero (by norm_num) hq1.ne') (div_ne_zero (pow_ne_zero _ ha0.ne') hf.ne'),
        Real.log_mul (by norm_num) hq1.ne', Real.log_div (pow_ne_zero _ ha0.ne') hf.ne', Real.log_pow] at h
    linarith only [h]
  have hδlog : -(|Real.log δ| * (k : ℝ)) ≤ Real.log δ := by
    have h := mul_le_mul_of_nonneg_left hk1 (abs_nonneg (Real.log δ))
    nlinarith only [h, neg_abs_le (Real.log δ)]
  have hUpperU := mul_le_mul_of_nonneg_right (le_abs_self (Real.log U)) hk0.le
  have hUpper2 := mul_le_mul_of_nonneg_left hk1 hlog2
  have hLowerA := mul_le_mul_of_nonneg_left haLogL hk0.le
  have hUpperA := mul_le_mul_of_nonneg_left haLogU hk0.le
  have hEC : 0 ≤ (4 * C) * (k : ℝ) := by positivity
  have hEδ : 0 ≤ |Real.log δ| * (k : ℝ) := by positivity
  have hEU : 0 ≤ |Real.log U| * (k : ℝ) := by positivity
  refine ⟨hM, abs_le.mpr ⟨?_, ?_⟩⟩
  · nlinarith only [hML', hLowerA, hfU, hi, hδlog, hEU, hEC, hk0.le]
  · nlinarith only [hMU', hUpperA, hfL, hlogq, hqU, hUpperU, hUpper2, hEδ]

lemma tao_scale_close {k : ℕ} {s : ℝ}
    (hk : 1 ≤ k) (hs : (k : ℝ) ^ 2 ≤ s) (hS : s ≤ ((k + 1 : ℕ) : ℝ) ^ 2) :
    (k : ℝ) * Real.log (k : ℝ) ≤ √s * Real.log s / 2 ∧
      √s * Real.log s / 2 - (k : ℝ) * Real.log (k : ℝ) ≤ 2 * (k : ℝ) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < (k : ℝ) := zero_lt_one.trans_le hkr
  have hs0 : 0 < s := (by positivity : 0 < (k : ℝ) ^ 2).trans_le hs
  have hk1 : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hsqL : (k : ℝ) ≤ √s := by
    have h := Real.sqrt_le_sqrt hs
    rwa [Real.sqrt_sq hk0.le] at h
  have hsqU : √s ≤ ((k + 1 : ℕ) : ℝ) := by
    have h := Real.sqrt_le_sqrt hS
    rwa [Real.sqrt_sq hk1.le] at h
  have hlogL : 2 * Real.log (k : ℝ) ≤ Real.log s := by
    have he := Real.log_le_log (by positivity : 0 < (k : ℝ) ^ 2) hs
    rw [Real.log_pow] at he
    exact_mod_cast he
  have hlogU : Real.log s ≤ 2 * Real.log ((k + 1 : ℕ) : ℝ) := by
    have he := Real.log_le_log hs0 hS
    rw [Real.log_pow] at he
    exact_mod_cast he
  have hLog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkr
  have hLogS : 0 ≤ Real.log s := by linarith
  have hlo := mul_le_mul hsqL hlogL (by positivity : 0 ≤ 2 * Real.log (k : ℝ)) (Real.sqrt_nonneg s)
  have hhi := mul_le_mul hsqU hlogU hLogS hk1.le
  have hstep : Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hk1 hk0)
    rw [Real.log_div hk1.ne' hk0.ne'] at h
    have he : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
      push_cast
      field_simp
      ring
    rwa [he] at h
  have hstep' := mul_le_mul_of_nonneg_left hstep hk0.le
  have hlogK1 := Real.log_le_sub_one_of_pos hk1
  rw [mul_one_div_cancel hk0.ne'] at hstep'
  push_cast at hhi hlogK1 hstep'
  constructor
  · nlinarith only [hlo]
  · nlinarith only [hhi, hstep', hlogK1, hkr]

end OMA.TaoAsymptotic

open OMA.TaoAsymptotic

theorem OMA.solution : OMA.R_Erdos442_erdos_442_variants_tao_R1.H1 := by
  intro t A hT hA
  classical
  obtain ⟨δ, hδ, hlower⟩ := tao_reciprocal_mass_lower t A hT hA
  obtain ⟨_, _, hblocks⟩ := tao_block_reciprocal_lower t hT
  obtain ⟨Y, hY, hcomp⟩ := prime_mass_log_log_comparison
  let L := Erdos442.Real.maxLogOne
  let R (x : ℝ) := √(L (L x)) * L (L (L x))
  let M (x : ℝ) := ∑ n ∈ (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ).toFinset, (1 : ℝ) / n
  let f (x : ℝ) := Real.log (M x) / R x - 1 / 2
  let C := Real.log 4 + 1
  let U := primeMass Y + 2 * C + 1
  let E := |Real.log δ| + |Real.log U| + Real.log 2 + 4 * C + 3
  have hC : 0 < C := by
    dsimp [C]
    linarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)]
  have hU : 0 < U := by dsimp [U]; linarith [prime_mass_nonneg Y]
  have hE : 0 < E := by dsimp [E]; positivity
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hlogY : 1 ≤ Real.log Y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hY
  have hloglogY : 0 ≤ Real.log (Real.log Y) := Real.log_nonneg hlogY
  have tCut (n : ℕ) : t n = doubleExp ((n : ℝ) ^ 2) := hT n
  have tPos (n : ℕ) : 0 < t n := tCut n ▸ doubleExp_pos _
  have tMono : StrictMono t := by
    intro i j h
    rw [tCut i, tCut j]
    exact doubleExp_mono (pow_lt_pow_left₀ (by exact_mod_cast h) (by positivity) (by decide))
  have tLog (n : ℕ) : Real.log (Real.log (t n)) = (n : ℝ) ^ 2 := by rw [tCut, log_log_doubleExp]
  have data (r : ℝ) (hr : 1 ≤ r) :
      ∀ᶠ x : ℝ in atTop, ∃ k : ℕ, 1 ≤ k ∧ r ≤ Real.log (k : ℝ) ∧
        0 < M x ∧ 2 * (k : ℝ) * Real.log (k : ℝ) ≤ R x ∧
        |Real.log (M x) - R x / 2| ≤ E * (k : ℝ) := by
    obtain ⟨K, hK⟩ := exists_nat_gt (Y + Real.exp r + 2)
    filter_upwards [hblocks, hlower, eventually_gt_atTop (t K)] with x hxblocks hxmass hxK
    obtain ⟨k, hk, hkx, hxk, hka, hqA⟩ := hxblocks
    have hkN : K ≤ k := by
      by_contra! h
      exact (not_le_of_gt hxK) (hxk.trans (tMono.monotone (Nat.succ_le_of_lt h)))
    have hkbig : Y + Real.exp r + 2 < (k : ℝ) := hK.trans_le (Nat.cast_le.mpr hkN)
    have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk0 : 0 < (k : ℝ) := zero_lt_one.trans_le hkr
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      simpa only [one_pow] using (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hkr 2)
    have hpow : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr hkr)]
    have hYtk : Y ≤ t k := by
      rw [tCut]
      exact (show Y ≤ (k : ℝ) by linarith [Real.exp_pos r]).trans (hpow.trans (le_doubleExp _))
    have hrk : r ≤ Real.log (k : ℝ) := by
      have he : Real.exp r ≤ (k : ℝ) := by linarith [Real.exp_pos r]
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos r) he
    let S := (A ∩ Set.Icc 1 ⌊x⌋₊ : Set ℕ).toFinset
    let P := Nat.primesLE ⌊t k⌋₊
    let Q := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => t k < (p : ℝ))
    let a := primeMass (t k)
    let q := primeMass x - a
    have hqeq : ∑ p ∈ Q, (1 : ℝ) / p = q := prime_mass_between hkx.le
    have hq0 : 0 ≤ q := sub_nonneg.mpr (prime_mass_mono hkx.le)
    have ha0 : 0 < a := by
      change 2 * (k : ℝ) ≤ a at hka
      linarith
    have haL : (k : ℝ) ^ 2 / 2 ≤ a := by
      have hfloor : t k < ((⌊t k⌋₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_floor_add_one (a := t k)
      have he : Real.exp ((k : ℝ) ^ 2) ≤ Real.log ((⌊t k⌋₊ + 1 : ℕ) : ℝ) := by
        simpa only [hT k, Real.log_exp] using Real.log_le_log (tPos k) hfloor.le
      have hp := Real.exp_le_exp.mp (he.trans (log_le_exp_prime_reciprocal_sum ⌊t k⌋₊))
      change (k : ℝ) ^ 2 ≤ 2 * a at hp
      linarith
    have haU : a ≤ U * (k : ℝ) ^ 2 := by
      have he := (hcomp Y (t k) le_rfl hYtk).2
      rw [tLog k] at he
      change a - primeMass Y ≤ C * ((k : ℝ) ^ 2 - Real.log (Real.log Y)) + C at he
      have hprod := mul_nonneg hC.le hloglogY
      have hcoef : 0 ≤ primeMass Y + C + 1 := by linarith [prime_mass_nonneg Y]
      have hscale := mul_le_mul_of_nonneg_left hk2 hcoef
      dsimp [U]
      nlinarith only [he, hprod, hscale]
    let s := Real.log (Real.log x)
    have hx0 : 0 < x := (tPos k).trans hkx
    have hx1 : 1 < x := by
      have h1 : 1 < Real.exp 1 := by
        have h : Real.exp 0 < Real.exp 1 := Real.exp_strictMono zero_lt_one
        simpa only [Real.exp_zero] using h
      exact h1.trans_le (hY.trans (hYtk.trans hkx.le))
    have hxe : doubleExp s = x := by
      dsimp [doubleExp, s]
      rw [Real.exp_log (Real.log_pos hx1), Real.exp_log hx0]
    have hsL : (k : ℝ) ^ 2 ≤ s := by
      apply doubleExp_mono.le_iff_le.mp
      rw [← tCut, hxe]
      exact hkx.le
    have hsU : s ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
      apply doubleExp_mono.le_iff_le.mp
      rw [← tCut, hxe]
      exact hxk
    have hqU : q ≤ 4 * C * (k : ℝ) := by
      have h := (hcomp (t k) x hYtk hkx.le).2
      rw [tLog k] at h
      change q ≤ C * (s - (k : ℝ) ^ 2) + C at h
      have hdiff : s - (k : ℝ) ^ 2 ≤ 2 * (k : ℝ) + 1 := by
        push_cast at hsU
        nlinarith only [hsU]
      have he := mul_le_mul_of_nonneg_left hdiff hC.le
      have h1 := mul_le_mul_of_nonneg_left hkr hC.le
      nlinarith only [h, he, h1]
    have hML : δ * (1 + q) * (a ^ k / (k.factorial : ℝ)) ≤ M x := by
      have he := hxmass k hk hkx hxk
      dsimp only at he
      rw [hqeq] at he
      exact he
    have hMU : M x ≤ 2 * (1 + q) * (a ^ k / (k.factorial : ℝ)) := by
      have hPQ : Disjoint P Q := by
        apply Finset.disjoint_left.mpr
        intro p hp hq'
        have hp' : p ≤ ⌊t k⌋₊ := (Nat.mem_primesLE.mp hp).1
        have hle : (p : ℝ) ≤ t k := (Nat.cast_le.mpr hp').trans (Nat.floor_le (tPos k).le)
        exact (not_lt_of_ge hle) (Finset.mem_filter.mp hq').2
      have hS (n : ℕ) (hn : n ∈ S) : Squarefree n ∧ n.primeFactors ⊆ P ∪ Q ∧
          (n.primeFactors ∩ P).card ≤ k ∧ (n.primeFactors ∩ Q).card ≤ 1 :=
        tao_support_at_cutoff t tMono A hA x k hxk hx0.le n (Set.mem_toFinset.mp hn)
      have he := reciprocal_bounded_profile S P Q hPQ k 1 hS
      rw [hqeq] at he
      have hterm : (∑ j ∈ Finset.range (k + 1), a ^ j / (j.factorial : ℝ)) ≤
          2 * (a ^ k / (k.factorial : ℝ)) :=
        truncated_exponential_le ha0 k hka
      have hqterm : (∑ j ∈ Finset.range (1 + 1), q ^ j / (j.factorial : ℝ)) = 1 + q := by
        norm_num [Finset.sum_range_succ, add_comm]
      change M x ≤ (∑ j ∈ Finset.range (k + 1), a ^ j / (j.factorial : ℝ)) *
        (∑ j ∈ Finset.range (1 + 1), q ^ j / (j.factorial : ℝ)) at he
      rw [hqterm] at he
      exact he.trans ((mul_le_mul_of_nonneg_right hterm (by positivity)).trans_eq (by ring))
    have hR : R x = √s * Real.log s := by
      have hs0 : 0 ≤ s := (by positivity : 0 ≤ (k : ℝ) ^ 2).trans hsL
      have hs1 : 1 ≤ s := hk2.trans hsL
      have hXlog : Real.log x = Real.exp s := by rw [← hxe, doubleExp, Real.log_exp]
      have hL1 : L x = Real.log x := max_eq_left (hXlog.symm ▸ Real.one_le_exp hs0)
      have hL2 : L (L x) = s := by rw [hL1]; exact max_eq_left hs1
      have hlogS : 1 ≤ Real.log s := by
        have he := Real.log_le_log (by positivity : 0 < (k : ℝ) ^ 2) hsL
        rw [Real.log_pow] at he
        norm_num at he
        linarith
      have hL3 : L (L (L x)) = Real.log s := by rw [hL2]; exact max_eq_left hlogS
      change √(L (L x)) * L (L (L x)) = _
      rw [hL3, hL2]
    obtain ⟨hmpos, hmass⟩ := log_reciprocal_mass_close hk hδ hU hC.le hq0 hqU haL haU hML hMU
    obtain ⟨hRL, hRU⟩ := tao_scale_close hk hsL hsU
    rw [← hR] at hRL hRU
    refine ⟨k, hk, hrk, hmpos, by nlinarith only [hRL], ?_⟩
    obtain ⟨hML, hMU⟩ := abs_le.mp hmass
    apply abs_le.mpr
    dsimp [E]
    constructor
    · nlinarith only [hML, hRU]
    · nlinarith only [hMU, hRL, hk0.le]
  have Rpos (x : ℝ) : 0 < R x := by
    have hL (y : ℝ) : 1 ≤ L y := le_max_right _ _
    exact mul_pos (Real.sqrt_pos_of_pos (zero_lt_one.trans_le (hL _))) (zero_lt_one.trans_le (hL _))
  refine ⟨f, ?_, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hr : 1 ≤ 1 + E / ε := le_add_of_nonneg_right (div_nonneg hE.le hε.le)
    filter_upwards [data (1 + E / ε) hr] with x hx
    obtain ⟨k, hk, hlogk, hM, hR, hErr⟩ := hx
    have hk0 : 0 < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    have heq : f x = (Real.log (M x) - R x / 2) / R x := by
      dsimp [f]
      field_simp [(Rpos x).ne'] <;> ring
    rw [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs, heq, abs_div, abs_of_pos (Rpos x)]
    apply (div_le_iff₀ (Rpos x)).mpr
    apply hErr.trans
    have hlogk1 : (1 : ℝ) ≤ Real.log (k : ℝ) := hr.trans hlogk
    have hEL : E ≤ ε * Real.log (k : ℝ) := by
      have he : E / ε ≤ Real.log (k : ℝ) := by linarith only [hlogk]
      nlinarith only [(div_le_iff₀ hε).mp he]
    have hklog : 0 ≤ (k : ℝ) * Real.log (k : ℝ) := mul_nonneg hk0.le (by linarith)
    calc
      _ ≤ (ε * Real.log (k : ℝ)) * (k : ℝ) := mul_le_mul_of_nonneg_right hEL hk0.le
      _ ≤ ε * (2 * (k : ℝ) * Real.log (k : ℝ)) := by nlinarith only [mul_nonneg hε.le hklog]
      _ ≤ _ := mul_le_mul_of_nonneg_left hR hε.le
  · filter_upwards [data 1 le_rfl] with x hx
    obtain ⟨_, _, _, hM, _, _⟩ := hx
    change M x = Real.exp ((1 / 2 + f x) * √(L (L x)) * L (L (L x)))
    rw [← Real.exp_log hM]
    congr 1
    change Real.log (M x) = (1 / 2 + f x) * √(L (L x)) * L (L (L x))
    rw [mul_assoc]
    change Real.log (M x) = (1 / 2 + f x) * R x
    dsimp only [f]
    field_simp [(Rpos x).ne'] <;> ring
