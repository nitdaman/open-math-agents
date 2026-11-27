import FormalConjectures.ErdosProblems.«1129»

-- Problem: Erdős Problem 1129 — chebyshev upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1129.lean:244 (declaration Erdos1129.erdos_1129.variants.chebyshev_upper_bound)
-- Credit: @koolkao (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea: for x = cos t and Chebyshev angles t_k, |l_k(x)| = |cos(n t)| sin t_k / (n |x - x_k|);
-- split sin t_k / (cos t - cos t_k) into two half-angle cotangents, bound each by min(1, 1/(pi d))
-- with d the distance to an integer point of a window of width 2n, and sum to 2 + (2/pi)(1 + log n).

namespace OMA.E1129

open Erdos1129 Finset Real Polynomial

noncomputable def fdist (d : ℝ) : ℝ := min 1 (1 / (π * d))

noncomputable def gharm (i : ℕ) : ℝ := if i = 0 then 1 else 1 / (π * i)

lemma fdist_le_gharm {d : ℝ} {i : ℕ} (h : (i : ℝ) ≤ d) : fdist d ≤ gharm i := by
  unfold fdist gharm
  split_ifs with hi
  · exact min_le_left _ _
  · have hi' : (0 : ℝ) < i := by exact_mod_cast Nat.pos_of_ne_zero hi
    refine (min_le_right _ _).trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left h pi_pos.le

lemma gharm_nonneg (i : ℕ) : 0 ≤ gharm i := by
  unfold gharm; split_ifs
  · norm_num
  · have := pi_pos; positivity

lemma sum_gharm (N : ℕ) :
    ∑ i ∈ range (N + 1), gharm i = 1 + (1 / π) * ∑ i ∈ range N, (1 : ℝ) / (i + 1) := by
  have h0 : gharm 0 = 1 := by simp [gharm]
  rw [sum_range_succ', mul_sum, add_comm, h0]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  simp only [gharm, Nat.succ_ne_zero, ↓reduceIte]
  push_cast
  field_simp

lemma sum_inv_le (N : ℕ) : ∑ i ∈ range N, (1 : ℝ) / (i + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have e : (harmonic N : ℝ) = ∑ i ∈ range N, (1 : ℝ) / (i + 1) := by
    simp [harmonic]
  linarith

lemma left_sum (s : ℝ) (N : ℕ) (J : Finset ℤ) (hJ : ∀ j ∈ J, (j : ℝ) ≤ s ∧ s - j ≤ N) :
    ∑ j ∈ J, fdist (s - j) ≤ ∑ i ∈ range (N + 1), gharm i := by
  set φ : ℤ → ℕ := fun j => (⌊s⌋ - j).toNat with hφ
  have hle : ∀ j ∈ J, j ≤ ⌊s⌋ := fun j hj => Int.le_floor.mpr (hJ j hj).1
  have hinj : Set.InjOn φ J := by
    intro a ha b hb hab
    have h1 := hle a ha
    have h2 := hle b hb
    simp only [hφ] at hab
    omega
  calc ∑ j ∈ J, fdist (s - j) ≤ ∑ j ∈ J, gharm (φ j) := by
        apply sum_le_sum
        intro j hj
        apply fdist_le_gharm
        have h1 := hle j hj
        have h2 : ((φ j : ℕ) : ℤ) = ⌊s⌋ - j := by simp only [hφ]; omega
        have h3 : ((φ j : ℕ) : ℝ) = ((⌊s⌋ - j : ℤ) : ℝ) := by exact_mod_cast h2
        rw [h3]; push_cast; linarith [Int.floor_le s]
    _ = ∑ i ∈ J.image φ, gharm i := (sum_image hinj).symm
    _ ≤ ∑ i ∈ range (N + 1), gharm i := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
          rw [mem_range]
          have h1 := hle j hj
          have h4 : ((⌊s⌋ - j : ℤ) : ℝ) ≤ N := by
            push_cast; linarith [Int.floor_le s, (hJ j hj).2]
          have h5 : ⌊s⌋ - j ≤ (N : ℤ) := by exact_mod_cast h4
          simp only [hφ]; omega
        · intro i _ _; exact gharm_nonneg i

lemma right_sum (s : ℝ) (N : ℕ) (J : Finset ℤ) (hJ : ∀ j ∈ J, s < (j : ℝ) ∧ (j : ℝ) - s ≤ N) :
    ∑ j ∈ J, fdist (j - s) ≤ ∑ i ∈ range (N + 1), gharm i := by
  set φ : ℤ → ℕ := fun j => (j - ⌊s⌋ - 1).toNat with hφ
  have hle : ∀ j ∈ J, ⌊s⌋ < j := fun j hj => Int.floor_lt.mpr (hJ j hj).1
  have hinj : Set.InjOn φ J := by
    intro a ha b hb hab
    have h1 := hle a ha
    have h2 := hle b hb
    simp only [hφ] at hab
    omega
  calc ∑ j ∈ J, fdist (j - s) ≤ ∑ j ∈ J, gharm (φ j) := by
        apply sum_le_sum
        intro j hj
        apply fdist_le_gharm
        have h1 := hle j hj
        have h2 : ((φ j : ℕ) : ℤ) = j - ⌊s⌋ - 1 := by simp only [hφ]; omega
        have h3 : ((φ j : ℕ) : ℝ) = ((j - ⌊s⌋ - 1 : ℤ) : ℝ) := by exact_mod_cast h2
        rw [h3]; push_cast; linarith [Int.lt_floor_add_one s]
    _ = ∑ i ∈ J.image φ, gharm i := (sum_image hinj).symm
    _ ≤ ∑ i ∈ range (N + 1), gharm i := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
          rw [mem_range]
          have h1 := hle j hj
          have h4 : ((j - ⌊s⌋ - 1 : ℤ) : ℝ) ≤ N := by
            push_cast; linarith [Int.lt_floor_add_one s, (hJ j hj).2]
          have h5 : j - ⌊s⌋ - 1 ≤ (N : ℤ) := by exact_mod_cast h4
          simp only [hφ]; omega
        · intro i _ _; exact gharm_nonneg i

lemma window_sum (s : ℝ) (N : ℕ) (J : Finset ℤ) (hJ : ∀ j ∈ J, |s - j| ≤ N) :
    ∑ j ∈ J, fdist |s - j| ≤ 2 + (2 / π) * (1 + Real.log N) := by
  rw [← sum_filter_add_sum_filter_not J (fun j : ℤ => (j : ℝ) ≤ s)]
  have hl := left_sum s N (J.filter (fun j : ℤ => (j : ℝ) ≤ s)) (by
    intro j hj
    rw [mem_filter] at hj
    have := hJ j hj.1
    rw [abs_le] at this
    exact ⟨hj.2, by linarith⟩)
  have hr := right_sum s N (J.filter (fun j : ℤ => ¬ (j : ℝ) ≤ s)) (by
    intro j hj
    rw [mem_filter] at hj
    have := hJ j hj.1
    rw [abs_le] at this
    exact ⟨lt_of_not_ge hj.2, by linarith⟩)
  have e1 : ∑ j ∈ J.filter (fun j : ℤ => (j : ℝ) ≤ s), fdist |s - j| =
      ∑ j ∈ J.filter (fun j : ℤ => (j : ℝ) ≤ s), fdist (s - j) := by
    refine sum_congr rfl fun j hj => ?_
    rw [mem_filter] at hj
    rw [abs_of_nonneg (by linarith [hj.2])]
  have e2 : ∑ j ∈ J.filter (fun j : ℤ => ¬ (j : ℝ) ≤ s), fdist |s - j| =
      ∑ j ∈ J.filter (fun j : ℤ => ¬ (j : ℝ) ≤ s), fdist (j - s) := by
    refine sum_congr rfl fun j hj => ?_
    rw [mem_filter] at hj
    rw [abs_of_neg (by linarith [lt_of_not_ge hj.2]), neg_sub]
  rw [e1, e2]
  have hs := sum_gharm N
  have hh := sum_inv_le N
  have hpi := pi_pos
  have : (1 / π) * ∑ i ∈ range N, (1 : ℝ) / (i + 1) ≤ (1 / π) * (1 + Real.log N) :=
    mul_le_mul_of_nonneg_left hh (by positivity)
  have e3 : (2 / π) * (1 + Real.log N) = 2 * ((1 / π) * (1 + Real.log N)) := by ring
  rw [e3]
  linarith

lemma abs_sin_eq (M : ℝ) (h1 : |M| ≤ π) : |sin M| = sin |M| := by
  rcases le_or_gt 0 M with h | h
  · rw [abs_of_nonneg h] at h1 ⊢
    exact abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h h1)
  · rw [abs_of_neg h] at h1 ⊢
    rw [← abs_neg, ← sin_neg]
    exact abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi (by linarith) h1)

lemma cot_bound {M : ℝ} (h0 : M ≠ 0) (h1 : |M| ≤ π / 2) : |cos M| / |sin M| ≤ 1 / |M| := by
  have hu : 0 < |M| := abs_pos.mpr h0
  have hpi := pi_pos
  rw [abs_sin_eq M (by linarith), ← cos_abs M]
  have hsin : 0 < sin |M| := sin_pos_of_pos_of_lt_pi hu (by linarith)
  have hcos : 0 ≤ cos |M| := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [abs_of_nonneg hcos, div_le_div_iff₀ hsin hu]
  rcases lt_or_eq_of_le h1 with h2 | h2
  · have ht := le_tan hu.le h2
    rw [tan_eq_sin_div_cos] at ht
    have hcos' : 0 < cos |M| := cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
    rw [le_div_iff₀ hcos'] at ht
    linarith
  · rw [h2, cos_pi_div_two, sin_pi_div_two]; linarith

lemma term_bound {c M : ℝ} {n : ℕ} (hn : 1 ≤ n) (h0 : M ≠ 0) (h1 : |M| ≤ π / 2)
    (hc1 : |c| ≤ 1) (hc2 : |c| ≤ 2 * n * |M|) :
    |c| * (|cos M| / |sin M|) / (2 * n) ≤ fdist (2 * n * |M| / π) := by
  have hu : 0 < |M| := abs_pos.mpr h0
  have hpi := pi_pos
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq := cot_bound h0 h1
  have hq0 : 0 ≤ |cos M| / |sin M| := by positivity
  have hc0 : 0 ≤ |c| := abs_nonneg c
  unfold fdist
  apply le_min
  · rw [div_le_one (by positivity)]
    calc |c| * (|cos M| / |sin M|) ≤ (2 * n * |M|) * (1 / |M|) :=
          mul_le_mul hc2 hq hq0 (by positivity)
      _ = 2 * n := by field_simp
  · have e : 1 / (π * (2 * n * |M| / π)) = 1 * (1 / |M|) / (2 * n) := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul hc1 hq hq0 (by norm_num)

lemma sin_two_n_pi_sub (n : ℕ) (z : ℝ) : |sin (2 * n * π - z)| = |sin z| := by
  rw [sin_sub]
  have h1 : sin (2 * n * π) = 0 := by
    have := sin_nat_mul_pi (2 * n); push_cast at this; linarith
  have h2 : cos (2 * n * π) = 1 := by
    have := cos_nat_mul_two_pi n
    rw [show (2 : ℝ) * n * π = n * (2 * π) by ring]; exact this
  rw [h1, h2, zero_mul, one_mul, zero_sub, abs_neg]

noncomputable def j2 (n m : ℕ) (s : ℝ) : ℤ :=
  if s + m + 1 ≤ n then -((m : ℤ) + 1) else 2 * (n : ℤ) - 1 - m

lemma per_term {n m : ℕ} (hn : 1 ≤ n) (hm : m < n) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π)
    (hne : cos θ ≠ cos ((2 * m + 1) * π / (2 * n))) :
    |cos (n * θ)| * |sin ((2 * m + 1) * π / (2 * n))| /
        (n * |cos θ - cos ((2 * m + 1) * π / (2 * n))|) ≤
      fdist |(n * θ / π - 1 / 2) - (m : ℤ)| +
        fdist |(n * θ / π - 1 / 2) - j2 n m (n * θ / π - 1 / 2)| := by
  set θk := (2 * m + 1) * π / (2 * n) with hθk
  set s := n * θ / π - 1 / 2 with hs
  have hpi := pi_pos
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm
  have hθk0 : 0 < θk := by rw [hθk]; positivity
  have hθkπ : θk < π := by
    rw [hθk, div_lt_iff₀ (by positivity)]; nlinarith
  have hnθk : (n : ℝ) * θk = (2 * m + 1) * π / 2 := by rw [hθk]; field_simp
  have hcosk : cos (n * θk) = 0 := cos_eq_zero_iff.mpr ⟨m, by rw [hnθk]; push_cast; ring⟩
  have hsink : |sin (n * θk)| ≤ 1 := abs_sin_le_one _
  set M := (θ - θk) / 2 with hM
  set P := (θ + θk) / 2 with hP
  have hsub : cos θ - cos θk = -2 * sin P * sin M := cos_sub_cos θ θk
  have hsinθk : sin θk = sin P * cos M - cos P * sin M := by
    rw [← sin_sub]; congr 1; rw [hM, hP]; ring
  have hsP : sin P ≠ 0 := by
    intro h; apply hne; rw [← sub_eq_zero, hsub, h]; ring
  have hsM : sin M ≠ 0 := by
    intro h; apply hne; rw [← sub_eq_zero, hsub, h]; ring
  have hM0 : M ≠ 0 := by intro h; apply hsM; rw [h, sin_zero]
  have hMπ : |M| ≤ π / 2 := by rw [hM, abs_le]; constructor <;> linarith
  have hP0 : 0 < P := by rw [hP]; linarith
  have hPπ : P < π := by rw [hP]; linarith
  set c := cos (n * θ) with hc
  have hc1 : |c| ≤ 1 := abs_cos_le_one _
  -- split the term
  have hsplit : |c| * |sin θk| / (n * |cos θ - cos θk|) ≤
      |c| * (|cos M| / |sin M|) / (2 * n) + |c| * (|cos P| / |sin P|) / (2 * n) := by
    rw [hsub, hsinθk]
    have hP' : 0 < |sin P| := abs_pos.mpr hsP
    have hM' : 0 < |sin M| := abs_pos.mpr hsM
    have hab : |sin P * cos M - cos P * sin M| ≤ |sin P| * |cos M| + |cos P| * |sin M| := by
      rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    have e : |(-2 : ℝ) * sin P * sin M| = 2 * |sin P| * |sin M| := by
      rw [abs_mul, abs_mul]; norm_num
    rw [e]
    have e2 : |c| * (|cos M| / |sin M|) / (2 * n) + |c| * (|cos P| / |sin P|) / (2 * n) =
        |c| * (|sin P| * |cos M| + |cos P| * |sin M|) / (n * (2 * |sin P| * |sin M|)) := by
      field_simp
    rw [e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hab (abs_nonneg c)
  refine hsplit.trans (add_le_add ?_ ?_)
  · -- M term
    have hcM : |c| ≤ 2 * n * |M| := by
      have : (n : ℝ) * θ = n * θk + 2 * n * M := by rw [hM]; ring
      rw [hc, this, cos_add, hcosk, zero_mul, zero_sub, abs_neg, abs_mul]
      calc |sin (n * θk)| * |sin (2 * n * M)| ≤ 1 * |2 * n * M| :=
            mul_le_mul hsink (abs_sin_le_abs) (abs_nonneg _) (by norm_num)
        _ = 2 * n * |M| := by rw [one_mul, abs_mul, abs_mul]; norm_num
    have := term_bound hn hM0 hMπ hc1 hcM
    refine this.trans (le_of_eq (congrArg fdist ?_))
    rw [show (2 : ℝ) * n * |M| / π = |2 * n * M / π| by
        rw [abs_div ((2 : ℝ) * n * M) π, abs_mul ((2 : ℝ) * n) M, abs_of_pos hpi,
          abs_of_pos (show (0 : ℝ) < 2 * n by positivity)]]
    congr 1; push_cast; rw [hs, hM, hθk]; field_simp; ring
  · -- P term
    have hcP : |c| ≤ |sin (2 * n * P)| := by
      have : (n : ℝ) * θ = 2 * n * P - n * θk := by rw [hP]; ring
      rw [hc, this, cos_sub, hcosk, mul_zero, zero_add, abs_mul]
      calc |sin (2 * n * P)| * |sin (n * θk)| ≤ |sin (2 * n * P)| * 1 :=
            mul_le_mul_of_nonneg_left hsink (abs_nonneg _)
        _ = _ := mul_one _
    unfold j2
    split_ifs with hcase
    · -- P ≤ π/2
      have hPle : P ≤ π / 2 := by
        have e : s + m + 1 = 2 * n * P / π := by rw [hs, hP, hθk]; field_simp; ring
        rw [e, div_le_iff₀ hpi] at hcase
        nlinarith
      have hPabs : |P| = P := abs_of_pos hP0
      have hcP' : |c| ≤ 2 * n * |P| := by
        rw [hPabs]; refine hcP.trans ?_
        have := abs_sin_le_abs (x := 2 * n * P)
        rwa [abs_of_pos (show (0 : ℝ) < 2 * n * P by positivity)] at this
      have := term_bound hn hP0.ne' (by rw [hPabs]; exact hPle) hc1 hcP'
      refine this.trans (le_of_eq (congrArg fdist ?_))
      rw [hPabs]
      have e : s - ((-((m : ℤ) + 1) : ℤ) : ℝ) = 2 * n * P / π := by
        push_cast; rw [hs, hP, hθk]; field_simp; ring
      rw [e, abs_of_pos (by positivity)]
    · -- P > π/2
      rw [not_le] at hcase
      set Q := π - P with hQ
      have hQ0 : 0 < Q := by rw [hQ]; linarith
      have hQle : Q ≤ π / 2 := by
        have e : s + m + 1 = 2 * n * P / π := by rw [hs, hP, hθk]; field_simp; ring
        rw [e, lt_div_iff₀ hpi] at hcase
        rw [hQ]; nlinarith
      have hQabs : |Q| = Q := abs_of_pos hQ0
      have hPQ : P = π - Q := by rw [hQ]; ring
      have hcQ : |c| ≤ 2 * n * |Q| := by
        rw [hQabs]; refine hcP.trans ?_
        rw [hPQ, show (2 : ℝ) * n * (π - Q) = 2 * n * π - 2 * n * Q by ring, sin_two_n_pi_sub]
        have := abs_sin_le_abs (x := 2 * n * Q)
        rwa [abs_of_pos (show (0 : ℝ) < 2 * n * Q by positivity)] at this
      have := term_bound hn hQ0.ne' (by rw [hQabs]; exact hQle) hc1 hcQ
      have ecos : |cos P| = |cos Q| := by rw [hPQ, cos_pi_sub, abs_neg]
      have esin : |sin P| = |sin Q| := by rw [hPQ, sin_pi_sub]
      rw [ecos, esin]
      refine this.trans (le_of_eq (congrArg fdist ?_))
      rw [hQabs]
      have e : s - ((2 * (n : ℤ) - 1 - m : ℤ) : ℝ) = -(2 * n * Q / π) := by
        push_cast; rw [hs, hQ, hP, hθk]; field_simp; ring
      rw [e, abs_neg, abs_of_pos (by positivity)]

lemma node_angle {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hT : (Chebyshev.T ℝ (n : ℤ)).eval z = 0) :
    ∃ m : ℕ, m < n ∧ z = cos ((2 * m + 1) * π / (2 * n)) := by
  have hc : cos (arccos z) = z := cos_arccos hz.1 hz.2
  have h0 := arccos_nonneg z
  have hπ := arccos_le_pi z
  set θ := arccos z with hθ
  rw [← hc, Chebyshev.T_real_cos] at hT
  obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp hT
  push_cast at hk
  have hpi := pi_pos
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnθ : (0 : ℝ) ≤ n * θ := by positivity
  have hk0 : (0 : ℝ) ≤ 2 * k + 1 := by
    by_contra h
    rw [not_le] at h
    have := mul_neg_of_neg_of_pos h hpi
    linarith
  have hk1 : (2 * k + 1 : ℝ) ≤ 2 * n := by
    have : (n : ℝ) * θ ≤ n * π := mul_le_mul_of_nonneg_left hπ (by positivity)
    nlinarith
  have hkz : (-1 : ℤ) < k := by
    have : (-1 : ℝ) < k := by linarith
    exact_mod_cast this
  have hkn : k < (n : ℤ) := by
    have : (k : ℝ) < n := by linarith
    exact_mod_cast this
  refine ⟨k.toNat, by omega, ?_⟩
  have e : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [e, ← hc]
  congr 1
  rw [eq_div_iff (by positivity)]
  linarith

lemma T_eq_nodal {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (hT : ∀ j, (Chebyshev.T ℝ (n : ℤ)).eval (x j) = 0) :
    Chebyshev.T ℝ (n : ℤ) =
      Polynomial.C (Chebyshev.T ℝ (n : ℤ)).leadingCoeff * Lagrange.nodal univ x := by
  have hdeg : (Chebyshev.T ℝ (n : ℤ)).degree = n := by
    rw [Chebyshev.degree_T ℝ]; simp
  have hne : Chebyshev.T ℝ (n : ℤ) ≠ 0 := by
    intro h; rw [h, degree_zero] at hdeg; exact WithBot.bot_ne_coe hdeg
  have hlc : (Chebyshev.T ℝ (n : ℤ)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (univ.image x)
  · rw [card_image_of_injective _ hx, card_univ, Fintype.card_fin]
    calc _ < (Chebyshev.T ℝ (n : ℤ)).degree := by
          apply Polynomial.degree_sub_lt_left
          · rw [Polynomial.degree_C_mul hlc, Lagrange.degree_nodal, hdeg, card_univ,
              Fintype.card_fin]
          · exact hne
          · rw [leadingCoeff_mul, leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff, mul_one]
      _ = n := hdeg
  · intro z hz
    obtain ⟨j, -, rfl⟩ := mem_image.mp hz
    rw [hT j, eval_mul, eval_C, Lagrange.eval_nodal_at_node (mem_univ j), mul_zero]

lemma basis_formula {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (hT : ∀ j, (Chebyshev.T ℝ (n : ℤ)).eval (x j) = 0) (y : ℝ) (hy : ∀ j, y ≠ x j)
    (k : Fin n) :
    (Lagrange.basis univ x k).eval y =
      (Chebyshev.T ℝ (n : ℤ)).eval y /
        ((y - x k) * (derivative (Chebyshev.T ℝ (n : ℤ))).eval (x k)) := by
  have hfac := T_eq_nodal x hx hT
  have hne : Chebyshev.T ℝ (n : ℤ) ≠ 0 := by
    intro h; have := hT; rw [h] at hfac
    have hdeg : (Chebyshev.T ℝ (n : ℤ)).degree = n := by
      rw [Chebyshev.degree_T ℝ]; simp
    rw [h, degree_zero] at hdeg; exact WithBot.bot_ne_coe hdeg
  have ha : (Chebyshev.T ℝ (n : ℤ)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  set a := (Chebyshev.T ℝ (n : ℤ)).leadingCoeff with ha_def
  rw [hfac, derivative_mul, derivative_C, zero_mul, zero_add]
  simp only [eval_mul, eval_C]
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ k), Lagrange.eval_nodal,
    Lagrange.eval_nodal, ← mul_prod_erase univ (fun i => y - x i) (mem_univ k)]
  rw [Lagrange.basis, eval_prod]
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  rw [prod_mul_distrib, prod_inv_distrib]
  have hy' : y - x k ≠ 0 := sub_ne_zero.mpr (hy k)
  have hp : ∏ i ∈ univ.erase k, (x k - x i) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i hi => sub_ne_zero.mpr (fun h => (ne_of_mem_erase hi) (hx h).symm))
  field_simp

lemma deriv_T_cos (n : ℕ) (φ : ℝ) :
    (derivative (Chebyshev.T ℝ (n : ℤ))).eval (cos φ) * sin φ = n * sin (n * φ) := by
  have h1 : HasDerivAt (fun φ => (Chebyshev.T ℝ (n : ℤ)).eval (cos φ))
      ((derivative (Chebyshev.T ℝ (n : ℤ))).eval (cos φ) * (-sin φ)) φ :=
    ((Chebyshev.T ℝ (n : ℤ)).hasDerivAt (cos φ)).comp φ (hasDerivAt_cos φ)
  have h2 : HasDerivAt (fun φ => cos ((n : ℝ) * φ)) (-sin ((n : ℝ) * φ) * ((n : ℝ) * 1)) φ :=
    ((hasDerivAt_id' φ).const_mul (n : ℝ)).cos
  have e : (fun φ => (Chebyshev.T ℝ (n : ℤ)).eval (cos φ)) = fun φ => cos ((n : ℝ) * φ) := by
    funext φ; rw [Chebyshev.T_real_cos]; push_cast; rfl
  rw [e] at h1
  have := h1.unique h2
  linarith

theorem main_bound (n : ℕ) (x : Fin n → ℝ) (hn : 1 ≤ n) (hx : IsChebyshevNodes x) :
    lebesgueConstant x < 2 / π * Real.log n + 3 := by
  obtain ⟨⟨hmono, hIcc⟩, hT⟩ := hx
  have hinj := hmono.injective
  choose m hm using fun k => node_angle hn (hIcc k) (hT k)
  have hpi := pi_pos
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hminj : Function.Injective m := by
    intro k l h
    apply hinj
    rw [(hm k).2, (hm l).2, h]
  have hbound : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      lebesgueFunction x y ≤ 2 + (2 / π) * (1 + Real.log n) := by
    intro y hy
    by_cases hnode : ∃ j, y = x j
    · obtain ⟨j, rfl⟩ := hnode
      have h1 : lebesgueFunction x (x j) = 1 := by
        unfold lebesgueFunction
        rw [sum_eq_single j]
        · rw [Lagrange.eval_basis_self (hinj.injOn) (mem_univ j), abs_one]
        · intro k _ hk; rw [Lagrange.eval_basis_of_ne hk (mem_univ j), abs_zero]
        · intro h; exact absurd (mem_univ j) h
      rw [h1]
      have : 0 ≤ (2 / π) * (1 + Real.log n) := by positivity
      linarith
    · rw [not_exists] at hnode
      have hyc : cos (arccos y) = y := cos_arccos hy.1 hy.2
      have hθ0 := arccos_nonneg y
      have hθπ := arccos_le_pi y
      set θ := arccos y with hθ
      set s := n * θ / π - 1 / 2 with hs
      have hterm : ∀ k, |(Lagrange.basis univ x k).eval y| ≤
          fdist |s - ((m k : ℤ) : ℝ)| + fdist |s - j2 n (m k) s| := by
        intro k
        set θk := (2 * (m k : ℝ) + 1) * π / (2 * n) with hθk
        have hxk : x k = cos θk := (hm k).2
        have hmk : ((m k : ℝ)) + 1 ≤ n := by exact_mod_cast (hm k).1
        have hθk0 : 0 < θk := by rw [hθk]; positivity
        have hθkπ : θk < π := by
          rw [hθk, div_lt_iff₀ (by positivity)]; nlinarith
        have hsθk : 0 < sin θk := sin_pos_of_pos_of_lt_pi hθk0 hθkπ
        have hnθk : (n : ℝ) * θk = (2 * m k + 1) * π / 2 := by rw [hθk]; field_simp
        have hcosk : cos (n * θk) = 0 :=
          cos_eq_zero_iff.mpr ⟨m k, by rw [hnθk]; push_cast; ring⟩
        have hsin1 : |sin (n * θk)| = 1 := by
          have h := sin_sq_add_cos_sq (n * θk)
          rw [hcosk] at h
          rw [← pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero, sq_abs]
          linarith
        have hd := deriv_T_cos n θk
        rw [← hxk] at hd
        set D := (derivative (Chebyshev.T ℝ (n : ℤ))).eval (x k) with hD
        have hnD : (n : ℝ) = |D| * |sin θk| := by
          rw [← abs_mul, hd, abs_mul, hsin1, mul_one, abs_of_nonneg (by positivity)]
        have hD0 : |D| ≠ 0 := by
          intro h; rw [h, zero_mul] at hnD; linarith
        have hTy : (Chebyshev.T ℝ (n : ℤ)).eval y = cos (n * θ) := by
          rw [← hyc, Chebyshev.T_real_cos]; push_cast; rfl
        rw [basis_formula x hinj hT y hnode k, hTy]
        have hne : cos θ ≠ cos θk := by rw [hyc, ← hxk]; exact hnode k
        have hy0 : |y - x k| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (hnode k))
        have e : |cos (n * θ) / ((y - x k) * D)| =
            |cos (n * θ)| * |sin θk| / (n * |cos θ - cos θk|) := by
          rw [hnD, hyc, ← hxk, abs_div, abs_mul]
          have : |sin θk| ≠ 0 := abs_ne_zero.mpr hsθk.ne'
          field_simp
        rw [e]
        have := per_term hn (hm k).1 hθ0 hθπ hne
        push_cast at this ⊢
        exact this
      have hs0 : -1 / 2 ≤ s := by
        rw [hs]; have : 0 ≤ n * θ / π := by positivity
        linarith
      have hs1 : s ≤ n - 1 / 2 := by
        rw [hs]
        have : n * θ / π ≤ n := by
          rw [div_le_iff₀ hpi]; exact mul_le_mul_of_nonneg_left hθπ (by positivity)
        linarith
      set f1 : Fin n → ℤ := fun k => (m k : ℤ) with hf1
      set f2 : Fin n → ℤ := fun k => j2 n (m k) s with hf2
      have hmlt : ∀ k, m k < n := fun k => (hm k).1
      have hf1inj : Function.Injective f1 := by
        intro k l h; apply hminj; simp only [hf1] at h; exact_mod_cast h
      have hf2inj : Function.Injective f2 := by
        intro k l h
        apply hminj
        have hk := hmlt k
        have hl := hmlt l
        simp only [hf2, j2] at h
        split_ifs at h <;> omega
      have hdisj : Disjoint (univ.image f1) (univ.image f2) := by
        rw [disjoint_left]
        intro j hj1 hj2
        obtain ⟨k, -, rfl⟩ := mem_image.mp hj1
        obtain ⟨l, -, hl⟩ := mem_image.mp hj2
        have hk := hmlt k
        have hl' := hmlt l
        simp only [hf1, hf2, j2] at hl
        split_ifs at hl <;> omega
      have hwin : ∀ j ∈ univ.image f1 ∪ univ.image f2, |s - j| ≤ n := by
        intro j hj
        rcases mem_union.mp hj with hj | hj
        · obtain ⟨k, -, rfl⟩ := mem_image.mp hj
          have : ((m k : ℝ)) + 1 ≤ n := by exact_mod_cast hmlt k
          simp only [hf1]; push_cast
          rw [abs_le]; constructor <;> linarith
        · obtain ⟨k, -, rfl⟩ := mem_image.mp hj
          have : ((m k : ℝ)) + 1 ≤ n := by exact_mod_cast hmlt k
          simp only [hf2, j2]
          split_ifs with hc
          · push_cast; rw [abs_le]; constructor <;> linarith
          · push_cast; rw [not_le] at hc; rw [abs_le]; constructor <;> linarith
      calc lebesgueFunction x y = ∑ k, |(Lagrange.basis univ x k).eval y| := rfl
        _ ≤ ∑ k, (fdist |s - ((f1 k : ℤ) : ℝ)| + fdist |s - f2 k|) := sum_le_sum fun k _ => hterm k
        _ = ∑ j ∈ univ.image f1 ∪ univ.image f2, fdist |s - j| := by
            rw [sum_add_distrib, sum_union hdisj, sum_image (fun a _ b _ h => hf1inj h),
              sum_image (fun a _ b _ h => hf2inj h)]
        _ ≤ 2 + (2 / π) * (1 + Real.log n) := window_sum s n _ hwin
  have hle : lebesgueConstant x ≤ 2 + (2 / π) * (1 + Real.log n) := by
    unfold lebesgueConstant
    apply csSup_le ((Set.nonempty_Icc.mpr (by norm_num)).image _)
    rintro _ ⟨y, hy, rfl⟩
    exact hbound y hy
  have h2 : 2 / π < 1 := by rw [div_lt_one hpi]; linarith [pi_gt_three]
  have e : 2 + (2 / π) * (1 + Real.log n) = 2 / π * Real.log n + (2 + 2 / π) := by ring
  rw [e] at hle
  linarith

end OMA.E1129

theorem OMA.solution : type_of% @Erdos1129.erdos_1129.variants.chebyshev_upper_bound :=
  ⟨3, OMA.E1129.main_bound⟩
