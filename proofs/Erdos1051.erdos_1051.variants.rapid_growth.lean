import FormalConjectures.ErdosProblems.«1051»

-- Problem: Erdős Problem 1051 — rapid growth
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1051.lean:83 (declaration Erdos1051.erdos_1051.variants.rapid_growth)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA1051

open Finset

/-- Core: a sequence of large integers with `b (n+1) ≥ C b n ^ 2` gives an irrational series. -/
lemma core (b : ℕ → ℤ) (C : ℝ) (hC : 0 < C) (hK1 : ∀ n, (2 : ℝ) / C ^ 2 ≤ b n)
    (hK2 : ∀ n, (2 : ℝ) / C ≤ b n) (hK3 : ∀ n, (1 : ℝ) ≤ b n)
    (hrec : ∀ n, C * (b n : ℝ) ^ 2 ≤ b (n + 1)) :
    Summable (fun n => 1 / ((b n : ℝ) * b (n + 1))) ∧
      Irrational (∑' n, 1 / ((b n : ℝ) * b (n + 1))) := by
  set t : ℕ → ℝ := fun n => 1 / ((b n : ℝ) * b (n + 1)) with ht
  have bpos : ∀ n, (0 : ℝ) < b n := fun n => lt_of_lt_of_le one_pos (hK3 n)
  -- doubling
  have hdbl : ∀ n, 2 * (b n : ℝ) ≤ b (n + 1) := by
    intro n
    have h1 := hrec n
    have h2 := hK2 n
    have hb := bpos n
    have : 2 ≤ C * b n := by
      rw [div_le_iff₀ hC] at h2; linarith
    nlinarith
  have tpos : ∀ n, 0 < t n := fun n => by
    simp only [ht]; exact one_div_pos.mpr (mul_pos (bpos n) (bpos (n + 1)))
  have thalf : ∀ n, t (n + 1) ≤ t n / 2 := by
    intro n
    simp only [ht]
    have h1 := hdbl n
    have h2 := hdbl (n + 1)
    have b0 := bpos n
    have b1 := bpos (n + 1)
    have b2 := bpos (n + 2)
    rw [div_div, div_le_div_iff₀ (mul_pos b1 b2) (by positivity)]
    nlinarith
  have tgeo : ∀ n k, t (k + n) ≤ t n / 2 ^ k := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      have := thalf (k + n)
      rw [show k + 1 + n = (k + n) + 1 by ring]
      calc t (k + n + 1) ≤ t (k + n) / 2 := this
        _ ≤ t n / 2 ^ k / 2 := by linarith
        _ = t n / 2 ^ (k + 1) := by rw [pow_succ, div_div]
  have tsumm_shift : ∀ n, Summable (fun k => t (k + n)) := by
    intro n
    refine Summable.of_nonneg_of_le (fun k => (tpos _).le) (tgeo n) ?_
    have : Summable (fun k : ℕ => t n * (1 / 2) ^ k) :=
      (summable_geometric_two).mul_left (t n)
    convert this using 1
    funext k; rw [one_div_pow, mul_one_div]
  have tsumm : Summable t := by simpa using tsumm_shift 0
  have tail_le : ∀ n, ∑' k, t (k + n) ≤ 2 * t n := by
    intro n
    have h := (tsumm_shift n).tsum_le_tsum (tgeo n)
      ((summable_geometric_two).mul_left (t n) |>.congr fun k => by
        rw [one_div_pow, mul_one_div])
    calc ∑' k, t (k + n) ≤ ∑' k : ℕ, t n / 2 ^ k := h
      _ = 2 * t n := by
        rw [show (fun k : ℕ => t n / 2 ^ k) = fun k : ℕ => t n * (1 / 2) ^ k by
          funext k; rw [one_div_pow, mul_one_div]]
        rw [tsum_mul_left, tsum_geometric_two]; ring
  have tail_pos : ∀ n, 0 < ∑' k, t (k + n) := fun n =>
    (tsumm_shift n).tsum_pos (fun k => (tpos _).le) 0 (tpos _)
  -- the product sequence
  set Q : ℕ → ℝ := fun m => ∏ i ∈ range m, (b i : ℝ) with hQ
  have Qpos : ∀ m, 0 < Q m := fun m => prod_pos fun i _ => bpos i
  set y : ℕ → ℝ := fun N => Q (N + 1) / b (N + 2) with hy
  have ystep : ∀ N, y (N + 1) ≤ y N / 2 := by
    intro N
    simp only [hy, hQ]
    rw [prod_range_succ (fun i => (b i : ℝ)) (N + 1)]
    set q := ∏ i ∈ range (N + 1), (b i : ℝ)
    have hq : 0 < q := prod_pos fun i _ => bpos i
    have b1 := bpos (N + 1)
    have b2 := bpos (N + 2)
    have b3 := bpos (N + 3)
    have r1 := hrec (N + 1)
    have r2 := hrec (N + 2)
    have k1 := hK1 (N + 1)
    rw [div_le_iff₀ (by positivity)] at k1
    rw [div_div, div_le_div_iff₀ b3 (by positivity)]
    -- q * b1 * (b2 * 2) ≤ q * b3 ; use b3 ≥ C b2^2, b2 ≥ C b1^2, C^2 b1 ≥ 2
    have e2 : (b (N + 1) : ℝ) * (b (N + 2) * 2) ≤ b (N + 3) := by
      have : (b (N + 1) : ℝ) * 2 ≤ C * b (N + 2) := by
        have hh : C * (C * (b (N + 1) : ℝ) ^ 2) ≤ C * b (N + 2) :=
          mul_le_mul_of_nonneg_left r1 hC.le
        nlinarith
      have : (b (N + 1) : ℝ) * (b (N + 2) * 2) ≤ C * b (N + 2) ^ 2 := by nlinarith
      linarith [r2]
    have := mul_le_mul_of_nonneg_left e2 hq.le
    linarith
  have ygeo : ∀ N, y N ≤ y 0 / 2 ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      calc y (N + 1) ≤ y N / 2 := ystep N
        _ ≤ y 0 / 2 ^ N / 2 := by linarith
        _ = y 0 / 2 ^ (N + 1) := by rw [pow_succ, div_div]
  -- suppose rational
  refine ⟨tsumm, ?_⟩
  rintro ⟨r, hr⟩
  set q : ℕ := r.den
  have hqpos : (0 : ℝ) < q := by exact_mod_cast r.den_pos
  -- pick N with 2 * q * y N < 1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * q * y N < 1 := by
    have hy0 : 0 ≤ y 0 := (div_pos (Qpos 1) (bpos 2)).le
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * q * y 0 + 1) (by norm_num : (1 : ℝ) < 2)
    refine ⟨N, ?_⟩
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have := ygeo N
    calc 2 * q * y N ≤ 2 * q * (y 0 / 2 ^ N) := by gcongr
      _ = (2 * q * y 0) / 2 ^ N := by ring
      _ < 1 := by rw [div_lt_one h2N]; linarith
  -- the integer
  set P : ℝ := Q (N + 2) with hP
  have split := tsumm.sum_add_tsum_nat_add (N + 1)
  set R := ∑' k, t (k + (N + 1)) with hR
  -- integrality of q * P * R
  have hint : ∃ z : ℤ, (z : ℝ) = q * P * R := by
    have hpart : ∀ n ∈ range (N + 1), ∃ z : ℤ, (z : ℝ) = P * t n := by
      intro n hn
      rw [mem_range] at hn
      refine ⟨∏ i ∈ ((range (N + 2)).erase n).erase (n + 1), b i, ?_⟩
      have hn1 : n + 1 ∈ (range (N + 2)).erase n := by
        rw [mem_erase, mem_range]; omega
      have hn0 : n ∈ range (N + 2) := by rw [mem_range]; omega
      simp only [hP, hQ, ht]
      rw [← mul_prod_erase _ _ hn0, ← mul_prod_erase _ _ hn1]
      push_cast
      field_simp [(bpos n).ne', (bpos (n + 1)).ne']
    choose! f hf using hpart
    have hqx : (q : ℝ) * (r : ℝ) = r.num := by
      have h := congrArg (fun x : ℚ => (x : ℝ)) (Rat.mul_den_eq_num r)
      push_cast at h
      rw [mul_comm]; exact h
    refine ⟨r.num * (∏ i ∈ range (N + 2), b i) - q * ∑ n ∈ range (N + 1), f n, ?_⟩
    have hsum : (q : ℝ) * P * (∑ n ∈ range (N + 1), t n) =
        q * ∑ n ∈ range (N + 1), (f n : ℝ) := by
      have h2 : ∑ n ∈ range (N + 1), (f n : ℝ) = P * ∑ n ∈ range (N + 1), t n := by
        rw [mul_sum]; exact sum_congr rfl fun n hn => hf n hn
      rw [h2]; ring
    have hRe : R = (r : ℝ) - ∑ n ∈ range (N + 1), t n := by
      rw [hr]; linarith
    rw [hRe]
    push_cast
    rw [mul_sub, ← hsum]
    simp only [hP, hQ]
    rw [← hqx]; ring
  obtain ⟨z, hz⟩ := hint
  have hRpos : 0 < R := tail_pos (N + 1)
  have hz0 : (0 : ℝ) < z := by rw [hz]; exact mul_pos (mul_pos hqpos (Qpos _)) hRpos
  have hz1 : (z : ℝ) < 1 := by
    rw [hz]
    have hRle : R ≤ 2 * t (N + 1) := tail_le (N + 1)
    have hPt : P * t (N + 1) = y N := by
      simp only [hP, hQ, hy, ht]
      rw [prod_range_succ]
      have := bpos (N + 1)
      have := bpos (N + 2)
      field_simp
    calc (q : ℝ) * P * R ≤ q * P * (2 * t (N + 1)) := by
          gcongr
          exact (mul_pos hqpos (Qpos _)).le
      _ = 2 * q * (P * t (N + 1)) := by ring
      _ = 2 * q * y N := by rw [hPt]
      _ < 1 := hN
  have h1 : (0 : ℤ) < z := by exact_mod_cast hz0
  have h2 : z < (1 : ℤ) := by exact_mod_cast hz1
  omega

end OMA1051

theorem OMA.solution : type_of% @Erdos1051.erdos_1051.variants.rapid_growth := by
  intro a h_mono ⟨C, hC, hrec⟩
  set K : ℝ := max (max (2 / C ^ 2) (2 / C)) 1 with hK
  have hgrow : ∀ n, a 0 + n ≤ a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : a n < a (n + 1) := h_mono (by omega)
      push_cast; omega
  obtain ⟨M, hM⟩ : ∃ M : ℕ, K - a 0 ≤ M := exists_nat_ge _
  have haM : K ≤ a M := by
    have := hgrow M
    have : ((a 0 + M : ℤ) : ℝ) ≤ a M := by exact_mod_cast this
    push_cast at this; linarith
  set b : ℕ → ℤ := fun n => a (n + M) with hb
  have hbK : ∀ n, K ≤ b n := by
    intro n
    have : a M ≤ a (n + M) := h_mono.monotone (by omega)
    have : (a M : ℝ) ≤ a (n + M) := by exact_mod_cast this
    simp only [hb]; linarith
  have hb1 : ∀ n, (2 : ℝ) / C ^ 2 ≤ b n := fun n =>
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hbK n)
  have hb2 : ∀ n, (2 : ℝ) / C ≤ b n := fun n =>
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hbK n)
  have hb3 : ∀ n, (1 : ℝ) ≤ b n := fun n => le_trans (le_max_right _ _) (hbK n)
  have hbrec : ∀ n, C * (b n : ℝ) ^ 2 ≤ b (n + 1) := by
    intro n
    simp only [hb]
    rw [show n + 1 + M = n + M + 1 by ring]
    exact hrec (n + M)
  obtain ⟨hsumm, hirr⟩ := OMA1051.core b C hC hb1 hb2 hb3 hbrec
  set t : ℕ → ℝ := fun n => 1 / ((a n : ℝ) * a (n + 1)) with ht
  have hshift : (fun n => t (n + M)) = fun n => 1 / ((b n : ℝ) * b (n + 1)) := by
    funext n
    simp only [ht, hb]
    rw [show n + 1 + M = n + M + 1 by ring]
  have tsumm : Summable t := by
    rw [← summable_nat_add_iff M, hshift]; exact hsumm
  have hsplit := tsumm.sum_add_tsum_nat_add M
  unfold Erdos1051.ErdosSeries
  change Irrational (∑' n, t n)
  rw [← hsplit, hshift]
  have hrat : ∑ i ∈ Finset.range M, t i =
      ((∑ i ∈ Finset.range M, 1 / ((a i : ℚ) * a (i + 1)) : ℚ) : ℝ) := by
    push_cast; rfl
  rw [hrat]
  exact Irrational.ratCast_add _ hirr
