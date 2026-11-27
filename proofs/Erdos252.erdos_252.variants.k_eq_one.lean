import FormalConjectures.ErdosProblems.«252»

-- Problem: Erdős Problem 252 — k eq one
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/252.lean (declaration Erdos252.erdos_252.variants.k_eq_one)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA252b

open Nat ArithmeticFunction

lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- A positive integer `n` has at most `n / 2 + 1` divisors. -/
lemma card_div_le_half (n : ℕ) : n.divisors.card ≤ n / 2 + 1 := by
  have hsub : n.divisors ⊆ insert n (Finset.Icc 1 (n / 2)) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨e, he⟩, hn⟩ := hd
    rw [Finset.mem_insert, Finset.mem_Icc]
    by_cases hdn : d = n
    · left; exact hdn
    · right
      have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at he; exact hn he)
      have he2 : 2 ≤ e := by
        rcases e with _ | _ | e
        · simp at he; exact absurd he hn
        · simp at he; exact absurd he.symm hdn
        · omega
      refine ⟨hd0, ?_⟩
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      calc d * 2 ≤ d * e := Nat.mul_le_mul_left d he2
        _ = n := he.symm
  calc n.divisors.card ≤ (insert n (Finset.Icc 1 (n / 2))).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (n / 2)).card + 1 := Finset.card_insert_le _ _
    _ = n / 2 + 1 := by simp

/-- `σ(n) ≤ n τ(n)`. -/
lemma sigma_le (n : ℕ) : ArithmeticFunction.sigma 1 n ≤ n.divisors.card * n := by
  rw [sigma_one_apply]
  have := Finset.sum_le_card_nsmul n.divisors (fun d => d) n (fun d hd => Nat.divisor_le hd)
  simpa using this

lemma sigma_le_sq (n : ℕ) : ArithmeticFunction.sigma 1 n ≤ n * n := by
  have := sigma_le n
  have h2 := card_divisors_le_self n
  calc ArithmeticFunction.sigma 1 n ≤ n.divisors.card * n := this
    _ ≤ n * n := Nat.mul_le_mul_right n h2

end OMA252b

set_option maxHeartbeats 1000000 in
open Nat ArithmeticFunction in
theorem OMA.solution : type_of% @Erdos252.erdos_252.variants.k_eq_one := by
  unfold Erdos252.erdos_252_sum
  set f : ℕ → ℝ := fun n => (ArithmeticFunction.sigma 1 n : ℝ) / (n ! : ℝ) with hf_def
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [f]; positivity
  have hfle : ∀ n, f n ≤ 4 ^ n / n ! := by
    intro n
    simp only [f]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e1 := OMA252b.sigma_le_sq n
    have e2 := OMA252b.succ_le_two_pow n
    have : ArithmeticFunction.sigma 1 n ≤ 4 ^ n := by
      calc ArithmeticFunction.sigma 1 n ≤ n * n := e1
        _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul (by omega) (by omega)
        _ = 4 ^ n := by rw [← mul_pow]; norm_num
    exact_mod_cast this
  have hsum : Summable f :=
    Summable.of_nonneg_of_le hf0 hfle (Real.summable_pow_div_factorial 4)
  rintro ⟨r, hr⟩
  set q := r.den with hq_def
  have hq : 0 < q := r.pos
  -- choose a prime `p = N + 1` that is large
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (q + 12)
  set N := p - 1 with hN
  have hNp : N + 1 = p := by omega
  clear_value N
  have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
  set R := ∑' i, f (i + (N + 1)) with hR_def
  -- integrality of `N! * S`
  have hNS : ∃ z : ℤ, (N ! : ℝ) * (r : ℝ) = z := by
    refine ⟨((N ! / q : ℕ) : ℤ) * r.num, ?_⟩
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [Rat.cast_def, Int.cast_mul, Int.cast_natCast,
      Nat.cast_div (Nat.dvd_factorial hq (by omega)) hq0]
    rw [← hq_def]
    field_simp
  -- integrality of `N! * (partial sum)`
  have hNP : ∃ z : ℕ, (N ! : ℝ) * ∑ i ∈ Finset.range (N + 1), f i = z := by
    refine ⟨∑ i ∈ Finset.range (N + 1), ArithmeticFunction.sigma 1 i * (N ! / i !), ?_⟩
    rw [Finset.mul_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity)]
    simp only [f]
    have : (i ! : ℝ) ≠ 0 := by positivity
    field_simp
  obtain ⟨z1, hz1⟩ := hNS
  obtain ⟨z2, hz2⟩ := hNP
  have hR : (N ! : ℝ) * R = ((z1 - (z2 : ℤ) : ℤ) : ℝ) := by
    push_cast
    rw [← hz1, ← hz2, hr, ← hsplit]
    ring
  -- split the tail into two terms and the rest
  have hsumR : Summable (fun i => f (i + (N + 1))) := (summable_nat_add_iff (N + 1)).mpr hsum
  have hs0 : Summable (fun i => f (i + 1 + (N + 1))) := (summable_nat_add_iff 1).mpr hsumR
  have hs00 : Summable (fun i => f (i + 1 + 1 + (N + 1))) := (summable_nat_add_iff 1).mpr hs0
  have hR0 : R = f (N + 1) + (f (N + 2) + ∑' i, f (i + 2 + (N + 1))) := by
    rw [hR_def, hsumR.tsum_eq_zero_add, hs0.tsum_eq_zero_add]
    have e : ∀ i, i + 1 + 1 + (N + 1) = i + 2 + (N + 1) := fun i => by omega
    simp only [e]
    congr 2
    · simp
    · congr 1; omega
  have hrest0 : 0 ≤ ∑' i, f (i + 2 + (N + 1)) := tsum_nonneg (fun i => hf0 _)
  have hNr : (11 : ℝ) ≤ N := by
    have : 11 ≤ N := by omega
    exact_mod_cast this
  have hNf : (0 : ℝ) < (N ! : ℝ) := by positivity
  -- first term: `σ(p)/p = 1 + 1/p`
  have h1 : (N ! : ℝ) * f (N + 1) = 1 + 1 / ((N : ℝ) + 1) := by
    simp only [f]
    rw [hNp, sigma_one_apply, hp.sum_divisors, ← hNp, Nat.factorial_succ]
    push_cast
    field_simp
  -- second term
  have h2 : (N ! : ℝ) * f (N + 2) ≤ 1 / 2 + 3 / (2 * ((N : ℝ) + 1)) := by
    simp only [f]
    have hs := OMA252b.sigma_le (N + 2)
    have hc := OMA252b.card_div_le_half (N + 2)
    have hc' : ((N + 2).divisors.card : ℝ) ≤ ((N : ℝ) + 2) / 2 + 1 := by
      have h' : (((N + 2) / 2 : ℕ) : ℝ) ≤ ((N + 2 : ℕ) : ℝ) / 2 := Nat.cast_div_le
      have : ((N + 2).divisors.card : ℝ) ≤ (((N + 2) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hc
      push_cast at h'
      linarith
    have hs' : (ArithmeticFunction.sigma 1 (N + 2) : ℝ) ≤ ((N : ℝ) + 2) * (((N : ℝ) + 2) / 2 + 1) := by
      have : (ArithmeticFunction.sigma 1 (N + 2) : ℝ) ≤ ((N + 2).divisors.card : ℝ) * ((N + 2 : ℕ) : ℝ) := by
        exact_mod_cast hs
      push_cast at this
      nlinarith
    have hfac : ((N + 2) ! : ℝ) = ((N : ℝ) + 2) * (((N : ℝ) + 1) * N !) := by
      rw [show N + 2 = (N + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hfac]
    have e : (N ! : ℝ) * ((ArithmeticFunction.sigma 1 (N + 2) : ℝ) / (((N : ℝ) + 2) * (((N : ℝ) + 1) * N !))) =
        (ArithmeticFunction.sigma 1 (N + 2) : ℝ) / (((N : ℝ) + 2) * ((N : ℝ) + 1)) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have e2 : (1 / 2 + 3 / (2 * ((N : ℝ) + 1))) * (((N : ℝ) + 2) * ((N : ℝ) + 1)) =
        ((N : ℝ) + 2) * (((N : ℝ) + 2) / 2 + 1) := by
      field_simp
      ring
    rw [e2]
    exact hs'
  -- remaining terms
  have hb : ∀ i, (N ! : ℝ) * f (i + 2 + (N + 1)) ≤ (2 / 11) * (1 / 11) ^ i := by
    intro i
    simp only [f]
    set m := i + 2 + (N + 1) with hm
    have hs : (ArithmeticFunction.sigma 1 m : ℝ) ≤ (m : ℝ) * m := by exact_mod_cast OMA252b.sigma_le_sq m
    have hfac : (m ! : ℝ) = (m : ℝ) * (((m : ℝ) - 1) * ((N + (i + 1)) ! : ℝ)) := by
      rw [show m = (N + (i + 1)) + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hineq : (N ! : ℝ) * ((N : ℝ) + 1) ^ (i + 1) ≤ ((N + (i + 1)) ! : ℝ) := by
      exact_mod_cast Nat.factorial_mul_pow_le_factorial
    have hmr : (m : ℝ) = (i : ℝ) + 2 + ((N : ℝ) + 1) := by rw [hm]; push_cast; ring
    have hm1 : (2 : ℝ) ≤ (m : ℝ) - 1 := by
      rw [hmr]
      have : (0 : ℝ) ≤ i := (by positivity)
      linarith
    have hmpos : (0 : ℝ) < m := by linarith
    have hF : (0 : ℝ) < ((N + (i + 1)) ! : ℝ) := by positivity
    have hratio : (m : ℝ) / ((m : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    calc (N ! : ℝ) * ((ArithmeticFunction.sigma 1 m : ℝ) / (m ! : ℝ))
        ≤ (N ! : ℝ) * (((m : ℝ) * m) / (m ! : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hNf.le
          exact div_le_div_of_nonneg_right hs (by positivity)
      _ = ((m : ℝ) / ((m : ℝ) - 1)) * ((N ! : ℝ) / ((N + (i + 1)) ! : ℝ)) := by
          rw [hfac]
          have : (m : ℝ) - 1 ≠ 0 := by linarith
          field_simp
      _ ≤ 2 * (1 / ((N : ℝ) + 1) ^ (i + 1)) := by
          apply mul_le_mul hratio _ (by positivity) (by norm_num)
          rw [div_le_div_iff₀ hF (by positivity)]
          linarith
      _ ≤ 2 * (1 / 11 ^ (i + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact pow_le_pow_left₀ (by norm_num) (by linarith) _
      _ = (2 / 11) * (1 / 11) ^ i := by
          rw [one_div_pow, pow_succ]
          field_simp
  have hgeo : Summable (fun i : ℕ => (2 / 11 : ℝ) * (1 / 11) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hs2 : Summable (fun i => f (i + 2 + (N + 1))) := by
    exact hs00.congr (fun i => congrArg f (by omega))
  have hs1 : Summable (fun i => (N ! : ℝ) * f (i + 2 + (N + 1))) := hs2.mul_left _
  have h3 : (N ! : ℝ) * ∑' i, f (i + 2 + (N + 1)) ≤ 1 / 5 := by
    rw [← tsum_mul_left]
    calc ∑' i, (N ! : ℝ) * f (i + 2 + (N + 1)) ≤ ∑' i : ℕ, (2 / 11 : ℝ) * (1 / 11) ^ i :=
          hs1.tsum_le_tsum hb hgeo
      _ = 1 / 5 := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
  have hf2 : 0 ≤ (N ! : ℝ) * f (N + 2) := mul_nonneg hNf.le (hf0 _)
  have hfr : 0 ≤ (N ! : ℝ) * ∑' i, f (i + 2 + (N + 1)) := mul_nonneg hNf.le hrest0
  have hN1 : 1 / ((N : ℝ) + 1) ≤ 1 / 12 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hN2 : 3 / (2 * ((N : ℝ) + 1)) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hlow : 1 < (N ! : ℝ) * R := by
    rw [hR0, mul_add, mul_add, h1]
    have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    linarith
  have hupp : (N ! : ℝ) * R < 2 := by
    rw [hR0, mul_add, mul_add, h1]
    linarith
  rw [hR] at hlow hupp
  have a1 : (1 : ℤ) < z1 - (z2 : ℤ) := by exact_mod_cast hlow
  have a2 : z1 - (z2 : ℤ) < 2 := by exact_mod_cast hupp
  omega
