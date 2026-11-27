import FormalConjectures.ErdosProblems.«252»

-- Problem: Erdős Problem 252 — k eq zero
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/252.lean:57 (declaration Erdos252.erdos_252.variants.k_eq_zero)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA252

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

end OMA252

open Nat ArithmeticFunction in
theorem OMA.solution : type_of% @Erdos252.erdos_252.variants.k_eq_zero := by
  unfold Erdos252.erdos_252_sum
  set f : ℕ → ℝ := fun n => (ArithmeticFunction.sigma 0 n : ℝ) / (n ! : ℝ) with hf_def
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [f]; positivity
  have hfle : ∀ n, f n ≤ 2 ^ n / n ! := by
    intro n
    simp only [f]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [sigma_zero_apply]
    have e1 := card_divisors_le_self n
    have e2 := OMA252.succ_le_two_pow n
    have : n.divisors.card ≤ 2 ^ n := by omega
    exact_mod_cast this
  have hsum : Summable f :=
    Summable.of_nonneg_of_le hf0 hfle (Real.summable_pow_div_factorial 2)
  rintro ⟨r, hr⟩
  set q := r.den with hq_def
  have hq : 0 < q := r.pos
  set N := q + 5 with hN
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
    refine ⟨∑ i ∈ Finset.range (N + 1), ArithmeticFunction.sigma 0 i * (N ! / i !), ?_⟩
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
  -- bounds on the tail
  have hsumR : Summable (fun i => f (i + (N + 1))) := (summable_nat_add_iff (N + 1)).mpr hsum
  have hR0 : R = f (N + 1) + ∑' i, f (i + 1 + (N + 1)) := by
    rw [hR_def, hsumR.tsum_eq_zero_add]
    simp
  have hpos : 0 < f (N + 1) := by
    simp only [f]
    rw [sigma_zero_apply]
    apply _root_.div_pos
    · exact_mod_cast Finset.card_pos.mpr (Nat.nonempty_divisors.mpr (by omega))
    · positivity
  have hrest0 : 0 ≤ ∑' i, f (i + 1 + (N + 1)) := tsum_nonneg (fun i => hf0 _)
  have hRpos : 0 < (N ! : ℝ) * R := by
    apply mul_pos (by positivity)
    rw [hR0]
    linarith
  have hNr : (6 : ℝ) ≤ N := by
    have : 6 ≤ N := by omega
    exact_mod_cast this
  have h1 : (N ! : ℝ) * f (N + 1) ≤ 2 / 3 := by
    simp only [f]
    rw [sigma_zero_apply, Nat.factorial_succ]
    push_cast
    have hc := OMA252.card_div_le_half (N + 1)
    have hc' : ((N + 1).divisors.card : ℝ) ≤ ((N : ℝ) + 1) / 2 + 1 := by
      have h' : (((N + 1) / 2 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / 2 := Nat.cast_div_le
      have : ((N + 1).divisors.card : ℝ) ≤ (((N + 1) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hc
      push_cast at h'
      linarith
    have hfac : (0 : ℝ) < N ! := by positivity
    have e : (N ! : ℝ) * (((N + 1).divisors.card : ℝ) / (((N : ℝ) + 1) * N !)) =
        ((N + 1).divisors.card : ℝ) / ((N : ℝ) + 1) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have hb : ∀ i, (N ! : ℝ) * f (i + 1 + (N + 1)) ≤ (1 / 6) * (1 / 6) ^ i := by
    intro i
    simp only [f]
    rw [sigma_zero_apply]
    set m := i + 1 + (N + 1) with hm
    have hc : ((m.divisors.card : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast card_divisors_le_self m
    have hm' : m = (N + (i + 1)) + 1 := by omega
    have hfac : (m ! : ℝ) = (m : ℝ) * ((N + (i + 1)) ! : ℝ) := by
      rw [hm', Nat.factorial_succ]
      push_cast
      ring
    have hineq : (N ! : ℝ) * ((N : ℝ) + 1) ^ (i + 1) ≤ ((N + (i + 1)) ! : ℝ) := by
      exact_mod_cast Nat.factorial_mul_pow_le_factorial
    have hmpos : (0 : ℝ) < m := by
      have : 0 < m := by omega
      exact_mod_cast this
    have hF : (0 : ℝ) < ((N + (i + 1)) ! : ℝ) := by positivity
    have hNf : (0 : ℝ) < (N ! : ℝ) := by positivity
    calc (N ! : ℝ) * ((m.divisors.card : ℝ) / (m ! : ℝ))
        ≤ (N ! : ℝ) * ((m : ℝ) / (m ! : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hNf.le
          exact div_le_div_of_nonneg_right hc (by positivity)
      _ = (N ! : ℝ) / ((N + (i + 1)) ! : ℝ) := by
          rw [hfac]; field_simp
      _ ≤ 1 / ((N : ℝ) + 1) ^ (i + 1) := by
          rw [div_le_div_iff₀ hF (by positivity)]
          linarith
      _ ≤ 1 / 6 ^ (i + 1) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact pow_le_pow_left₀ (by norm_num) (by linarith) _
      _ = (1 / 6) * (1 / 6) ^ i := by
          rw [one_div_pow, pow_succ]
          field_simp
  have hgeo : Summable (fun i : ℕ => (1 / 6 : ℝ) * (1 / 6) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hs0 : Summable (fun i => f (i + 1 + (N + 1))) := (summable_nat_add_iff 1).mpr hsumR
  have hs1 : Summable (fun i => (N ! : ℝ) * f (i + 1 + (N + 1))) := hs0.mul_left _
  have h2 : (N ! : ℝ) * ∑' i, f (i + 1 + (N + 1)) ≤ 1 / 5 := by
    rw [← tsum_mul_left]
    calc ∑' i, (N ! : ℝ) * f (i + 1 + (N + 1)) ≤ ∑' i : ℕ, (1 / 6 : ℝ) * (1 / 6) ^ i :=
          hs1.tsum_le_tsum hb hgeo
      _ = 1 / 5 := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
  have hRlt : (N ! : ℝ) * R < 1 := by
    rw [hR0, mul_add]
    linarith
  rw [hR] at hRpos hRlt
  have a1 : (0 : ℤ) < z1 - (z2 : ℤ) := by exact_mod_cast hRpos
  have a2 : z1 - (z2 : ℤ) < 1 := by exact_mod_cast hRlt
  omega
