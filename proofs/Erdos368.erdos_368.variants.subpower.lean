import FormalConjectures.ErdosProblems.«368»

-- Problem: Erdős Problem 368 — subpower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/368.lean:72 (declaration Erdos368.erdos_368.variants.subpower)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial Filter Finset

namespace OMA

/-- A finite set of primes whose Euler product `∏ (1 - 1/p)` is small. -/
lemma small_euler_prod (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ, 2 ∈ s ∧ (∀ p ∈ s, p.Prime) ∧ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) < ε := by
  set f : ℕ → ℝ := Set.indicator {p | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n) with hf
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    simp only [hf, Set.indicator]
    split_ifs <;> positivity
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp not_summable_one_div_on_primes
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp ht) (-Real.log ε + 1) |>.exists
  set s := insert 2 ((range N).filter Nat.Prime) with hs
  have hsP : ∀ p ∈ s, p.Prime := by
    intro p hp
    rw [hs, mem_insert, mem_filter] at hp
    rcases hp with rfl | ⟨_, h⟩
    · exact Nat.prime_two
    · exact h
  refine ⟨s, mem_insert_self _ _, hsP, ?_⟩
  have hsum : ∑ i ∈ range N, f i ≤ ∑ p ∈ s, (p : ℝ)⁻¹ := by
    calc ∑ i ∈ range N, f i = ∑ p ∈ (range N).filter Nat.Prime, (p : ℝ)⁻¹ := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [hf, Set.indicator]
      _ ≤ ∑ p ∈ s, (p : ℝ)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (subset_insert _ _)
          intros; positivity
  have h1 : ∏ p ∈ s, (1 - (p : ℝ)⁻¹) ≤ ∏ p ∈ s, Real.exp (-(p : ℝ)⁻¹) := by
    apply Finset.prod_le_prod
    · intro p hp
      have := (hsP p hp).two_le
      have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ p))
      linarith
    · intro p _
      exact Real.one_sub_le_exp_neg _
  rw [← Real.exp_sum, Finset.sum_neg_distrib] at h1
  calc _ ≤ _ := h1
    _ < Real.exp (Real.log ε) := by
        apply Real.exp_lt_exp.mpr
        linarith
    _ = ε := Real.exp_log hε

/-- Prime divisors of `2^d - 1` are at most `3 ^ φ d`. -/
lemma prime_dvd_two_pow_sub_one_le {d q : ℕ} (hd : 0 < d) (hq : q.Prime) (hqd : q ∣ 2 ^ d - 1) :
    q ≤ 3 ^ Nat.totient d := by
  have hprod := congrArg (Polynomial.eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hd ℤ)
  rw [Polynomial.eval_prod] at hprod
  simp only [eval_sub, eval_pow, eval_X, eval_one] at hprod
  have hqZ : (q : ℤ) ∣ ∏ e ∈ d.divisors, eval 2 (cyclotomic e ℤ) := by
    rw [hprod]
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have : ((2 ^ d - 1 : ℕ) : ℤ) = 2 ^ d - 1 := by push_cast [h1]; ring
    rw [← this]
    exact_mod_cast hqd
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  obtain ⟨e, he, hqe⟩ := (Prime.dvd_finsetProd_iff hqp _).mp hqZ
  have hed : e ∣ d := Nat.dvd_of_mem_divisors he
  have hφ : Nat.totient e ≤ Nat.totient d :=
    Nat.le_of_dvd (Nat.totient_pos.mpr hd) (Nat.totient_dvd_of_dvd hed)
  have hφd : 1 ≤ Nat.totient d := Nat.totient_pos.mpr hd
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at hed
    omega
  rcases (by omega : e = 1 ∨ e = 2 ∨ 3 ≤ e) with rfl | rfl | he3
  · simp at hqe
    have := hq.one_lt
    have : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos hqe
    omega
  · simp at hqe
    have : (q : ℤ) ≤ 3 := Int.le_of_dvd (by norm_num) (by simpa using hqe)
    have h3 : 3 ≤ 3 ^ Nat.totient d := Nat.le_self_pow (by omega) 3
    omega
  · have hpos : 0 < eval 2 (cyclotomic e ℤ) := cyclotomic_pos (by omega) _
    have hle : (q : ℤ) ≤ eval 2 (cyclotomic e ℤ) := Int.le_of_dvd hpos hqe
    have hR : ((eval 2 (cyclotomic e ℤ) : ℤ) : ℝ) = eval 2 (cyclotomic e ℝ) := by
      rw [← map_cyclotomic_int e ℝ]
      have := eval_intCast_map (Int.castRingHom ℝ) (cyclotomic e ℤ) 2
      simpa using this.symm
    have hlt := cyclotomic_eval_lt_add_one_pow_totient (n := e) (q := (2 : ℝ)) he3 (by norm_num)
    have hqR : (q : ℝ) < 3 ^ Nat.totient e := by
      have : (q : ℝ) ≤ eval 2 (cyclotomic e ℝ) := by
        rw [← hR]; exact_mod_cast hle
      norm_num at hlt
      linarith
    have : q < 3 ^ Nat.totient e := by exact_mod_cast hqR
    have : 3 ^ Nat.totient e ≤ 3 ^ Nat.totient d := Nat.pow_le_pow_right (by norm_num) hφ
    omega

end OMA

theorem OMA.solution : type_of% @Erdos368.erdos_368.variants.subpower := by
  intro δ hδ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set ε := δ * Real.log 2 / (2 * Real.log 3) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨s, hs2, hsP, hsε⟩ := OMA.small_euler_prod ε hεpos
  set P := ∏ p ∈ s, p with hP
  have hPpf : P.primeFactors = s := Nat.primeFactors_prod hsP
  have hP2 : 2 ≤ P := by
    have : 2 ∣ P := Finset.dvd_prod_of_mem _ hs2
    have hP0 : P ≠ 0 := by
      rw [hP, Finset.prod_ne_zero_iff]
      intro p hp; exact (hsP p hp).ne_zero
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hP0) this
  rw [frequently_atTop]
  intro a
  set d := P ^ (a + 1) with hd
  have hd2 : 2 ^ (a + 1) ≤ d := Nat.pow_le_pow_left hP2 _
  have ha_lt : a + 1 < 2 ^ (a + 1) := Nat.lt_two_pow_self
  have hdpos : 0 < d := by omega
  have hdlt : d < 2 ^ d := Nat.lt_two_pow_self
  set n := 2 ^ d - 1 with hn
  refine ⟨n, by omega, ?_⟩
  -- bound on the largest prime factor
  have hF : Erdos368.F n ≤ 3 ^ Nat.totient d := by
    have hn1 : n + 1 = 2 ^ d := by omega
    have hn3 : 3 ≤ n := by
      have : 4 ≤ 2 ^ d := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hgt : 1 < n * (n + 1) := by nlinarith
    have hqp := Nat.prime_maxPrimeFac_of_one_lt _ hgt
    have hqd := Nat.maxPrimeFac_dvd (n := n * (n + 1))
    unfold Erdos368.F
    set q := (n * (n + 1)).maxPrimeFac
    have hq : q.Prime := hqp
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · exact OMA.prime_dvd_two_pow_sub_one_le hdpos hq h
    · rw [hn1] at h
      have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
      have h3 : 3 ≤ 3 ^ Nat.totient d := Nat.le_self_pow (Nat.totient_pos.mpr hdpos).ne' 3
      omega
  -- totient bound
  have hdpf : d.primeFactors = s := by
    rw [hd, Nat.primeFactors_pow _ (by omega), hPpf]
  have hφ : (Nat.totient d : ℝ) ≤ ε * d := by
    have h := Nat.totient_eq_mul_prod_factors d
    have h' : (Nat.totient d : ℝ) = d * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have := congrArg (fun x : ℚ => (x : ℝ)) h
      push_cast at this
      exact this
    rw [h', hdpf, mul_comm]
    exact mul_le_mul_of_nonneg_right hsε.le (by positivity)
  have hnR : (2 : ℝ) ^ (d - 1) ≤ n := by
    have : 2 ^ (d - 1) ≤ n := by
      have : 2 ^ d = 2 * 2 ^ (d - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    exact_mod_cast this
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have hlogn : ((d : ℝ) - 1) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hnR
    rw [Real.log_pow] at this
    have hc : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hc] at this
    exact this
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
  calc (Erdos368.F n : ℝ) ≤ (3 : ℝ) ^ Nat.totient d := by exact_mod_cast hF
    _ = Real.exp (Real.log 3 * Nat.totient d) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    _ ≤ Real.exp (Real.log n * δ) := by
        apply Real.exp_le_exp.mpr
        have h1 : Real.log 3 * Nat.totient d ≤ Real.log 3 * (ε * d) :=
          mul_le_mul_of_nonneg_left hφ hl3.le
        have h2 : Real.log 3 * (ε * d) = δ * Real.log 2 * d / 2 := by
          rw [hε]; field_simp
        have h3 : δ * Real.log 2 * d / 2 ≤ δ * (((d : ℝ) - 1) * Real.log 2) := by
          nlinarith [mul_nonneg (mul_nonneg hδ.le hl2.le) (show (0:ℝ) ≤ (d:ℝ)/2 - 1 by linarith)]
        have h4 : δ * (((d : ℝ) - 1) * Real.log 2) ≤ δ * Real.log n :=
          mul_le_mul_of_nonneg_left hlogn hδ.le
        linarith
    _ = (n : ℝ) ^ δ := by rw [Real.rpow_def_of_pos hnpos]
