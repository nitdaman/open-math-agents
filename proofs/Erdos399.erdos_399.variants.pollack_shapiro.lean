import FormalConjectures.ErdosProblems.«399»

-- SPDX-License-Identifier: Apache-2.0
-- Copyright 2026 alan-mroczek. Written with Claude (claude-fable-5-2).

-- Problem: Erdős Problem 399 — pollack shapiro
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/399.lean:68 (declaration Erdos399.erdos_399.variants.pollack_shapiro)
-- Credit: @alan-mroczek (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Idea: if n! + 1 = x^4 then n! = (x^2 - 1)(x^2 + 1), x odd, and (x^2 + 1)/2 has only prime
-- factors = 1 mod 4.  Let gt be the completely additive function with gt(p) = chi4(p) log p.
-- A Chebyshev-style convolution argument with the character chi4 gives gt(n!) <= 3n/8, while
-- the factorisation forces gt(n!) > (v_2(n!) - 2) log 2, impossible for n >= 16.

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace PS

noncomputable def chi (n : ℕ) : ℝ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)

lemma chi_mul (a b : ℕ) : chi (a * b) = chi a * chi b := by
  unfold chi
  rw [Nat.cast_mul, map_mul, Int.cast_mul]

lemma chi_eq (n : ℕ) : chi n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  unfold chi; rw [ZMod.χ₄_nat_eq_if_mod_four]; split_ifs <;> simp

lemma chi_one : chi 1 = 1 := by simp [chi_eq]

lemma chi_zero : chi 0 = 0 := by simp [chi_eq]

lemma chi_le_one (n : ℕ) : chi n ≤ 1 := by rw [chi_eq]; split_ifs <;> norm_num

lemma neg_one_le_chi (n : ℕ) : -1 ≤ chi n := by rw [chi_eq]; split_ifs <;> norm_num

lemma chi_pow (p k : ℕ) : chi (p ^ k) = chi p ^ k := by
  induction k with
  | zero => simp [chi_one]
  | succ k ih => rw [pow_succ, chi_mul, ih, pow_succ]

lemma chi_le_pow (p i : ℕ) : chi p ≤ chi (p ^ (i + 1)) := by
  rw [chi_pow]
  have h : chi p = 0 ∨ chi p = 1 ∨ chi p = -1 := by
    rw [chi_eq]; split_ifs <;> simp
  rcases h with h | h | h
  · rw [h]; simp
  · rw [h]; simp
  · rw [h]
    rcases neg_one_pow_eq_or ℝ (i + 1) with h' | h' <;> rw [h'] <;> norm_num

noncomputable def X : ArithmeticFunction ℝ := ⟨chi, chi_zero⟩

lemma X_apply (n : ℕ) : X n = chi n := rfl

lemma pmul_X_mul (a b : ArithmeticFunction ℝ) : X.pmul (a * b) = X.pmul a * X.pmul b := by
  ext n
  simp only [pmul_apply, mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  rw [← this, X_apply, chi_mul]
  simp only [X_apply]
  ring

noncomputable def f : ArithmeticFunction ℝ :=
  X.pmul (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)

lemma X_mul_f : X * f = (ζ : ArithmeticFunction ℝ) := by
  have h1 : X = X.pmul (ζ : ArithmeticFunction ℝ) := (pmul_zeta X).symm
  have h2 : X.pmul (1 : ArithmeticFunction ℝ) = 1 := by
    ext n
    by_cases h : n = 1 <;> simp [h, X_apply, chi_one]
  unfold f
  rw [← mul_assoc]
  nth_rewrite 1 [h1]
  rw [← pmul_X_mul, coe_zeta_mul_coe_moebius, h2, one_mul]

lemma f_mult : f.IsMultiplicative := by
  unfold f
  apply IsMultiplicative.mul
  · apply IsMultiplicative.pmul
    · exact ⟨chi_one, fun {m n} _ => chi_mul m n⟩
    · exact isMultiplicative_moebius.intCast
  · exact isMultiplicative_zeta.natCast

lemma f_prime_pow (p k : ℕ) (hp : p.Prime) : 0 ≤ f (p ^ k) := by
  unfold f
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  rcases k with _ | k
  · simp [X_apply, chi_one]
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : ∑ i ∈ range k, (X.pmul (μ : ArithmeticFunction ℝ)) (p ^ (i + 1 + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [pmul_apply, moebius_apply_prime_pow hp]
    rw [h0]
    simp [pmul_apply, X_apply, chi_one, moebius_apply_prime hp]
    linarith [chi_le_one p]

lemma f_nonneg (n : ℕ) : 0 ≤ f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [f_mult.multiplicative_factorization f hn]
  apply Finset.prod_nonneg
  intro p hp
  exact f_prime_pow p _ (Nat.prime_of_mem_primeFactors (by simpa using hp))

noncomputable def F (N : ℕ) : ℝ := ∑ j ∈ Ioc 0 N, f j

lemma F_nonneg (N : ℕ) : 0 ≤ F N := Finset.sum_nonneg fun j _ => f_nonneg j

lemma F_mono {a b : ℕ} (h : a ≤ b) : F a ≤ F b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right h) (fun j _ _ => f_nonneg j)

noncomputable def S (M : ℕ) : ℝ := ∑ e ∈ Ioc 0 M, X e

lemma S_eq (M : ℕ) : S M = if M % 4 = 1 ∨ M % 4 = 2 then 1 else 0 := by
  induction M with
  | zero => simp [S]
  | succ M ih =>
    unfold S at *
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih, X_apply, chi_eq]
    have := Nat.mod_lt M (by norm_num : 4 > 0)
    split_ifs <;> first | omega | norm_num

lemma S_nonneg (M : ℕ) : 0 ≤ S M := by
  rw [S_eq]; split_ifs <;> norm_num

lemma F_rec (N : ℕ) : F N ≤ N + F (N / 3) := by
  have h1 : (N : ℝ) = ∑ j ∈ Ioc 0 N, f j * S (N / j) := by
    have h := sum_Ioc_mul_eq_sum_sum f X N
    rw [mul_comm, X_mul_f] at h
    have h2 := sum_Ioc_zeta N
    have h3 : ∑ n ∈ Ioc 0 N, (ζ : ArithmeticFunction ℝ) n = (N : ℝ) := by
      simp only [natCoe_apply]
      exact_mod_cast h2
    rw [← h3, h]
    rfl
  have h3 : F N = F (N / 3) + ∑ j ∈ Ioc (N / 3) N, f j := by
    unfold F
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_self _ _)]
  have h4 : ∑ j ∈ Ioc (N / 3) N, f j ≤ ∑ j ∈ Ioc 0 N, f j * S (N / j) := by
    calc ∑ j ∈ Ioc (N / 3) N, f j = ∑ j ∈ Ioc (N / 3) N, f j * S (N / j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_Ioc] at hj
          have hj0 : 0 < j := by omega
          have ha : 0 < N / j := Nat.div_pos hj.2 hj0
          have hb : N / j < 3 := by
            rw [Nat.div_lt_iff_lt_mul hj0]
            have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).mp hj.1
            omega
          have hc : N / j = 1 ∨ N / j = 2 := by omega
          rw [S_eq]
          rcases hc with h | h <;> simp [h]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
          (fun j _ _ => mul_nonneg (f_nonneg j) (S_nonneg _))
  linarith

lemma F_le (N : ℕ) : F N ≤ 3 / 2 * N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [F]
    have h1 := ih (N / 3) (Nat.div_lt_self hN (by norm_num))
    have h3 : ((N / 3 : ℕ) : ℝ) ≤ (N : ℝ) / 3 := Nat.cast_div_le
    linarith [F_rec N]

noncomputable def hh : ArithmeticFunction ℝ := X.pmul Λ * (ζ : ArithmeticFunction ℝ)

lemma hh_eq : hh = X.pmul ArithmeticFunction.log * f := by
  unfold hh
  rw [← vonMangoldt_mul_zeta, pmul_X_mul, pmul_zeta, mul_assoc, X_mul_f]

lemma sum_hh (n : ℕ) :
    ∑ m ∈ Ioc 0 n, hh m = ∑ t ∈ Ioc 0 n, chi t * Real.log t * F (n / t) := by
  rw [hh_eq, sum_Ioc_mul_eq_sum_sum]
  rfl

lemma pair_bound (n t : ℕ) (ht : 3 ≤ t) :
    Real.log ((t : ℝ) + 2) * F (n / (t + 2)) - Real.log t * F (n / t)
      ≤ 3 / 4 * n * (1 / ((t : ℝ) - 1) - 1 / ((t : ℝ) + 3)) := by
  have ht' : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hF1 : F (n / (t + 2)) ≤ F (n / t) :=
    F_mono (Nat.div_le_div_left (by omega) (by omega))
  have hF2 : F (n / (t + 2)) ≤ 3 / 2 * ((n : ℝ) / ((t : ℝ) + 2)) := by
    refine (F_le _).trans ?_
    have : ((n / (t + 2) : ℕ) : ℝ) ≤ (n : ℝ) / ((t + 2 : ℕ) : ℝ) := Nat.cast_div_le
    push_cast at this
    linarith
  have hlog : Real.log ((t : ℝ) + 2) - Real.log t ≤ 2 / t := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((t : ℝ) + 2) / t by positivity)
    calc _ ≤ ((t : ℝ) + 2) / t - 1 := this
      _ = 2 / t := by field_simp; ring
  have hlog0 : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hlog1 : 0 ≤ Real.log ((t : ℝ) + 2) - Real.log t := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < t) (by linarith : (t : ℝ) ≤ t + 2)
    linarith
  have hΦ := F_nonneg (n / (t + 2))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have key : 2 / (t : ℝ) * (3 / 2 * ((n : ℝ) / ((t : ℝ) + 2)))
      ≤ 3 / 4 * n * (1 / ((t : ℝ) - 1) - 1 / ((t : ℝ) + 3)) := by
    have e1 : 2 / (t : ℝ) * (3 / 2 * ((n : ℝ) / ((t : ℝ) + 2))) = 3 * n / (t * (t + 2)) := by
      field_simp
    have e2 : 3 / 4 * n * (1 / ((t : ℝ) - 1) - 1 / ((t : ℝ) + 3))
        = 3 * n / ((t - 1) * (t + 3)) := by
      have : (t : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [e1, e2]
    apply div_le_div_of_nonneg_left (by positivity) (by nlinarith) (by nlinarith)
  calc _ ≤ (Real.log ((t : ℝ) + 2) - Real.log t) * F (n / (t + 2)) := by nlinarith
    _ ≤ 2 / t * (3 / 2 * ((n : ℝ) / ((t : ℝ) + 2))) := by gcongr
    _ ≤ _ := key

lemma sum_range_bound (n N : ℕ) :
    ∑ t ∈ range (4 * N + 2), chi t * Real.log t * F (n / t)
      ≤ 3 / 4 * n * (1 / 2 - 1 / (4 * (N : ℝ) + 2)) := by
  induction N with
  | zero => simp [Finset.sum_range_succ, chi_zero]
  | succ N ih =>
    rw [show 4 * (N + 1) + 2 = 4 * N + 2 + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have c0 : chi (4 * N + 2) = 0 := by rw [chi_eq, if_pos (by omega)]
    have c1 : chi (4 * N + 2 + 1) = -1 := by
      rw [chi_eq, if_neg (by omega), if_neg (by omega)]
    have c2 : chi (4 * N + 2 + 1 + 1) = 0 := by rw [chi_eq, if_pos (by omega)]
    have c3 : chi (4 * N + 2 + 1 + 1 + 1) = 1 := by
      rw [chi_eq, if_neg (by omega), if_pos (by omega)]
    have hp := pair_bound n (4 * N + 3) (by omega)
    rw [c0, c1, c2, c3]
    have e1 : (((4 * N + 3 : ℕ) : ℝ)) - 1 = 4 * (N : ℝ) + 2 := by push_cast; ring
    have e2 : (((4 * N + 3 : ℕ) : ℝ)) + 3 = 4 * ((N + 1 : ℕ) : ℝ) + 2 := by push_cast; ring
    have e3 : (((4 * N + 3 : ℕ) : ℝ)) + 2 = ((4 * N + 2 + 1 + 1 + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [e1, e2, e3] at hp
    have e4 : 4 * N + 3 + 2 = 4 * N + 2 + 1 + 1 + 1 := by ring
    have e5 : 4 * N + 3 = 4 * N + 2 + 1 := by ring
    rw [e4, e5] at hp
    have : 3 / 4 * (n : ℝ) * (1 / 2 - 1 / (4 * ((N + 1 : ℕ) : ℝ) + 2))
        = 3 / 4 * (n : ℝ) * (1 / 2 - 1 / (4 * (N : ℝ) + 2))
          + 3 / 4 * n * (1 / (4 * (N : ℝ) + 2) - 1 / (4 * ((N + 1 : ℕ) : ℝ) + 2)) := by ring
    rw [this]
    linarith

lemma sum_hh_le (n : ℕ) : ∑ m ∈ Ioc 0 n, hh m ≤ 3 / 8 * n := by
  rw [sum_hh]
  have hsub : Ioc 0 n ⊆ range (4 * n + 2) := by
    intro t ht
    rw [Finset.mem_Ioc] at ht
    rw [Finset.mem_range]
    omega
  rw [Finset.sum_subset hsub]
  · refine (sum_range_bound n n).trans ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : 0 ≤ 1 / (4 * (n : ℝ) + 2) := by positivity
    nlinarith
  · intro t _ ht
    rw [Finset.mem_Ioc] at ht
    rcases Nat.eq_zero_or_pos t with rfl | h0
    · simp [chi_zero]
    · have : n / t = 0 := Nat.div_eq_of_lt (by omega)
      rw [this]
      simp [F]

noncomputable def gt (m : ℕ) : ℝ :=
  m.factorization.sum fun p k => (k : ℝ) * (chi p * Real.log p)

lemma gt_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : gt (a * b) = gt a + gt b := by
  unfold gt
  rw [Nat.factorization_mul ha hb, Finsupp.sum_add_index']
  · intro p; simp
  · intro p k1 k2; push_cast; ring

lemma gt_one : gt 1 = 0 := by simp [gt]

lemma gt_prime_pow {p : ℕ} (k : ℕ) (hp : p.Prime) :
    gt (p ^ k) = k * (chi p * Real.log p) := by
  unfold gt
  rw [hp.factorization_pow, Finsupp.sum_single_index]
  simp

lemma gt_prime {p : ℕ} (hp : p.Prime) : gt p = chi p * Real.log p := by
  have := gt_prime_pow 1 hp
  simpa using this

lemma neg_log_le_gt (m : ℕ) (hm : m ≠ 0) : -Real.log m ≤ gt m := by
  induction m using Nat.recOnMul with
  | zero => exact absurd rfl hm
  | one => simp [gt_one]
  | prime p hp =>
    rw [gt_prime hp]
    nlinarith [neg_one_le_chi p, Real.log_natCast_nonneg p]
  | mul a b iha ihb =>
    have ha : a ≠ 0 := left_ne_zero_of_mul hm
    have hb : b ≠ 0 := right_ne_zero_of_mul hm
    rw [gt_mul ha hb, Nat.cast_mul, Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]
    linarith [iha ha, ihb hb]

lemma gt_eq_log (s : ℕ) (hs : s ≠ 0) (h : ∀ p : ℕ, p.Prime → p ∣ s → p % 4 = 1) :
    gt s = Real.log s := by
  induction s using Nat.recOnMul with
  | zero => exact absurd rfl hs
  | one => simp [gt_one]
  | prime p hp =>
    have h1 := h p hp dvd_rfl
    rw [gt_prime hp, chi_eq, if_neg (by omega), if_pos h1, one_mul]
  | mul a b iha ihb =>
    have ha : a ≠ 0 := left_ne_zero_of_mul hs
    have hb : b ≠ 0 := right_ne_zero_of_mul hs
    rw [gt_mul ha hb, Nat.cast_mul, Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast hb),
      iha ha (fun p hp hd => h p hp (hd.mul_right b)),
      ihb hb (fun p hp hd => h p hp (hd.mul_left a))]

lemma hh_apply (m : ℕ) : hh m = ∑ d ∈ m.divisors, chi d * Λ d := by
  unfold hh
  rw [coe_mul_zeta_apply]
  rfl

lemma hh_mul_coprime {a b : ℕ} (hab : a.Coprime b) : hh (a * b) = hh a + hh b := by
  have key : ∀ m : ℕ, hh m
      = ∑ d ∈ m.divisors with IsPrimePow d, chi d * Real.log (Nat.minFac d) := by
    intro m
    rw [hh_apply, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    rw [vonMangoldt_apply]
    split_ifs <;> simp
  rw [key, key, key, Nat.mul_divisors_filter_prime_pow hab, Finset.filter_union,
    Finset.sum_union (Nat.disjoint_divisors_filter_isPrimePow hab)]

lemma gt_le_hh (m : ℕ) (hm : m ≠ 0) : gt m ≤ hh m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [gt_prime_pow k hp, hh_apply, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
    simp only [pow_zero, vonMangoldt_apply_one, mul_zero, add_zero]
    calc (k : ℝ) * (chi p * Real.log p) = ∑ i ∈ range k, chi p * Real.log p := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
          rw [vonMangoldt_apply_pow (Nat.succ_ne_zero i), vonMangoldt_apply_prime hp]
          exact mul_le_mul_of_nonneg_right (chi_le_pow p i) (Real.log_natCast_nonneg p)
  | zero => exact absurd rfl hm
  | one => simp [gt_one, hh_apply]
  | coprime a b ha hb hab iha ihb =>
    rw [gt_mul (by omega) (by omega), hh_mul_coprime hab]
    linarith [iha (by omega), ihb (by omega)]

lemma gt_factorial (n : ℕ) : gt n ! = ∑ m ∈ Ioc 0 n, gt m := by
  induction n with
  | zero => simp [gt_one]
  | succ n ih =>
    rw [Nat.factorial_succ, gt_mul (by omega) (Nat.factorial_ne_zero n), ih,
      Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    ring

lemma gt_factorial_le (n : ℕ) : gt n ! ≤ 3 / 8 * n := by
  rw [gt_factorial]
  refine le_trans (Finset.sum_le_sum fun m hm => gt_le_hh m ?_) (sum_hh_le n)
  rw [Finset.mem_Ioc] at hm
  omega

lemma eight_dvd (m : ℕ) : 2 ^ 3 ∣ (m + 1) * (m + 2) * (m + 3) * (m + 4) := by
  obtain ⟨q, hq⟩ : ∃ q, m = 4 * q ∨ m = 4 * q + 1 ∨ m = 4 * q + 2 ∨ m = 4 * q + 3 :=
    ⟨m / 4, by omega⟩
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨(4 * q + 1) * (2 * q + 1) * (4 * q + 3) * (q + 1), by ring⟩
  · exact ⟨(2 * q + 1) * (4 * q + 3) * (q + 1) * (4 * q + 5), by ring⟩
  · exact ⟨(4 * q + 3) * (q + 1) * (4 * q + 5) * (2 * q + 3), by ring⟩
  · exact ⟨(q + 1) * (4 * q + 5) * (2 * q + 3) * (4 * q + 7), by ring⟩

lemma two_pow_dvd_factorial (n : ℕ) : 2 ^ (n / 2 + n / 4) ∣ n ! := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 4
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h1 := ih m (by omega)
      have e : (m + 4) / 2 + (m + 4) / 4 = (m / 2 + m / 4) + 3 := by omega
      have e2 : (m + 4)! = m ! * ((m + 1) * (m + 2) * (m + 3) * (m + 4)) := by
        simp only [Nat.factorial_succ]
        ring
      rw [e, pow_add, e2]
      exact Nat.mul_dvd_mul h1 (eight_dvd m)

lemma not_fourth (N y x : ℕ) (h1 : y ^ 4 < N) (h2 : N < (y + 1) ^ 4) : N ≠ x ^ 4 := by
  rintro rfl
  have a1 := lt_of_pow_lt_pow_left₀ 4 (Nat.zero_le _) h1
  have a2 := lt_of_pow_lt_pow_left₀ 4 (Nat.zero_le _) h2
  omega

lemma small (n x : ℕ) (hn : n < 16) : n ! + 1 ≠ x ^ 4 := by
  interval_cases n
  · exact not_fourth _ 1 x (by decide) (by decide)
  · exact not_fourth _ 1 x (by decide) (by decide)
  · exact not_fourth _ 1 x (by decide) (by decide)
  · exact not_fourth _ 1 x (by decide) (by decide)
  · exact not_fourth _ 2 x (by decide) (by decide)
  · exact not_fourth _ 3 x (by decide) (by decide)
  · exact not_fourth _ 5 x (by decide) (by decide)
  · exact not_fourth _ 8 x (by decide) (by decide)
  · exact not_fourth _ 14 x (by decide) (by decide)
  · exact not_fourth _ 24 x (by decide) (by decide)
  · exact not_fourth _ 43 x (by decide) (by decide)
  · exact not_fourth _ 79 x (by decide) (by decide)
  · exact not_fourth _ 147 x (by decide) (by decide)
  · exact not_fourth _ 280 x (by decide) (by decide)
  · exact not_fourth _ 543 x (by decide) (by decide)
  · exact not_fourth _ 1069 x (by decide) (by decide)

lemma prime_dvd_mod_four (k p : ℕ) (hp : p.Prime) (hd : p ∣ 2 * k ^ 2 + 2 * k + 1) :
    p % 4 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((2 * k ^ 2 + 2 * k + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have h1 : ((2 * k + 1 : ℕ) : ZMod p) ^ 2 = -1 := by
    have e : ((2 * k + 1 : ℕ) : ZMod p) ^ 2 + 1 = 2 * ((2 * k ^ 2 + 2 * k + 1 : ℕ) : ZMod p) := by
      push_cast; ring
    rw [h0, mul_zero] at e
    exact eq_neg_of_add_eq_zero_left e
  have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one h1
  have h2 : p ≠ 2 := by
    rintro rfl
    omega
  have := hp.eq_one_or_self_of_dvd 2
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h h2
    · exact h
  omega

theorem main (n x : ℕ) : n ! + 1 ≠ x ^ 4 := by
  by_cases hn : n < 16
  · exact small n x hn
  intro heq
  rw [not_lt] at hn
  have h2n : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) (by omega)
  have hxodd : x % 2 = 1 := by
    by_contra hx
    have hx0 : 2 ∣ x := by omega
    have : 2 ∣ x ^ 4 := dvd_pow hx0 (by norm_num)
    rw [← heq] at this
    omega
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  have hfac : n ! = (4 * (k * (k + 1))) * (2 * (2 * k ^ 2 + 2 * k + 1)) := by
    have : (2 * k + 1) ^ 4 = (4 * (k * (k + 1))) * (2 * (2 * k ^ 2 + 2 * k + 1)) + 1 := by ring
    omega
  have hs := prime_dvd_mod_four k
  have hsz : 8 * (k * (k + 1)) < 4 * (2 * k ^ 2 + 2 * k + 1) := by
    have : 4 * (2 * k ^ 2 + 2 * k + 1) = 8 * (k * (k + 1)) + 4 := by ring
    omega
  generalize 2 * k ^ 2 + 2 * k + 1 = s at hfac hs hsz
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hfac
    exact Nat.factorial_ne_zero n hfac
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hfac
    exact Nat.factorial_ne_zero n hfac
  have hcop : Nat.Coprime (2 ^ (n / 2 + n / 4)) s :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (fun h => by have := hs 2 Nat.prime_two h; omega))
  have he := two_pow_dvd_factorial n
  have hE : 3 * n ≤ 4 * (n / 2 + n / 4) + 5 := by omega
  generalize n / 2 + n / 4 = e at hcop he hE
  obtain ⟨r, hr⟩ : 2 ^ e ∣ 8 * (k * (k + 1)) :=
    hcop.dvd_of_dvd_mul_right (by rw [hfac] at he; convert he using 1; ring)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
    exact hk hr
  have hfac2 : n ! = 2 ^ e * (r * s) := by
    rw [hfac, ← mul_assoc (2 ^ e), ← hr]
    ring
  have hg : gt n ! = gt r + Real.log s := by
    have c2 : chi 2 = 0 := by rw [chi_eq]; simp
    rw [hfac2, gt_mul (by positivity) (mul_ne_zero hr0 hs0), gt_mul hr0 hs0,
      gt_prime_pow e Nat.prime_two, gt_eq_log s hs0 hs, c2]
    ring
  have h1 := neg_log_le_gt r hr0
  have h2 := gt_factorial_le n
  have hlt : ((2 : ℝ) ^ e * r) < 4 * s := by
    rw [hr] at hsz
    exact_mod_cast hsz
  have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  have hs0' : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
  have hrpos : (0 : ℝ) < r := by positivity
  have hlog := Real.log_lt_log (by positivity) hlt
  rw [Real.log_mul (by positivity) hr0', Real.log_pow,
    Real.log_mul (by norm_num) hs0'] at hlog
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2 := Real.log_two_gt_d9
  have hE' : 3 * (n : ℝ) ≤ 4 * e + 5 := by exact_mod_cast hE
  have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have a1 : ((3 * (n : ℝ) - 13) / 4) * 0.6931 ≤ ((e : ℝ) - 2) * Real.log 2 :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  linarith

end PS

theorem OMA.solution : type_of% @Erdos399.erdos_399.variants.pollack_shapiro := by
  intro n x
  exact PS.main n x
