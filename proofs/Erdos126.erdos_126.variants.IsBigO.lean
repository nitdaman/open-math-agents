import FormalConjectures.ErdosProblems.«126»

-- Problem: Erdős Problem 126 — IsBigO
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/126.lean (declaration Erdos126.erdos_126.variants.IsBigO)
-- Credit: @Rahul-007afk (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- A two-colouring of the positive integers attached to a prime `p`: it records on which side of
`p / 2` the `p`-free part of `a` lies modulo `p` (for `p = 2`, its class modulo `4`). -/
def OMA.colour (a p : ℕ) : Bool :=
  if p = 2 then decide ((a / 2 ^ a.factorization 2) % 4 = 1)
  else decide (2 * ((a / p ^ a.factorization p) % p) < p)

/-- Two numbers of the same colour have a sum whose `p`-adic valuation is essentially the smaller
of the two valuations. -/
lemma OMA.key {p : ℕ} (hp : p.Prime) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : OMA.colour a p = OMA.colour b p) :
    (a + b).factorization p ≤
      min (a.factorization p) (b.factorization p) + (if p = 2 then 1 else 0) := by
  wlog hij : a.factorization p ≤ b.factorization p generalizing a b
  · have h := this hb ha hc.symm (by omega)
    rw [add_comm, min_comm]
    exact h
  have hab : a + b ≠ 0 := by omega
  obtain ⟨a', ha'⟩ : ∃ a', a' = a / p ^ a.factorization p := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = b / p ^ b.factorization p := ⟨_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, i = a.factorization p := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = b.factorization p := ⟨_, rfl⟩
  have hae : p ^ i * a' = a := by rw [hi, ha']; exact Nat.ordProj_mul_ordCompl_eq_self a p
  have hbe : p ^ j * b' = b := by rw [hj, hb']; exact Nat.ordProj_mul_ordCompl_eq_self b p
  have hpa : ¬ p ∣ a' := by rw [ha']; exact Nat.not_dvd_ordCompl hp ha
  have hpb : ¬ p ∣ b' := by rw [hb']; exact Nat.not_dvd_ordCompl hp hb
  have hp2 := hp.two_le
  rw [← hi, ← hj] at hij ⊢
  rw [min_eq_left hij]
  by_contra hcon
  have hle : i + (if p = 2 then 1 else 0) + 1 ≤ (a + b).factorization p := by omega
  have hdvd : p ^ (i + (if p = 2 then 1 else 0) + 1) ∣ a + b :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hab).2 hle
  rcases Nat.lt_or_eq_of_le hij with hlt | heq
  · -- different valuations
    obtain ⟨d, hd⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
    have hsum : a + b = p ^ i * (a' + p ^ (d + 1) * b') := by
      rw [← hae, ← hbe, hd, pow_add]
      ring
    rw [hsum, show i + (if p = 2 then 1 else 0) + 1 = i + ((if p = 2 then 1 else 0) + 1) by ring,
      pow_add] at hdvd
    have h1 : p ^ ((if p = 2 then 1 else 0) + 1) ∣ a' + p ^ (d + 1) * b' :=
      (Nat.mul_dvd_mul_iff_left (by positivity)).1 hdvd
    have h2 : p ∣ a' + p ^ (d + 1) * b' := dvd_trans (dvd_pow_self p (by omega)) h1
    have h3 : p ∣ p ^ (d + 1) * b' := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
    exact hpa ((Nat.dvd_add_left h3).1 h2)
  · -- equal valuations
    have hsum : a + b = p ^ i * (a' + b') := by
      rw [← hae, ← hbe, ← heq]
      ring
    rw [hsum, show i + (if p = 2 then 1 else 0) + 1 = i + ((if p = 2 then 1 else 0) + 1) by ring,
      pow_add] at hdvd
    have h1 : p ^ ((if p = 2 then 1 else 0) + 1) ∣ a' + b' :=
      (Nat.mul_dvd_mul_iff_left (by positivity)).1 hdvd
    unfold OMA.colour at hc
    by_cases hp2' : p = 2
    · subst hp2'
      simp only [if_true] at hc h1
      rw [← ha', ← hb'] at hc
      have hc' : (a' % 4 = 1) ↔ (b' % 4 = 1) := by simpa using hc
      have h4 : (4 : ℕ) ∣ a' + b' := by simpa using h1
      have hoa : a' % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one a' with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) hpa
        · exact h
      have hob : b' % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one b' with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) hpb
        · exact h
      omega
    · simp only [if_neg hp2'] at hc h1
      rw [← ha', ← hb'] at hc
      have hc' : (2 * (a' % p) < p) ↔ (2 * (b' % p) < p) := by simpa using hc
      have hdp : p ∣ a' + b' := by simpa using h1
      have hra : a' % p ≠ 0 := fun h => hpa (Nat.dvd_of_mod_eq_zero h)
      have hrb : b' % p ≠ 0 := fun h => hpb (Nat.dvd_of_mod_eq_zero h)
      have hra' : a' % p < p := Nat.mod_lt _ (by omega)
      have hrb' : b' % p < p := Nat.mod_lt _ (by omega)
      have hmod : (a' % p + b' % p) % p = 0 := by
        rw [← Nat.add_mod]
        exact Nat.mod_eq_zero_of_dvd hdp
      have hsum' : a' % p + b' % p = p := by
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
        have hq1 : q = 1 := by
          have h1' : 0 < p * q := by omega
          have h2' : p * q < p * 2 := by omega
          have h3' : q < 2 := Nat.lt_of_mul_lt_mul_left h2'
          have h4' : q ≠ 0 := by
            rintro rfl
            simp at h1'
          omega
        rw [hq, hq1, mul_one]
      have hodd : p % 2 = 1 := by
        rcases Nat.Prime.eq_two_or_odd hp with h | h
        · exact absurd h hp2'
        · exact h
      omega

/-- Two distinct positive integers cannot have the same colour at every prime dividing their
sum: otherwise the sum would divide twice their greatest common divisor. -/
lemma OMA.inj {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hne : a ≠ b)
    (hc : ∀ p ∈ (a + b).primeFactors, OMA.colour a p = OMA.colour b p) : False := by
  have hab : a + b ≠ 0 := by omega
  have hg : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  have h2g : 2 * Nat.gcd a b ≠ 0 := by omega
  have hdvd : a + b ∣ 2 * Nat.gcd a b := by
    rw [← Nat.factorization_le_iff_dvd hab h2g]
    intro q
    by_cases hq : q ∈ (a + b).primeFactors
    · have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hk := OMA.key hqp ha hb (hc q hq)
      rw [Nat.factorization_mul (by norm_num) hg, Nat.factorization_gcd ha hb]
      simp only [Finsupp.add_apply, Finsupp.inf_apply]
      by_cases hq2 : q = 2
      · subst hq2
        rw [Nat.Prime.factorization_self Nat.prime_two]
        simp only [if_true] at hk
        omega
      · have h0 : (2 : ℕ).factorization q = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (fun h =>
            hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 h))
        rw [h0]
        simp only [if_neg hq2] at hk
        omega
    · have h0 : (a + b).factorization q = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hq
      rw [h0]
      exact Nat.zero_le _
  have hle := Nat.le_of_dvd (by omega) hdvd
  have h1 := Nat.gcd_le_left b (Nat.pos_of_ne_zero ha)
  have h2 := Nat.gcd_le_right a (Nat.pos_of_ne_zero hb)
  omega

/-- A set of positive integers whose pairwise sums involve only `k` primes has at most `2 ^ k`
elements. -/
lemma OMA.card_le (A : Finset ℕ) :
    (A.erase 0).card ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card := by
  classical
  obtain ⟨P, hP⟩ : ∃ P, P = (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors := ⟨_, rfl⟩
  rw [← hP, ← Finset.card_powerset]
  have hprod : (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    rintro ⟨x, y⟩ hxy
    rw [Finset.mem_offDiag] at hxy
    have := hxy.2.2
    show x + y ≠ 0
    omega
  apply Finset.card_le_card_of_injOn (fun a => P.filter (fun p => OMA.colour a p = true))
  · intro a _
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    exact Finset.filter_subset _ _
  · intro a ha b hb hab
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at ha hb
    by_contra hne
    refine OMA.inj ha.2 hb.2 hne (fun p hp => ?_)
    have hmem : (a, b) ∈ A.offDiag := Finset.mem_offDiag.2 ⟨ha.1, hb.1, hne⟩
    have hd : a + b ∣ ∏ ⟨a, b⟩ ∈ A.offDiag, (a + b) :=
      Finset.dvd_prod_of_mem (fun x : ℕ × ℕ => match x with | (a, b) => a + b) hmem
    have hpP : p ∈ P := by
      rw [hP]
      exact Nat.primeFactors_mono hd hprod hp
    have h1 : p ∈ P.filter (fun p => OMA.colour a p = true) ↔
        p ∈ P.filter (fun p => OMA.colour b p = true) := by
      have hab' : P.filter (fun p => OMA.colour a p = true) =
          P.filter (fun p => OMA.colour b p = true) := hab
      rw [hab']
    simp only [Finset.mem_filter, hpP, true_and] at h1
    exact Bool.eq_iff_iff.2 h1

/-- The prime factors of the pairwise sums of `{1, …, n}` are at most `2 * n`. -/
lemma OMA.card_primeFactors_Icc (n : ℕ) :
    (∏ ⟨a, b⟩ ∈ (Finset.Icc 1 n).offDiag, (a + b)).primeFactors.card ≤
      Nat.primeCounting (2 * n) := by
  have hcard : ((Finset.range (2 * n + 1)).filter Nat.Prime).card = Nat.primeCounting (2 * n) := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [← hcard]
  apply Finset.card_le_card
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ ∏ ⟨a, b⟩ ∈ (Finset.Icc 1 n).offDiag, (a + b) := Nat.dvd_of_mem_primeFactors hp
  rw [Prime.dvd_finsetProd_iff hpp.prime] at hdvd
  obtain ⟨⟨x, y⟩, hxy, hd⟩ := hdvd
  rw [Finset.mem_offDiag, Finset.mem_Icc, Finset.mem_Icc] at hxy
  have hd' : p ∣ x + y := hd
  have hle := Nat.le_of_dvd (by omega) hd'
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hpp⟩

theorem OMA.solution : type_of% @Erdos126.erdos_126.variants.IsBigO := by
  intro f hf
  constructor
  · -- lower bound: `log n ≤ 2 * f n` for `n ≥ 3`
    refine Asymptotics.IsBigO.of_bound 2 ?_
    rw [Filter.eventually_atTop]
    refine ⟨3, fun n hn => ?_⟩
    have hmem : Nat.log 2 (n - 1) ∈ {m | ∀ A : Finset ℕ, A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card} := by
      intro A hA
      have h1 := OMA.card_le A
      have h2 := Finset.pred_card_le_card_erase (s := A) (a := 0)
      rw [hA] at h2
      have h3 : n - 1 ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card := by omega
      exact le_trans (Nat.log_mono_right h3) (le_of_eq (Nat.log_pow (by norm_num) _))
    have hL : Nat.log 2 (n - 1) ≤ f n := (hf n).2 hmem
    have hpow : n - 1 < 2 ^ (Nat.log 2 (n - 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hL1 : 1 ≤ Nat.log 2 (n - 1) := by
      have : Nat.log 2 2 ≤ Nat.log 2 (n - 1) := Nat.log_mono_right (by omega)
      have h22 : Nat.log 2 2 = 1 := by
        have := Nat.log_pow (b := 2) (by norm_num) 1
        simpa using this
      omega
    have hn' : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (n - 1) + 1) := by
      have : n ≤ 2 ^ (Nat.log 2 (n - 1) + 1) := by omega
      exact_mod_cast this
    have hnpos : (0 : ℝ) < n := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hlog : Real.log n ≤ ((Nat.log 2 (n - 1) + 1 : ℕ) : ℝ) * Real.log 2 := by
      have h := Real.log_le_log hnpos hn'
      rw [Real.log_pow] at h
      exact h
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
    have hcast : ((Nat.log 2 (n - 1) + 1 : ℕ) : ℝ) ≤ 2 * (f n : ℝ) := by
      have : Nat.log 2 (n - 1) + 1 ≤ 2 * f n := by omega
      exact_mod_cast this
    have hnonneg : (0 : ℝ) ≤ ((Nat.log 2 (n - 1) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_of_nonneg hlogn, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc Real.log n ≤ ((Nat.log 2 (n - 1) + 1 : ℕ) : ℝ) * Real.log 2 := hlog
      _ ≤ ((Nat.log 2 (n - 1) + 1 : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2 hnonneg
      _ ≤ 2 * (f n : ℝ) := by linarith
  · -- upper bound: `f n ≤ π (2 n) ≤ C * n / log n`
    have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    refine Asymptotics.IsBigO.of_bound (2 * (Real.log 4 + 1)) ?_
    have hev := Chebyshev.eventually_primeCounting_le (ε := 1) one_pos
    have htend : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
    filter_upwards [htend.eventually hev, Filter.eventually_ge_atTop 2] with n hn hn2
    have hfn : f n ≤ Nat.primeCounting (2 * n) :=
      le_trans ((hf n).1 (Finset.Icc 1 n) (by simp)) (OMA.card_primeFactors_Icc n)
    have hfloor : ⌊(2 : ℝ) * (n : ℝ)⌋₊ = 2 * n := by
      rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring]
      exact Nat.floor_natCast _
    rw [hfloor] at hn
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hlog2n : Real.log n ≤ Real.log (2 * n) := Real.log_le_log (by linarith) (by linarith)
    have hnum : 0 ≤ (Real.log 4 + 1) * (2 * (n : ℝ)) := by positivity
    have h1 : (Real.log 4 + 1) * (2 * (n : ℝ)) / Real.log (2 * n) ≤
        (Real.log 4 + 1) * (2 * (n : ℝ)) / Real.log n :=
      div_le_div_of_nonneg_left hnum hlogn hlog2n
    have hfn' : (f n : ℝ) ≤ (Nat.primeCounting (2 * n) : ℝ) := by exact_mod_cast hfn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
    calc (f n : ℝ) ≤ (Nat.primeCounting (2 * n) : ℝ) := hfn'
      _ ≤ (Real.log 4 + 1) * (2 * (n : ℝ)) / Real.log (2 * n) := hn
      _ ≤ (Real.log 4 + 1) * (2 * (n : ℝ)) / Real.log n := h1
      _ = 2 * (Real.log 4 + 1) * ((n : ℝ) / Real.log n) := by ring
