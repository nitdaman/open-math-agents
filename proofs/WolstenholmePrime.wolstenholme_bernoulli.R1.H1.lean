import OMAReductions.R_WolstenholmePrime_wolstenholme_bernoulli_R1

-- Step WolstenholmePrime.wolstenholme_bernoulli.R1.H1: hypothesis H1 of reduction WolstenholmePrime.wolstenholme_bernoulli.R1
-- Credit: @ivillar
-- H1 is word for word the statement WolstenholmePrime.wolstenholme_harmonic, already proved in this
-- repository by @Genbox (proofs/WolstenholmePrime.wolstenholme_harmonic.lean). The whole argument below is
-- copied unchanged from that accepted file; only the final theorem now names the step H1.
-- Strategy. Pair k with p - k: (p+k)(2p-k) = k(p-k) + 2p^2 and 1/k + 1/(p-k) = p/(k(p-k)). So
-- C(2p-1,p-1)·D = ∏(d_k + 2p^2) ≡ D + 2p^2 R (mod 4p^4) and H_{p-1} = pR/D, with D = ∏ d_k prime to p.
-- Both conditions are then equivalent to p^2 ∣ R.


open Finset

namespace OMA.Wolstenholme

lemma pair_prod {M : Type*} [CommMonoid M] (g : ℕ → M) (h : ℕ) :
    ∏ j ∈ Ico 1 (2 * h + 1), g j = ∏ k ∈ Ico 1 (h + 1), (g k * g (2 * h + 1 - k)) := by
  rw [prod_mul_distrib, ← prod_Ico_consecutive g (by omega : 1 ≤ h + 1) (by omega : h + 1 ≤ 2 * h + 1),
    prod_Ico_reflect g 1 (by omega : h + 1 ≤ 2 * h + 1 + 1),
    show 2 * h + 1 + 1 - (h + 1) = h + 1 by omega, show 2 * h + 1 + 1 - 1 = 2 * h + 1 by omega]

lemma pair_sum {M : Type*} [AddCommMonoid M] (g : ℕ → M) (h : ℕ) :
    ∑ j ∈ Ico 1 (2 * h + 1), g j = ∑ k ∈ Ico 1 (h + 1), (g k + g (2 * h + 1 - k)) := by
  rw [sum_add_distrib, ← sum_Ico_consecutive g (by omega : 1 ≤ h + 1) (by omega : h + 1 ≤ 2 * h + 1),
    sum_Ico_reflect g 1 (by omega : h + 1 ≤ 2 * h + 1 + 1),
    show 2 * h + 1 + 1 - (h + 1) = h + 1 by omega, show 2 * h + 1 + 1 - 1 = 2 * h + 1 by omega]

lemma asc (p : ℕ) : ∀ m, p.factorial * ∏ j ∈ Ico 1 (m + 1), (p + j) = (p + m).factorial := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_Ico_succ_top (by omega), ← mul_assoc, ih, show p + (m + 1) = (p + m) + 1 by ring,
      Nat.factorial_succ]
    ring

lemma expand (d : ℕ → ℤ) (x : ℤ) (s : Finset ℕ) :
    ∃ W : ℤ, ∏ k ∈ s, (d k + x) =
      ∏ k ∈ s, d k + x * ∑ k ∈ s, ∏ j ∈ s.erase k, d j + x ^ 2 * W := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨W, hW⟩ := ih
    have hR : ∑ k ∈ insert a s, ∏ j ∈ (insert a s).erase k, d j =
        ∏ j ∈ s, d j + d a * ∑ k ∈ s, ∏ j ∈ s.erase k, d j := by
      rw [sum_insert ha, erase_insert ha, mul_sum]
      congr 1
      apply sum_congr rfl
      intro k hk
      have hka : k ≠ a := fun h => ha (h ▸ hk)
      rw [erase_insert_of_ne (Ne.symm hka), prod_insert (fun h => ha (mem_of_mem_erase h))]
    refine ⟨∑ k ∈ s, ∏ j ∈ s.erase k, d j + d a * W + x * W, ?_⟩
    rw [hR, prod_insert ha, prod_insert ha, hW]
    ring

lemma num_dvd_iff (a D : ℤ) (n : ℤ) (hD : D ≠ 0) (hc : IsCoprime n D) :
    n ∣ ((a : ℚ) / D).num ↔ n ∣ a := by
  set q : ℚ := (a : ℚ) / D with hq
  have key : (q.num : ℤ) * D = a * q.den := by
    have h1 := Rat.mul_den_eq_num q
    have h2 : q * D = a := by rw [hq]; field_simp
    have : ((q.num : ℤ) : ℚ) * D = (a : ℚ) * q.den := by
      rw [← h1, ← h2]; ring
    exact_mod_cast this
  have hden : (q.den : ℤ) ∣ D := by
    have := Rat.den_dvd a D
    rwa [Rat.divInt_eq_div] at this
  obtain ⟨t, ht⟩ := hden
  have hcd : IsCoprime n (q.den : ℤ) := by
    rw [ht] at hc; exact hc.of_mul_right_left
  constructor
  · intro h
    have : n ∣ a * q.den := key ▸ dvd_mul_of_dvd_left h D
    exact hcd.dvd_of_dvd_mul_right this
  · intro h
    have : n ∣ q.num * D := key ▸ dvd_mul_of_dvd_left h _
    exact hc.dvd_of_dvd_mul_right this

theorem core (h : ℕ) (hp : (2 * h + 1).Prime) :
    (2 * (2 * h + 1) - 1).choose (2 * h + 1 - 1) ≡ 1 [MOD (2 * h + 1) ^ 4] ↔
      (((2 * h + 1) ^ 3 : ℕ) : ℤ) ∣ (harmonic (2 * h + 1 - 1)).num := by
  set p := 2 * h + 1 with hpdef
  set s := Ico 1 (h + 1) with hs
  set d : ℕ → ℤ := fun k => ((k * (p - k) : ℕ) : ℤ) with hd
  set D := ∏ k ∈ s, d k with hDdef
  set R := ∑ k ∈ s, ∏ j ∈ s.erase k, d j with hRdef
  set C := (2 * p - 1).choose (p - 1) with hC
  have hcopk : ∀ k ∈ s, Nat.Coprime p (k * (p - k)) := by
    intro k hk
    rw [mem_Ico] at hk
    exact Nat.Coprime.mul_right (Nat.coprime_of_lt_prime (by omega) (by omega) hp)
      (Nat.coprime_of_lt_prime (by omega) (by omega) hp)
  have hcop : IsCoprime (p : ℤ) D := by
    apply IsCoprime.prod_right
    intro k hk
    exact Nat.isCoprime_iff_coprime.2 (hcopk k hk)
  have hdne : ∀ k ∈ s, d k ≠ 0 := by
    intro k hk
    rw [mem_Ico] at hk
    simp only [hd, ne_eq, Nat.cast_eq_zero, mul_eq_zero, not_or]
    omega
  have hDne : D ≠ 0 := prod_ne_zero_iff.2 hdne
  -- (A)
  have hA : (C : ℤ) * D = ∏ k ∈ s, (d k + 2 * (p : ℤ) ^ 2) := by
    have h1 : C * (p - 1).factorial * p.factorial = (2 * p - 1).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (n := 2 * p - 1) (k := p - 1) (by omega)
      rwa [show 2 * p - 1 - (p - 1) = p by omega] at this
    have h2 : p.factorial * ∏ j ∈ Ico 1 p, (p + j) = (2 * p - 1).factorial := by
      have := asc p (p - 1)
      rwa [show p - 1 + 1 = p by omega, show p + (p - 1) = 2 * p - 1 by omega] at this
    have h3 : C * (p - 1).factorial = ∏ j ∈ Ico 1 p, (p + j) := by
      have hpf := Nat.factorial_pos p
      apply Nat.eq_of_mul_eq_mul_left hpf
      rw [h2, ← h1]; ring
    have h4 : (p - 1).factorial = ∏ j ∈ Ico 1 p, j := by
      rw [← prod_Ico_id_eq_factorial, show p - 1 + 1 = p by omega]
    have h5 : ((C * (p - 1).factorial : ℕ) : ℤ) = ∏ k ∈ s, (d k + 2 * (p : ℤ) ^ 2) := by
      rw [h3, Nat.cast_prod, hpdef, pair_prod]
      apply prod_congr rfl
      intro k hk
      rw [mem_Ico] at hk
      simp only [hd]
      push_cast [show k ≤ 2 * h + 1 by omega, show 2 * h + 1 - k ≤ 2 * h + 1 by omega]
      rw [Nat.cast_sub (by omega : k ≤ 2 * h + 1)]
      push_cast
      ring
    have h6 : (((p - 1).factorial : ℕ) : ℤ) = D := by
      rw [h4, Nat.cast_prod, hDdef, hs, hpdef, pair_prod]
      apply prod_congr rfl
      intro k hk
      simp [hd, hpdef]
    rw [← h6, ← h5]; push_cast; ring
  -- (B)
  obtain ⟨W, hW⟩ := expand d (2 * (p : ℤ) ^ 2) s
  -- (C)
  have hH : harmonic (p - 1) = ((p * R : ℤ) : ℚ) / (D : ℚ) := by
    rw [harmonic_eq_sum_Icc, show p - 1 = 2 * h by omega,
      show Icc 1 (2 * h) = Ico 1 (2 * h + 1) by ext; simp, hpdef, pair_sum]
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDne
    rw [eq_div_iff hDq, sum_mul]
    push_cast
    rw [hRdef, Int.cast_sum, mul_sum]
    apply sum_congr rfl
    intro k hk
    have hk' := hk
    rw [mem_Ico] at hk'
    have hmul := prod_erase_mul s d hk
    have hdk : (d k : ℚ) ≠ 0 := by exact_mod_cast hdne k hk
    rw [hDdef, ← hmul]
    simp only [hd] at hdk ⊢
    push_cast [Nat.cast_sub (by omega : k ≤ 2 * h + 1)] at hdk ⊢
    rw [Nat.cast_sub (by omega : k ≤ 2 * h + 1)] at hdk ⊢
    push_cast at hdk ⊢
    have hk0 : (k : ℚ) ≠ 0 := by
      intro h0; apply hdk; rw [h0]; ring
    have hk1 : (2 * (h : ℚ) + 1 - k) ≠ 0 := by
      intro h0; apply hdk; rw [h0]; ring
    field_simp
    ring
  -- conclude
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcop2 : IsCoprime ((p : ℤ) ^ 2) 2 := by
    apply IsCoprime.pow_left
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
  have lhs : C ≡ 1 [MOD p ^ 4] ↔ (p : ℤ) ^ 2 ∣ R := by
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd, Nat.cast_one]
    have e1 : ((p ^ 4 : ℕ) : ℤ) ∣ (C : ℤ) - 1 ↔ ((p : ℤ) ^ 4) ∣ ((C : ℤ) - 1) * D := by
      push_cast
      constructor
      · intro h; exact dvd_mul_of_dvd_right h _ |>.trans (by rw [mul_comm])
      · intro h; exact (hcop.pow_left).dvd_of_dvd_mul_right h
    have e2 : ((C : ℤ) - 1) * D = (p : ℤ) ^ 2 * (2 * R) + (p : ℤ) ^ 4 * (4 * W) := by
      rw [sub_mul, hA, hW]; ring
    rw [e1, e2, (dvd_add_left (dvd_mul_right _ _)), show (p : ℤ) ^ 4 = (p : ℤ) ^ 2 * (p : ℤ) ^ 2 by ring,
      mul_dvd_mul_iff_left (pow_ne_zero 2 hp0)]
    constructor
    · intro h; exact hcop2.dvd_of_dvd_mul_left h
    · intro h; exact dvd_mul_of_dvd_right h 2
  have rhs : (((p ^ 3 : ℕ) : ℤ)) ∣ (harmonic (p - 1)).num ↔ (p : ℤ) ^ 2 ∣ R := by
    rw [hH, num_dvd_iff _ _ _ hDne (by push_cast; exact hcop.pow_left)]
    push_cast
    rw [show (p : ℤ) ^ 3 = p * p ^ 2 by ring, mul_dvd_mul_iff_left hp0]
  rw [lhs, rhs]

end OMA.Wolstenholme

theorem OMA.solution : OMA.R_WolstenholmePrime_wolstenholme_bernoulli_R1.H1 := by
  unfold OMA.R_WolstenholmePrime_wolstenholme_bernoulli_R1.H1
  intro p
  unfold WolstenholmePrime.IsWolstenholmePrime
  constructor
  · rintro ⟨h7, hp, hm⟩
    refine ⟨h7, hp, ?_⟩
    obtain ⟨h, rfl⟩ : ∃ h, p = 2 * h + 1 := by
      rcases hp.eq_two_or_odd' with rfl | ⟨h, rfl⟩
      · omega
      · exact ⟨h, rfl⟩
    exact (OMA.Wolstenholme.core h hp).1 hm
  · rintro ⟨h7, hp, hm⟩
    refine ⟨h7, hp, ?_⟩
    obtain ⟨h, rfl⟩ : ∃ h, p = 2 * h + 1 := by
      rcases hp.eq_two_or_odd' with rfl | ⟨h, rfl⟩
      · omega
      · exact ⟨h, rfl⟩
    exact (OMA.Wolstenholme.core h hp).2 hm
