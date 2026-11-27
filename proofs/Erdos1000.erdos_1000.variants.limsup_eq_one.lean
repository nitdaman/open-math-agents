import FormalConjectures.ErdosProblems.«1000»

-- Problem: Erdős Problem 1000 — limsup eq one
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1000.lean:149 (declaration Erdos1000.erdos_1000.variants.limsup_eq_one)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.O10

open Filter Topology

/-- If a prime power `p ^ a` divides `n k` but no earlier `n j`, then every `m` not divisible
by `p` gives a new fraction `m / n k`. -/
theorem count_new (n : ℕ → ℕ) (k p a : ℕ) (hp : p.Prime) (hpa : p ^ a ∣ n k)
    (hnot : ∀ j < k, ¬ p ^ a ∣ n j) : n k - n k / p ≤ Erdos1000.phiSeq n k := by
  classical
  set N := n k with hN
  have hsub : (Finset.Icc 1 N).filter (fun m => ¬ p ∣ m) ⊆
      (Finset.Icc 1 N).filter (fun m => ∀ j < k, ¬ (N / Nat.gcd m N) ∣ n j) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, ?_⟩
    intro j hj hd
    have hg : Nat.gcd m N ∣ m := Nat.gcd_dvd_left m N
    have hpg : ¬ p ∣ Nat.gcd m N := fun h => hm.2 (h.trans hg)
    have hcop : Nat.Coprime (p ^ a) (Nat.gcd m N) :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpg)
    have hmul : N / Nat.gcd m N * Nat.gcd m N = N := Nat.div_mul_cancel (Nat.gcd_dvd_right m N)
    have h1 : p ^ a ∣ N / Nat.gcd m N * Nat.gcd m N := by rw [hmul]; exact hpa
    have h2 : p ^ a ∣ N / Nat.gcd m N := Nat.Coprime.dvd_of_dvd_mul_right hcop h1
    exact hnot j hj (h2.trans hd)
  have hcard := Finset.card_le_card hsub
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 N) (fun m => p ∣ m)
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := rfl
  have hdiv : ((Finset.Icc 1 N).filter (fun m => p ∣ m)).card = N / p := by
    rw [hIcc]; exact Nat.Ioc_filter_dvd_card_eq_div N p
  have hcardI : (Finset.Icc 1 N).card = N := by simp
  have hphi : Erdos1000.phiSeq n k =
      ((Finset.Icc 1 N).filter (fun m => ∀ j < k, ¬ (N / Nat.gcd m N) ∣ n j)).card := rfl
  rw [hphi]
  omega

theorem phiSeq_le (n : ℕ → ℕ) (k : ℕ) : Erdos1000.phiSeq n k ≤ n k := by
  unfold Erdos1000.phiSeq
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- A number all of whose prime factors are at most `M` has `N ≤ φ(N) * P`, where `P` is the
product of the primes up to `M`. -/
theorem smooth_bound (N M : ℕ) (hs : ∀ q ∈ N.primeFactors, q ≤ M) :
    N ≤ N.totient * ∏ p ∈ (Finset.range (M + 1)).filter Nat.Prime, p := by
  have h1 := Nat.totient_mul_prod_primeFactors N
  have h2 : 0 < ∏ p ∈ N.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h3 : ∏ p ∈ N.primeFactors, p ∣ ∏ p ∈ (Finset.range (M + 1)).filter Nat.Prime, p := by
    apply Finset.prod_dvd_prod_of_subset N.primeFactors _ (fun p => p)
    intro q hq
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hs q hq), Nat.prime_of_mem_primeFactors hq⟩
  have hPpos : 0 < ∏ p ∈ (Finset.range (M + 1)).filter Nat.Prime, p :=
    Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  have h4 := Nat.le_of_dvd hPpos h3
  calc N ≤ N * ∏ p ∈ N.primeFactors, (p - 1) := Nat.le_mul_of_pos_right N h2
    _ = N.totient * ∏ p ∈ N.primeFactors, p := h1.symm
    _ ≤ N.totient * ∏ p ∈ (Finset.range (M + 1)).filter Nat.Prime, p :=
        Nat.mul_le_mul_left _ h4

end OMA.O10

open Filter Topology in
theorem OMA.solution : type_of% @Erdos1000.erdos_1000.variants.limsup_eq_one := by
  intro n hn hn0 hlim
  have hnpos : ∀ k, 0 < n k := fun k => hn0.trans_le (hn.monotone (Nat.zero_le k))
  have hr1 : ∀ k, (Erdos1000.phiSeq n k : ℝ) / (n k : ℝ) ≤ 1 := by
    intro k
    rw [div_le_one (by exact_mod_cast hnpos k)]
    exact_mod_cast OMA.O10.phiSeq_le n k
  have hr0 : ∀ k, 0 ≤ (Erdos1000.phiSeq n k : ℝ) / (n k : ℝ) := fun k => by positivity
  apply le_antisymm
  · exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop hr0) (Eventually.of_forall hr1)
  · apply le_of_forall_sub_le
    intro ε hε
    refine le_limsup_of_frequently_le ?_ (isBoundedUnder_of ⟨1, hr1⟩)
    rw [frequently_atTop]
    intro K
    set M := max (n K) ⌈1 / ε⌉₊ with hM
    set P := ∏ p ∈ (Finset.range (M + 1)).filter Nat.Prime, p with hP
    have hPpos : 0 < P := Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
    have hPposR : (0 : ℝ) < P := by exact_mod_cast hPpos
    have hlt : atTop.liminf (fun k : ℕ => (Erdos1000.phiSeq n k : ℝ) / (n k : ℝ)) < 1 / P := by
      rw [hlim]; positivity
    have hfreq := frequently_lt_of_liminf_lt (isCoboundedUnder_ge_of_le atTop hr1) hlt
    obtain ⟨k, hk⟩ := hfreq.exists
    have hq : ∃ q ∈ (n k).primeFactors, M < q := by
      by_contra hcon
      push Not at hcon
      have hb := OMA.O10.smooth_bound (n k) M hcon
      have ht := Erdos1000.erdos_1000.variants.totient_le n hn hn0 k
      have hb2 : n k ≤ Erdos1000.phiSeq n k * P :=
        hb.trans (Nat.mul_le_mul_right _ ht)
      have hnkR : (0 : ℝ) < n k := by exact_mod_cast hnpos k
      have hb3 : (n k : ℝ) ≤ (Erdos1000.phiSeq n k : ℝ) * P := by exact_mod_cast hb2
      have h5 : (1 : ℝ) / P ≤ (Erdos1000.phiSeq n k : ℝ) / (n k : ℝ) := by
        rw [div_le_div_iff₀ hPposR hnkR]
        linarith
      linarith
    obtain ⟨q, hqf, hqM⟩ := hq
    have hqp := Nat.prime_of_mem_primeFactors hqf
    have hqd := Nat.dvd_of_mem_primeFactors hqf
    have hex : ∃ j, q ∣ n j := ⟨k, hqd⟩
    classical
    have hk'd : q ∣ n (Nat.find hex) := Nat.find_spec hex
    have hk'min : ∀ j < Nat.find hex, ¬ q ∣ n j := fun j hj => Nat.find_min hex hj
    have hk'K : K ≤ Nat.find hex := by
      by_contra hlt2
      push Not at hlt2
      have h1 : n (Nat.find hex) ≤ n K := hn.monotone hlt2.le
      have h2 := Nat.le_of_dvd (hnpos _) hk'd
      have h3 : n K ≤ M := le_max_left _ _
      omega
    refine ⟨Nat.find hex, hk'K, ?_⟩
    have hc := OMA.O10.count_new n (Nat.find hex) q 1 hqp (by simpa using hk'd)
      (by simpa using hk'min)
    set N := n (Nat.find hex) with hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hnpos _
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hdivle : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
    have hq1 : (1 : ℝ) / ε < q := by
      have h1 := Nat.le_ceil (1 / ε)
      have h2 : ⌈1 / ε⌉₊ < q := lt_of_le_of_lt (le_max_right _ _) hqM
      have h3 : (⌈1 / ε⌉₊ : ℝ) < q := by exact_mod_cast h2
      linarith
    have hqε : 1 < q * ε := (div_lt_iff₀ hε).mp hq1
    have hNq : (N : ℝ) / q ≤ N * ε := by
      rw [div_le_iff₀ hqpos]
      nlinarith
    have hcR : ((N - N / q : ℕ) : ℝ) ≤ (Erdos1000.phiSeq n (Nat.find hex) : ℝ) := by
      exact_mod_cast hc
    rw [Nat.cast_sub (Nat.div_le_self N q)] at hcR
    rw [le_div_iff₀ hNpos]
    linarith
