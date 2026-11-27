import FormalConjectures.ErdosProblems.«1000»

-- Problem: Erdős Problem 1000 — not tendsto zero
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1000.lean:140 (declaration Erdos1000.erdos_1000.variants.not_tendsto_zero)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.O10

open Filter Topology

/-- If a prime power `p ^ a` divides `n k` but no earlier `n j`, then at least half of the
fractions `m / n k` are new. -/
theorem half (n : ℕ → ℕ) (k p a : ℕ) (hp : p.Prime) (hpa : p ^ a ∣ n k)
    (hnot : ∀ j < k, ¬ p ^ a ∣ n j) : n k ≤ 2 * Erdos1000.phiSeq n k := by
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
  have hp2 : N / p ≤ N / 2 := Nat.div_le_div_left hp.two_le (by norm_num)
  have hphi : Erdos1000.phiSeq n k =
      ((Finset.Icc 1 N).filter (fun m => ∀ j < k, ¬ (N / Nat.gcd m N) ∣ n j)).card := rfl
  rw [hphi]
  omega

end OMA.O10

open Filter Topology in
theorem OMA.solution : type_of% @Erdos1000.erdos_1000.variants.not_tendsto_zero := by
  intro n hn hn0 hT
  have hev := hT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  have hrec : ∃ k ≥ K, ¬ n k ∣ (Finset.range k).lcm n := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ k, n k ∣ (Finset.range K).lcm n := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        by_cases hk : k < K
        · exact Finset.dvd_lcm (Finset.mem_range.mpr hk)
        · exact (hcon k (by omega)).trans
            (Finset.lcm_dvd (fun j hj => ih j (Finset.mem_range.mp hj)))
    have hne : (Finset.range K).lcm n ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]
      rintro ⟨j, _, hj⟩
      have := hn0.trans_le (hn.monotone (Nat.zero_le j))
      omega
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (hall ((Finset.range K).lcm n + 1))
    have h2 : (Finset.range K).lcm n + 1 ≤ n ((Finset.range K).lcm n + 1) := hn.id_le _
    omega
  obtain ⟨k, hkK, hk⟩ := hrec
  rw [Nat.dvd_iff_prime_pow_dvd_dvd] at hk
  push Not at hk
  obtain ⟨p, a, hp, hpa, hnot⟩ := hk
  have hnot' : ∀ j < k, ¬ p ^ a ∣ n j := fun j hj h =>
    hnot (h.trans (Finset.dvd_lcm (Finset.mem_range.mpr hj)))
  have h2 := OMA.O10.half n k p a hp hpa hnot'
  have hK' := hK k hkK
  have hpos : (0 : ℝ) < n k := by
    exact_mod_cast hn0.trans_le (hn.monotone (Nat.zero_le k))
  rw [div_lt_iff₀ hpos] at hK'
  have h3 : (n k : ℝ) ≤ 2 * (Erdos1000.phiSeq n k : ℝ) := by exact_mod_cast h2
  linarith
