import FormalConjectures.ErdosProblems.«1189»

-- Problem: Erdős Problem 1189 — iv
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

namespace OMASun

lemma CL (L d : ℕ) (r : ℤ) (hd : 0 < d) (hdL : d ∣ L) :
    ((range L).filter (fun c : ℕ => (c : ℤ) ≡ r [ZMOD (d : ℤ)])).card ≤ L / d := by
  rw [← Finset.card_range (L / d)]
  apply Finset.card_le_card_of_injOn (· / d)
  · intro c hc
    try rw [Finset.mem_coe] at hc
    rw [mem_filter, mem_range] at hc
    exact mem_range.2 (Nat.div_lt_div_of_lt_of_dvd hdL hc.1)
  · intro c hc c' hc' h
    try rw [Finset.mem_coe] at hc hc'
    rw [mem_filter, mem_range] at hc hc'
    have hm : c % d = c' % d := by
      have := hc.2.trans hc'.2.symm
      unfold Int.ModEq at this
      exact_mod_cast this
    have h' : c / d = c' / d := h
    rw [← Nat.div_add_mod c d, ← Nat.div_add_mod c' d, h', hm]

lemma geom (q : ℕ) : ∑ j ∈ range q, 2 ^ j + 1 = 2 ^ q := by
  induction q with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

lemma G (q : ℕ) : ∑ i ∈ range q, 2 ^ (q - 1 - i) + 1 = 2 ^ q := by
  rw [Finset.sum_range_reflect (fun j => 2 ^ j) q]
  exact geom q

lemma S1 (q u : ℕ) : ∑ t ∈ range (q + 1), (if t = q then 1 else u) = q * u + 1 := by
  rw [sum_range_succ, if_pos rfl]
  rw [Finset.sum_congr rfl (g := fun _ => u)]
  · simp
  · intro t ht
    rw [if_neg (by have := mem_range.1 ht; omega)]

lemma core (q p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ → ℤ) (I2 Ip : Finset ℕ)
    (hI2 : I2 ⊆ range q) (hIp : ∀ t ∈ Ip, t ≤ q)
    (hcov : ∀ x : ℕ, x < 2 ^ q * p →
      (∃ i ∈ I2, (x : ℤ) ≡ a (2 ^ (i + 1)) [ZMOD ((2 ^ (i + 1) : ℕ) : ℤ)]) ∨
      (∃ t ∈ Ip, (x : ℤ) ≡ a (2 ^ t * p) [ZMOD ((2 ^ t * p : ℕ) : ℤ)])) :
    ∃ u : ℕ, 2 ^ q ≤ u + ∑ i ∈ I2, 2 ^ (q - 1 - i) ∧
      p * u ≤ ∑ t ∈ Ip, (if t = q then 1 else u) := by
  set K := 2 ^ q with hK
  have hKpos : 0 < K := by positivity
  have hppos : 0 < p := hp.pos
  set U := (range K).filter
    (fun c : ℕ => ∀ i ∈ I2, ¬ (c : ℤ) ≡ a (2 ^ (i + 1)) [ZMOD ((2 ^ (i + 1) : ℕ) : ℤ)]) with hU
  refine ⟨U.card, ?_, ?_⟩
  · calc 2 ^ q = (range K).card := by simp [K]
      _ ≤ (U ∪ I2.biUnion (fun i => (range K).filter
            (fun c : ℕ => (c : ℤ) ≡ a (2 ^ (i + 1)) [ZMOD ((2 ^ (i + 1) : ℕ) : ℤ)]))).card := by
          apply card_le_card
          intro c hc
          by_cases h : ∀ i ∈ I2, ¬ (c : ℤ) ≡ a (2 ^ (i + 1)) [ZMOD ((2 ^ (i + 1) : ℕ) : ℤ)]
          · exact mem_union_left _ (mem_filter.2 ⟨hc, h⟩)
          · push Not at h
            obtain ⟨i, hi, hci⟩ := h
            exact mem_union_right _ (mem_biUnion.2 ⟨i, hi, mem_filter.2 ⟨hc, hci⟩⟩)
      _ ≤ U.card + (I2.biUnion (fun i => (range K).filter
            (fun c : ℕ => (c : ℤ) ≡ a (2 ^ (i + 1)) [ZMOD ((2 ^ (i + 1) : ℕ) : ℤ)]))).card :=
          card_union_le _ _
      _ ≤ U.card + ∑ i ∈ I2, ((range K).filter
            (fun c : ℕ => (c : ℤ) ≡ a (2 ^ (i + 1)) [ZMOD ((2 ^ (i + 1) : ℕ) : ℤ)])).card := by
          gcongr; exact card_biUnion_le
      _ ≤ U.card + ∑ i ∈ I2, 2 ^ (q - 1 - i) := by
          gcongr with i hi
          have hiq : i < q := mem_range.1 (hI2 hi)
          have := CL K (2 ^ (i + 1)) (a (2 ^ (i + 1))) (by positivity)
            (pow_dvd_pow 2 (by omega))
          rwa [hK, Nat.pow_div (by omega) (by norm_num),
            show q - (i + 1) = q - 1 - i by omega] at this
  · set T := (range (K * p)).filter (fun x => x % K ∈ U) with hT
    have hT1 : p * U.card ≤ T.card := by
      rw [mul_comm, ← card_range p, ← card_product]
      apply card_le_card_of_injOn (fun cj : ℕ × ℕ => cj.1 + K * cj.2)
      · intro cj hcj
        try rw [Finset.mem_coe] at hcj
        rw [mem_product] at hcj
        obtain ⟨hc, hj⟩ := hcj
        have hcK : cj.1 < K := mem_range.1 (mem_filter.1 hc).1
        have hj' : cj.2 < p := mem_range.1 hj
        refine mem_filter.2 ⟨mem_range.2 ?_, ?_⟩
        · have : K * cj.2 + K ≤ K * p := by
            calc K * cj.2 + K = K * (cj.2 + 1) := by ring
              _ ≤ K * p := Nat.mul_le_mul_left _ hj'
          show cj.1 + K * cj.2 < K * p; omega
        · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcK]; exact hc
      · intro cj hcj cj' hcj' h
        try rw [Finset.mem_coe] at hcj hcj'
        rw [mem_product] at hcj hcj'
        have hcK : cj.1 < K := mem_range.1 (mem_filter.1 hcj.1).1
        have hcK' : cj'.1 < K := mem_range.1 (mem_filter.1 hcj'.1).1
        have h' : cj.1 + K * cj.2 = cj'.1 + K * cj'.2 := h
        have e1 := congrArg (· % K) h'
        have e2 := congrArg (· / K) h'
        simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcK, Nat.mod_eq_of_lt hcK'] at e1
        simp only [Nat.add_mul_div_left _ _ hKpos, Nat.div_eq_of_lt hcK, Nat.div_eq_of_lt hcK',
          zero_add] at e2
        exact Prod.ext e1 e2
    have hT2 : T ⊆ Ip.biUnion (fun t => T.filter
        (fun x : ℕ => (x : ℤ) ≡ a (2 ^ t * p) [ZMOD ((2 ^ t * p : ℕ) : ℤ)])) := by
      intro x hx
      have hx' := mem_filter.1 hx
      rcases hcov x (mem_range.1 hx'.1) with ⟨i, hi, hxi⟩ | ⟨t, ht, hxt⟩
      · exfalso
        have hU' := (mem_filter.1 hx'.2).2 i hi
        apply hU'
        have hiq : i < q := mem_range.1 (hI2 hi)
        have hdvd : ((2 ^ (i + 1) : ℕ) : ℤ) ∣ (K : ℤ) := by
          exact_mod_cast pow_dvd_pow 2 (show i + 1 ≤ q by omega)
        have h1 : ((x % K : ℕ) : ℤ) ≡ (x : ℤ) [ZMOD ((2 ^ (i + 1) : ℕ) : ℤ)] := by
          rw [Int.natCast_mod]; exact (Int.mod_modEq _ _).of_dvd hdvd
        exact h1.trans hxi
      · exact mem_biUnion.2 ⟨t, ht, mem_filter.2 ⟨hx, hxt⟩⟩
    calc p * U.card ≤ T.card := hT1
      _ ≤ (Ip.biUnion (fun t => T.filter
          (fun x : ℕ => (x : ℤ) ≡ a (2 ^ t * p) [ZMOD ((2 ^ t * p : ℕ) : ℤ)]))).card :=
          card_le_card hT2
      _ ≤ ∑ t ∈ Ip, (T.filter
          (fun x : ℕ => (x : ℤ) ≡ a (2 ^ t * p) [ZMOD ((2 ^ t * p : ℕ) : ℤ)])).card :=
          card_biUnion_le
      _ ≤ ∑ t ∈ Ip, (if t = q then 1 else U.card) := by
          apply sum_le_sum
          intro t ht
          split_ifs with htq
          · have e : 2 ^ t * p = K * p := by rw [htq]
            calc (T.filter (fun x : ℕ => (x : ℤ) ≡ a (2 ^ t * p)
                    [ZMOD ((2 ^ t * p : ℕ) : ℤ)])).card
                ≤ ((range (K * p)).filter (fun x : ℕ => (x : ℤ) ≡ a (2 ^ t * p)
                    [ZMOD ((2 ^ t * p : ℕ) : ℤ)])).card :=
                  card_le_card (filter_subset_filter _ (filter_subset _ _))
              _ ≤ (K * p) / (2 ^ t * p) := CL _ _ _ (by positivity) (by rw [e])
              _ = 1 := by rw [e]; exact Nat.div_self (by positivity)
          · apply card_le_card_of_injOn (· % K)
            · intro x hx
              try rw [Finset.mem_coe] at hx
              exact (mem_filter.1 (mem_filter.1 hx).1).2
            · intro x hx y hy hxy
              try rw [Finset.mem_coe] at hx hy
              have hx1 := mem_filter.1 hx
              have hy1 := mem_filter.1 hy
              have hxlt : x < K * p := mem_range.1 (mem_filter.1 hx1.1).1
              have hylt : y < K * p := mem_range.1 (mem_filter.1 hy1.1).1
              have hpd : (p : ℤ) ∣ (y : ℤ) - x := by
                have h1 := Int.modEq_iff_dvd.1 (hx1.2.trans hy1.2.symm)
                refine dvd_trans ?_ h1
                push_cast
                exact Dvd.intro_left _ rfl
              have hKd : (K : ℤ) ∣ (y : ℤ) - x := by
                have : x % K = y % K := hxy
                exact (Nat.modEq_iff_dvd.1 this)
              have hcop : IsCoprime (K : ℤ) (p : ℤ) := by
                rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
                exact Nat.Coprime.pow_left q ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
              have hN : ((K * p : ℕ) : ℤ) ∣ (y : ℤ) - x := by
                push_cast; exact hcop.mul_dvd hKd hpd
              have hm := Nat.modEq_iff_dvd.2 hN
              unfold Nat.ModEq at hm
              rwa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hm

lemma pow_ne (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (i t : ℕ) : 2 ^ (i + 1) ≠ 2 ^ t * p := by
  intro h
  have : p ∣ 2 ^ (i + 1) := ⟨2 ^ t, by rw [h]; ring⟩
  have := hp.dvd_of_dvd_pow this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem sun (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Erdos1189.IsIrreducibleCoveringSet ((2 ^ (p - 1) * p).divisors.filter (1 < ·)) := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hodd) even_two
  have hp1 := hp.two_le
  set q := p - 1 with hq
  have hpq : p = q + 1 := by omega
  set M := (2 ^ q * p).divisors.filter (1 < ·) with hM
  have hN0 : 2 ^ q * p ≠ 0 := by positivity
  have memM : ∀ d, d ∈ M ↔ d ∣ 2 ^ q * p ∧ 1 < d := by
    intro d; simp [M, Nat.mem_divisors, hN0]
  have classify : ∀ d ∈ M, (∃ i < q, d = 2 ^ (i + 1)) ∨ (∃ t ≤ q, d = 2 ^ t * p) := by
    intro d hd
    obtain ⟨hdvd, hd1⟩ := (memM d).1 hd
    obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.1 hdvd
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
    rcases hp.eq_one_or_self_of_dvd z hz with rfl | rfl
    · left
      have : j ≠ 0 := by rintro rfl; simp at hd1
      exact ⟨j - 1, by omega, by rw [mul_one]; congr 1; omega⟩
    · right; exact ⟨j, hj, rfl⟩
  have pmem : ∀ t ≤ q, 2 ^ t * p ∈ M := by
    intro t ht
    rw [memM]
    refine ⟨Nat.mul_dvd_mul_right (pow_dvd_pow 2 ht) p, ?_⟩
    have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    nlinarith
  have tmem : ∀ i < q, 2 ^ (i + 1) ∈ M := by
    intro i hi
    rw [memM]
    refine ⟨Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) p, ?_⟩
    have : 2 ≤ 2 ^ (i + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpodd : ¬ 2 ∣ p := by
    intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  refine ⟨⟨fun m hm => ((memM m).1 hm).2, ?_⟩, ?_⟩
  · -- covering
    refine ⟨fun d => if p ∣ d then (2 ^ q : ℤ) * (padicValNat 2 d : ℤ) else ((d / 2 : ℕ) : ℤ),
      fun z => ?_⟩
    by_cases h : (2 ^ q : ℤ) ∣ z
    · obtain ⟨w, rfl⟩ := h
      have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
      set t := (w % (p : ℤ)).toNat with ht
      have htw : (t : ℤ) = w % p := Int.toNat_of_nonneg (Int.emod_nonneg _ hpz.ne')
      have htp : t < p := by
        have := Int.emod_lt_of_pos w hpz
        omega
      refine ⟨2 ^ t * p, pmem t (by omega), ?_⟩
      have hval : padicValNat 2 (2 ^ t * p) = t := by
        rw [padicValNat.mul (by positivity) hp.ne_zero, padicValNat.prime_pow,
          padicValNat.eq_zero_of_not_dvd hpodd, add_zero]
      dsimp only; rw [if_pos (dvd_mul_left p _), hval]
      apply Int.ModEq.symm
      rw [Int.modEq_iff_dvd]
      have e : (2 : ℤ) ^ q * w - 2 ^ q * t = (2 ^ q * p) * (w / p) := by
        rw [htw, Int.emod_def]; ring
      rw [e]
      apply Dvd.dvd.mul_right
      push_cast
      exact mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) _
    · have hex : ∃ i, ¬ (2 ^ i : ℤ) ∣ z := ⟨q, h⟩
      set i0 := Nat.find hex with hi0
      have hi0spec : ¬ (2 ^ i0 : ℤ) ∣ z := Nat.find_spec hex
      have hi0le : i0 ≤ q := Nat.find_min' hex h
      have hi0pos : i0 ≠ 0 := by
        intro h0; apply hi0spec; rw [h0]; simp
      have hj : (2 ^ (i0 - 1) : ℤ) ∣ z := by
        have := Nat.find_min hex (show i0 - 1 < i0 by omega)
        push Not at this; exact this
      refine ⟨2 ^ (i0 - 1 + 1), tmem (i0 - 1) (by omega), ?_⟩
      have hnd : ¬ p ∣ 2 ^ (i0 - 1 + 1) := by
        intro hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      dsimp only; rw [if_neg hnd, show 2 ^ (i0 - 1 + 1) / 2 = 2 ^ (i0 - 1) by rw [pow_succ]; simp]
      obtain ⟨w, hw⟩ := hj
      have hwodd : w % 2 = 1 := by
        rcases Int.emod_two_eq_zero_or_one w with h0 | h1
        · exfalso; apply hi0spec
          obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
          refine ⟨k, ?_⟩
          rw [hw, hk, show (2:ℤ) ^ i0 = 2 ^ (i0 - 1) * 2 by rw [← pow_succ]; congr 1; omega]; ring
        · exact h1
      apply Int.ModEq.symm
      rw [Int.modEq_iff_dvd]
      refine ⟨w / 2, ?_⟩
      rw [hw]
      have := Int.emod_add_mul_ediv w 2
      push_cast
      rw [pow_succ]
      linear_combination (-(2 : ℤ) ^ (i0 - 1)) * this + (2 : ℤ) ^ (i0 - 1) * hwodd
  · -- irreducible
    intro N' hN' hcovN
    obtain ⟨-, a, ha⟩ := hcovN
    obtain ⟨m0, hm0M, hm0N⟩ := Finset.exists_of_ssubset hN'
    set I2 := (range q).filter (fun i => 2 ^ (i + 1) ≠ m0) with hI2
    set Ip := (range (q + 1)).filter (fun t => 2 ^ t * p ≠ m0) with hIp
    have hcov : ∀ x : ℕ, x < 2 ^ q * p →
        (∃ i ∈ I2, (x : ℤ) ≡ a (2 ^ (i + 1)) [ZMOD ((2 ^ (i + 1) : ℕ) : ℤ)]) ∨
        (∃ t ∈ Ip, (x : ℤ) ≡ a (2 ^ t * p) [ZMOD ((2 ^ t * p : ℕ) : ℤ)]) := by
      intro x _
      obtain ⟨d, hd, hx⟩ := ha x
      have hdM : d ∈ M := hN'.subset hd
      have hne : d ≠ m0 := by rintro rfl; exact hm0N hd
      rcases classify d hdM with ⟨i, hi, rfl⟩ | ⟨t, ht, rfl⟩
      · exact Or.inl ⟨i, mem_filter.2 ⟨mem_range.2 hi, hne⟩, hx⟩
      · exact Or.inr ⟨t, mem_filter.2 ⟨mem_range.2 (by omega), hne⟩, hx⟩
    obtain ⟨u, h1, h2⟩ := core q p hp hp2 a I2 Ip (filter_subset _ _)
      (fun t ht => by have := mem_range.1 (mem_filter.1 ht).1; omega) hcov
    have hG := G q
    have hS := S1 q u
    rcases classify m0 hm0M with ⟨k, hk, rfl⟩ | ⟨t0, ht0, rfl⟩
    · have eI2 : I2 = (range q).erase k := by
        ext i
        simp only [I2, mem_filter, mem_range, mem_erase]
        constructor
        · rintro ⟨hi, hne⟩
          refine ⟨fun h => hne (by rw [h]), hi⟩
        · rintro ⟨hne, hi⟩
          refine ⟨hi, fun h => hne ?_⟩
          have := Nat.pow_right_injective (le_refl 2) h
          omega
      have eIp : Ip = range (q + 1) := by
        apply filter_true_of_mem
        intro t _ h
        exact pow_ne p hp hp2 k t h.symm
      rw [eI2] at h1
      rw [eIp, hS] at h2
      have hk' : k ∈ range q := mem_range.2 hk
      have hsum := Finset.sum_erase_add (range q) (f := fun i => 2 ^ (q - 1 - i)) hk'
      have h2k : 1 ≤ 2 ^ (q - 1 - k) := Nat.one_le_two_pow
      have hu : 2 ≤ u := by omega
      rw [hpq] at h2
      nlinarith
    · have eI2 : I2 = range q := by
        apply filter_true_of_mem
        intro i _
        exact pow_ne p hp hp2 i t0
      have eIp : Ip = (range (q + 1)).erase t0 := by
        ext t
        simp only [Ip, mem_filter, mem_range, mem_erase]
        constructor
        · rintro ⟨ht, hne⟩
          exact ⟨fun h => hne (by rw [h]), ht⟩
        · rintro ⟨hne, ht⟩
          refine ⟨ht, fun h => hne ?_⟩
          have h' := Nat.eq_of_mul_eq_mul_right hp.pos h
          exact Nat.pow_right_injective (le_refl 2) h'
      rw [eI2] at h1
      rw [eIp] at h2
      have hu : 1 ≤ u := by omega
      have ht0' : t0 ∈ range (q + 1) := mem_range.2 (by omega)
      have hsum := Finset.sum_erase_add (range (q + 1))
        (f := fun t => if t = q then 1 else u) ht0'
      have hf : 1 ≤ (if t0 = q then 1 else u) := by split_ifs <;> omega
      try simp only at hsum
      rw [hS] at hsum
      rw [hpq] at h2
      nlinarith

end OMASun

theorem OMA.solution : type_of% @Erdos1189.erdos_1189.parts.iv := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (B + 3)
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  refine ⟨2 ^ (p - 1) * p, OMASun.sun p hp hodd, ?_⟩
  have : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  nlinarith
