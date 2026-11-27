import FormalConjectures.Paper.PartitionParity

-- Problem: Parities of partition numbers — kolberg
-- Upstream: formal-conjectures FormalConjectures/Paper/PartitionParity.lean:68 (declaration PartitionParity.kolberg)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries PowerSeries.WithPiTopology

namespace OMA

theorem not_pentagonal_between (k n : ℕ)
    (h1 : pentagonal (-(k : ℤ)) < n) (h2 : n < pentagonal ((k : ℤ) + 1)) :
    n ∉ Set.range pentagonal := by
  rintro ⟨j, rfl⟩
  have e1 := two_mul_natCast_pentagonal_neg (k : ℤ)
  have e2 := two_mul_natCast_pentagonal ((k : ℤ) + 1)
  have e3 := two_mul_natCast_pentagonal j
  have h1' : (pentagonal (-(k : ℤ)) : ℤ) < pentagonal j := by exact_mod_cast h1
  have h2' : (pentagonal j : ℤ) < pentagonal ((k : ℤ) + 1) := by exact_mod_cast h2
  have hk : (0 : ℤ) ≤ k := by positivity
  rcases le_or_gt j (-(k:ℤ) - 1) with h | h
  · nlinarith
  rcases le_or_gt j k with h' | h'
  · nlinarith
  · nlinarith

theorem zero_run (e : ℕ → ZMod 2) (he : ∀ n, e n = 0 ↔ n ∉ Set.range pentagonal)
    (d M : ℕ) : ∃ m ≥ M, ∀ i < d, e (m + i) = 0 := by
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, M ≤ k ∧ d ≤ k := ⟨M + d, by omega, by omega⟩
  have e1 := two_mul_natCast_pentagonal_neg (k : ℤ)
  have e2 := two_mul_natCast_pentagonal ((k : ℤ) + 1)
  have hk1' : (M : ℤ) ≤ k := by exact_mod_cast hk1
  have hk2' : (d : ℤ) ≤ k := by exact_mod_cast hk2
  have i1 : (M : ℤ) ≤ pentagonal (-(k : ℤ)) := by nlinarith
  have i2 : (pentagonal (-(k : ℤ)) : ℤ) + d < pentagonal ((k : ℤ) + 1) := by nlinarith
  refine ⟨pentagonal (-(k : ℤ)) + 1, by omega, fun i hi => ?_⟩
  rw [he]
  apply not_pentagonal_between k <;> omega

theorem exists_ne (e : ℕ → ZMod 2) (he : ∀ n, e n = 0 ↔ n ∉ Set.range pentagonal) (M : ℕ) :
    ∃ m ≥ M, e m ≠ 0 := by
  refine ⟨pentagonal ((M : ℤ) + 1), ?_, ?_⟩
  · have e2 := two_mul_natCast_pentagonal ((M : ℤ) + 1)
    have : (M : ℤ) ≤ pentagonal ((M : ℤ) + 1) := by nlinarith
    omega
  · rw [Ne, he]; simp

theorem core (e c : ℕ → ZMod 2) (N M : ℕ) (he : ∀ n, e n = 0 ↔ n ∉ Set.range pentagonal)
    (hc : c 0 = 1) (hrec : ∀ n ≥ M, ∑ i ∈ Finset.range (N + 1), c i * e (n - i) = 0) : False := by
  obtain ⟨m, hm, hrun⟩ := zero_run e he N (M)
  obtain ⟨m', hm', hne⟩ := exists_ne e he m
  have key : ∀ n, m ≤ n → e n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hlt : n < m + N
      · have := hrun (n - m) (by omega)
        rwa [show m + (n - m) = n by omega] at this
      · have h := hrec n (by omega)
        rw [Finset.sum_range_succ'] at h
        have : ∑ i ∈ Finset.range N, c (i + 1) * e (n - (i + 1)) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hi' := Finset.mem_range.mp hi
          rw [ih (n - (i + 1)) (by omega) (by omega), mul_zero]
        rw [this, hc] at h
        simpa using h
  exact hne (key m' hm')

theorem prod_eq_one :
    (PowerSeries.mk fun n => (Nat.partitionNumber n : ZMod 2)) * pentagonalSeries (ZMod 2) = 1 := by
  let _ : TopologicalSpace (ZMod 2) := ⊥
  have _ : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  have h1 : (PowerSeries.mk fun n => (Nat.partitionNumber n : ZMod 2)) =
      ∏' i, ∑' j : ℕ, (X ^ ((i + 1) * j) : (ZMod 2)⟦X⟧) := by
    have := Nat.Partition.powerSeriesMk_card_restricted_eq_tprod (ZMod 2) (fun _ => True)
    simpa [Nat.Partition.restricted, Nat.partitionNumber] using this
  have hm : Multipliable (fun i : ℕ => ∑' j : ℕ, (X ^ ((i + 1) * j) : (ZMod 2)⟦X⟧)) := by
    simpa using Nat.Partition.multipliable_powerSeriesMk_card_restricted (ZMod 2) (fun _ => True)
  rw [← tprod_one_sub_X_pow, h1, ← hm.tprod_mul (multipliable_one_sub_X_pow _)]
  have h2 : ∀ i : ℕ, (∑' j : ℕ, (X ^ ((i + 1) * j) : (ZMod 2)⟦X⟧)) * (1 - X ^ (i + 1)) = 1 := by
    intro i
    have := tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (R := ZMod 2)
      (f := (X ^ (i+1) : (ZMod 2)⟦X⟧)) (by simp)
    simpa [pow_mul] using this
  simp_rw [h2]
  exact tprod_one

theorem from_series (Q : (ZMod 2)⟦X⟧) (N M : ℕ) (hQ0 : coeff 0 Q = 1)
    (hQN : ∀ i, N < i → coeff i Q = 0) (hprod : ∀ n, M ≤ n → coeff n (Q * pentagonalSeries (ZMod 2)) = 0) :
    False := by
  refine core (fun n => coeff n (pentagonalSeries (ZMod 2))) (fun i => coeff i Q) N (max M N)
    (fun n => ?_) hQ0 (fun n hn => ?_)
  · simp
  · have h := hprod n (le_trans (le_max_left _ _) hn)
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    rw [← h]
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      have := le_trans (le_max_right _ _) hn
      omega
    · intro i hi hi'
      simp only [Finset.mem_range] at hi hi'
      rw [hQN i (by omega), zero_mul]

theorem kolberg_aux : {n : ℕ | Even (Nat.partitionNumber n)}.Infinite ∧
    {n : ℕ | Odd (Nat.partitionNumber n)}.Infinite := by
  have hP := prod_eq_one
  set P : (ZMod 2)⟦X⟧ := PowerSeries.mk fun n => (Nat.partitionNumber n : ZMod 2) with hPdef
  have hP0 : coeff 0 P = 1 := by simp [hPdef, Nat.partitionNumber_zero]
  constructor
  · intro hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    have hodd : ∀ n, N < n → coeff n P = 1 := by
      intro n hn
      have : n ∉ {n : ℕ | Even (Nat.partitionNumber n)} := fun h => absurd (hN h) (by omega)
      simp only [Set.mem_setOf_eq, ← Nat.not_odd_iff_even, not_not] at this
      simpa [hPdef] using (ZMod.natCast_eq_one_iff_odd).2 this
    refine from_series (P * (1 - X)) (N + 1) 2 (by rw [mul_sub, mul_one, map_sub, coeff_zero_mul_X, hP0]; simp) (fun i hi => ?_) (fun n hn => ?_)
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [mul_sub, mul_one, map_sub, coeff_succ_mul_X, hodd (j + 1) (by omega), hodd j]
      · simp
      · omega
    · rw [mul_assoc, mul_comm (1 - X), ← mul_assoc, hP, one_mul]
      rw [map_sub, coeff_one, coeff_X, if_neg (by omega), if_neg (by omega)]
      simp
  · intro hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    refine from_series P N 1 hP0 (fun i hi => ?_) (fun n hn => ?_)
    · have : i ∉ {n : ℕ | Odd (Nat.partitionNumber n)} := fun h => absurd (hN h) (by omega)
      simp only [Set.mem_setOf_eq, Nat.not_odd_iff_even] at this
      simpa [hPdef] using (ZMod.natCast_eq_zero_iff_even).2 this
    · rw [hP, coeff_one]
      simp
      omega

end OMA

theorem OMA.solution : type_of% @PartitionParity.kolberg := by
  exact OMA.kolberg_aux
