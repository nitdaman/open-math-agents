import FormalConjectures.ErdosProblems.«891»

-- Problem: Erdős Problem 891 — weisenberg
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/891.lean:79 (declaration Erdos891.erdos_891.variants.weisenberg)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Proof (Weisenberg's observation, as in the upstream docstring). Write P = p_1 ⋯ p_k for the
product of the first k primes and L = (P - 1)!, so that every 1 ≤ t ≤ P - 1 divides L.

* Apply Dickson's conjecture (a hypothesis here) to the linear forms (L / t) x + 1 for
  1 ≤ t ≤ P - 1. They are irreducible of degree one with positive leading coefficient, and
  they all take the value 1 at x = 0, so no prime divides all their values. Hence there are
  infinitely many n' for which every (L / t) n' + 1 is prime.
* For such n' put n = L n' + 1. Every m with n ≤ m < n + P - 1 is m = L n' + t with
  1 ≤ t ≤ P - 1, and
      L n' + t = t * ((L / t) n' + 1),
  a number below P times a prime.
* A positive integer below P has fewer than k distinct prime factors, because a product of k
  distinct primes is at least the product of the first k primes. So ω(m) ≤ (k - 1) + 1 = k.
* The map n' ↦ L n' + 1 is injective, so this gives infinitely many n.
-/

open Polynomial

namespace OMAAux

/-- `ω n` is the number of distinct prime factors of `n`. -/
lemma omega_eq_card (n : ℕ) :
    ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- If all `r + 1` elements of a set of primes are at most `M`, then the `r`-th prime
(counting from zero) is at most `M`. -/
lemma nth_prime_lt_succ (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (r : ℕ) (hr : T.card = r + 1)
    (M : ℕ) (hM : ∀ q ∈ T, q ≤ M) : Nat.nth Nat.Prime r < M + 1 := by
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range]
  have hsub : T ⊆ (Finset.range (M + 1)).filter Nat.Prime := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hM q hq), hT q hq⟩
  have hle := Finset.card_le_card hsub
  exact lt_of_lt_of_le (by omega : r < T.card) hle

/-- A product of `r` distinct primes is at least the product of the first `r` primes. -/
lemma prod_nth_prime_le (r : ℕ) : ∀ T : Finset ℕ, (∀ q ∈ T, q.Prime) → T.card = r →
    ∏ i ∈ Finset.range r, Nat.nth Nat.Prime i ≤ ∏ q ∈ T, q := by
  induction r with
  | zero =>
    intro T _ hT
    simp [Finset.card_eq_zero.mp hT]
  | succ r ih =>
    intro T hT hcard
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    have hMmem : T.max' hne ∈ T := Finset.max'_mem T hne
    have h1 : Nat.nth Nat.Prime r ≤ T.max' hne := by
      have h := nth_prime_lt_succ T hT r hcard (T.max' hne) (fun q hq => Finset.le_max' T q hq)
      omega
    have h2 := ih (T.erase (T.max' hne)) (fun q hq => hT q (Finset.mem_of_mem_erase hq))
      (by rw [Finset.card_erase_of_mem hMmem, hcard]; rfl)
    rw [Finset.prod_range_succ, ← Finset.prod_erase_mul T (fun q => q) hMmem]
    exact Nat.mul_le_mul h2 h1

/-- A positive integer below the product of the first `k` primes has fewer than `k` distinct
prime factors. -/
lemma card_primeFactors_lt (k t : ℕ) (ht0 : t ≠ 0)
    (ht : t < ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) : t.primeFactors.card < k := by
  by_contra hcon
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_lt hcon)
  have h1 := prod_nth_prime_le k T (fun q hq => Nat.prime_of_mem_primeFactors (hTsub hq)) hTcard
  have h2 : ∏ q ∈ T, q ≤ ∏ q ∈ t.primeFactors, q :=
    Finset.prod_le_prod_of_subset_of_one_le' hTsub
      (fun q hq _ => (Nat.prime_of_mem_primeFactors hq).one_le)
  have h3 : ∏ q ∈ t.primeFactors, q ≤ t :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) (Nat.prod_primeFactors_dvd t)
  omega

/-- A linear form `a x + 1` with `a > 0` is irreducible over the integers. -/
lemma linear_irreducible (a : ℤ) (ha : 0 < a) : Irreducible (C a * X + C 1 : ℤ[X]) := by
  have hprim : (C a * X + C 1 : ℤ[X]).IsPrimitive := by
    rw [isPrimitive_iff_isUnit_of_C_dvd]
    intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have h0 := hr 0
    simp at h0
    exact isUnit_of_dvd_one h0
  rw [IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim]
  apply irreducible_of_degree_eq_one
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  exact degree_linear (by simpa using ha.ne')

/-- The core argument, with the product of the first `k` primes abstracted to any `P` below
which every positive integer has fewer than `k` distinct prime factors. -/
lemma infinite_of_dickson (k P : ℕ)
    (hP : ∀ t : ℕ, t ≠ 0 → t < P → t.primeFactors.card < k)
    (hd : ∀ fs : Finset ℤ[X], (∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) →
      SchinzelCondition fs → Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}) :
    {n : ℕ | ∀ m ∈ Finset.Ico n (n + P - 1),
      ArithmeticFunction.cardDistinctFactors m ≤ k}.Infinite := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (P - 1).factorial := ⟨_, rfl⟩
  have hLpos : 0 < L := hL ▸ Nat.factorial_pos _
  have hdiv : ∀ t : ℕ, 1 ≤ t → t ≤ P - 1 → t ∣ L := fun t h1 h2 =>
    hL ▸ Nat.dvd_factorial (by omega) h2
  have hquot : ∀ t : ℕ, 1 ≤ t → t ≤ P - 1 → 0 < L / t := fun t h1 h2 =>
    Nat.div_pos (Nat.le_of_dvd hLpos (hdiv t h1 h2)) (by omega)
  -- the linear forms `(L / t) x + 1`, `1 ≤ t ≤ P - 1`
  obtain ⟨fs, hfs⟩ : ∃ fs : Finset ℤ[X], fs = (Finset.Icc 1 (P - 1)).image
      (fun t : ℕ => (C ((L / t : ℕ) : ℤ) * X + C 1 : ℤ[X])) := ⟨_, rfl⟩
  have hmem : ∀ f ∈ fs, ∃ t : ℕ, 1 ≤ t ∧ t ≤ P - 1 ∧ f = C ((L / t : ℕ) : ℤ) * X + C 1 := by
    intro f hf
    rw [hfs] at hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    rw [Finset.mem_Icc] at ht
    exact ⟨t, ht.1, ht.2, rfl⟩
  have hmem' : ∀ t : ℕ, 1 ≤ t → t ≤ P - 1 → (C ((L / t : ℕ) : ℤ) * X + C 1 : ℤ[X]) ∈ fs := by
    intro t h1 h2
    rw [hfs]
    exact Finset.mem_image.mpr ⟨t, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩
  have hcond1 : ∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f := by
    intro f hf
    obtain ⟨t, h1, h2, rfl⟩ := hmem f hf
    have hpos : (0 : ℤ) < ((L / t : ℕ) : ℤ) := by exact_mod_cast hquot t h1 h2
    have hdeg : (C ((L / t : ℕ) : ℤ) * X + C 1 : ℤ[X]).degree = 1 := degree_linear hpos.ne'
    refine ⟨hdeg, ?_⟩
    unfold BunyakovskyCondition
    refine ⟨by rw [hdeg], linear_irreducible _ hpos, ?_⟩
    rw [leadingCoeff_linear hpos.ne']
    exact hpos
  have hcond2 : SchinzelCondition fs := by
    intro p hp
    refine ⟨0, ?_⟩
    intro f hf
    obtain ⟨t, -, -, rfl⟩ := hmem f hf
    simp only [Nat.cast_zero, eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add]
    intro hdvd
    have h1 : p ∣ 1 := by exact_mod_cast hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hinf := Set.infinite_coe_iff.mp (hd fs hcond1 hcond2)
  -- transport along the injective map `n' ↦ L n' + 1`
  refine Set.infinite_of_injOn_mapsTo (f := fun n' : ℕ => L * n' + 1) ?_ ?_ hinf
  · intro a _ b _ hab
    have hab' : L * a + 1 = L * b + 1 := hab
    exact Nat.eq_of_mul_eq_mul_left hLpos (by omega)
  · intro n' hn'
    show ∀ m ∈ Finset.Ico (L * n' + 1) (L * n' + 1 + P - 1),
      ArithmeticFunction.cardDistinctFactors m ≤ k
    intro m hm
    rw [Finset.mem_Ico] at hm
    obtain ⟨t, ht1, ht2, rfl⟩ : ∃ t : ℕ, 1 ≤ t ∧ t ≤ P - 1 ∧ m = L * n' + t :=
      ⟨m - L * n', by omega, by omega, by omega⟩
    have hprime : (L / t * n' + 1).Prime := by
      have h := hn' _ (hmem' t ht1 ht2)
      simp only [eval_add, eval_mul, eval_C, eval_X] at h
      have hcast : ((L / t : ℕ) : ℤ) * (n' : ℤ) + 1 = ((L / t * n' + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hcast, Int.natAbs_natCast] at h
      exact h
    have hfact : L * n' + t = t * (L / t * n' + 1) := by
      have hcancel := Nat.mul_div_cancel' (hdiv t ht1 ht2)
      calc L * n' + t = t * (L / t) * n' + t := by rw [hcancel]
        _ = t * (L / t * n' + 1) := by ring
    rw [omega_eq_card, hfact, Nat.primeFactors_mul (by omega) hprime.ne_zero]
    have hc1 : t.primeFactors.card < k := hP t (by omega) (by omega)
    have hc2 : (L / t * n' + 1).primeFactors.card = 1 := by
      rw [hprime.primeFactors, Finset.card_singleton]
    have hc3 := Finset.card_union_le t.primeFactors (L / t * n' + 1).primeFactors
    omega

end OMAAux

theorem OMA.solution : type_of% @Erdos891.erdos_891.variants.weisenberg := by
  intro k _ hdickson
  rw [Nat.frequently_atTop_iff_infinite]
  exact OMAAux.infinite_of_dickson k _
    (fun t ht0 ht => OMAAux.card_primeFactors_lt k t ht0 ht) hdickson
