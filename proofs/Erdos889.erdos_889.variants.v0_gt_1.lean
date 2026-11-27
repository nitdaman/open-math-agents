import FormalConjectures.ErdosProblems.«889»

-- Problem: Erdős Problem 889 — v0 gt 1
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/889.lean:61 (declaration Erdos889.erdos_889.variants.v0_gt_1)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős Problem 889: `v₀ n > 1` outside eight exceptions

The statement is a theorem of Erdős and Selfridge (1967). This file gives a self-contained proof.

A prime `q` is counted by `v n k` exactly when `q ∣ n + k` and `q` divides none of
`n, …, n + k - 1`; this holds as soon as `q ∣ n + k` and `k < q`. So it suffices to find `k` such
that `n + k` has two distinct prime factors larger than `k`.

* If `n` has two distinct prime factors, take `k = 0`.
* If `n + 1` has two distinct prime factors, take `k = 1`.
* Otherwise `n` and `n + 1` are both prime powers, so one of them is a power of `2`. A short
  computation modulo `3`, `16` and `5` (in particular, the equation `2 ^ x + 1 = 3 ^ c` has no
  solution with `x ≥ 4`) shows that, outside the listed exceptions, `n + 2` is divisible by `3`
  and by another odd prime, so `k = 2` works.
-/

namespace OMA.E889

open Erdos889

/-- Two distinct primes larger than `k` that divide `n + k` are both counted by `v n k`. -/
lemma one_lt_v₀_of_two_primes (n k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hkp : k < p) (hkq : k < q) (hpd : p ∣ n + k) (hqd : q ∣ n + k) (hnk : n + k ≠ 0) :
    1 < v₀ n := by
  have key : ∀ r : ℕ, r.Prime → k < r → r ∣ n + k →
      r ∈ (n + k).primeFactors.filter (fun p => ∀ i ∈ Finset.range k, ¬ p ∣ n + i) := by
    intro r hr hkr hrd
    rw [Finset.mem_filter]
    refine ⟨Nat.mem_primeFactors.mpr ⟨hr, hrd, hnk⟩, ?_⟩
    intro i hi hdi
    have hik : i < k := Finset.mem_range.mp hi
    have hsplit : n + k = (n + i) + (k - i) := by omega
    rw [hsplit] at hrd
    have h1 : r ∣ k - i := (Nat.dvd_add_right hdi).mp hrd
    have h2 : r ≤ k - i := Nat.le_of_dvd (by omega) h1
    omega
  have hsub : ({p, q} : Finset ℕ) ⊆
      (n + k).primeFactors.filter (fun p => ∀ i ∈ Finset.range k, ¬ p ∣ n + i) := by
    intro r hr
    rw [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact key _ hp hkp hpd
    · exact key _ hq hkq hqd
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hpq] at hcard
  have h2 : 2 ≤ v n k := hcard
  have h3 : ((v n k : ℕ) : ℕ∞) ≤ v₀ n := le_iSup (fun k => ((v n k : ℕ) : ℕ∞)) k
  exact lt_of_lt_of_le (by exact_mod_cast h2) h3

/-- Powers of `3` modulo `16` and modulo `5`: the two residues determine each other. -/
lemma three_pow_mod (c : ℕ) :
    (3 ^ c % 16 = 1 ∧ 3 ^ c % 5 = 1) ∨ (3 ^ c % 16 = 3 ∧ 3 ^ c % 5 = 3) ∨
    (3 ^ c % 16 = 9 ∧ 3 ^ c % 5 = 4) ∨ (3 ^ c % 16 = 11 ∧ 3 ^ c % 5 = 2) := by
  induction c with
  | zero => left; norm_num
  | succ k ih =>
    have e : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; left; constructor <;> omega
    · right; right; left; constructor <;> omega
    · right; right; right; constructor <;> omega
    · left; constructor <;> omega

/-- Powers of `2` modulo `3`, according to the parity of the exponent. -/
lemma two_pow_mod_three (a : ℕ) :
    (a % 2 = 0 ∧ 2 ^ a % 3 = 1) ∨ (a % 2 = 1 ∧ 2 ^ a % 3 = 2) := by
  induction a with
  | zero => left; norm_num
  | succ k ih =>
    have e : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; constructor <;> omega
    · left; constructor <;> omega

lemma two_pow_mod_sixteen {x : ℕ} (hx : 4 ≤ x) : 2 ^ x % 16 = 0 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = 4 + y := ⟨x - 4, by omega⟩
  rw [pow_add]
  norm_num

/-- `2 ^ x + 1` is not a power of `3` when `x ≥ 4`: modulo `16` the exponent of `3` would be a
multiple of `4`, and then `5` would divide `2 ^ x`. -/
lemma two_pow_add_one_ne_three_pow (x c : ℕ) (hx : 4 ≤ x) : 2 ^ x + 1 ≠ 3 ^ c := by
  intro h
  have h16 := two_pow_mod_sixteen hx
  have h3 := three_pow_mod c
  have h5 : 5 ∣ 2 ^ x := Nat.dvd_of_mod_eq_zero (by omega)
  have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h5
  omega

/-- A positive integer that is not a power of `3` has a prime factor other than `3`. -/
lemma exists_prime_ne_three (m : ℕ) (hm : m ≠ 0) (h : ∀ c : ℕ, m ≠ 3 ^ c) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ r ∣ m := by
  by_contra hcon
  refine h _ (Nat.eq_prime_pow_of_unique_prime_dvd hm ?_)
  intro d hd hdm
  by_contra hne
  exact hcon ⟨d, hd, hne, hdm⟩

theorem main (n : ℕ) (hn : n ∉ ({0, 1, 2, 3, 4, 7, 8, 16} : Finset ℕ)) : 1 < v₀ n := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  obtain ⟨h0, h1, h2, h3, h4, h7, h8, h16⟩ := hn
  -- `k = 0`: two distinct prime factors of `n`.
  by_cases hA : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n
  · obtain ⟨p, q, hp, hq, hpq, hpd, hqd⟩ := hA
    exact one_lt_v₀_of_two_primes n 0 p q hp hq hpq hp.pos hq.pos hpd hqd h0
  -- `k = 1`: two distinct prime factors of `n + 1`.
  by_cases hB : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n + 1 ∧ q ∣ n + 1
  · obtain ⟨p, q, hp, hq, hpq, hpd, hqd⟩ := hB
    exact one_lt_v₀_of_two_primes n 1 p q hp hq hpq hp.one_lt hq.one_lt hpd hqd (by omega)
  -- `k = 2`: it suffices that `3` and another odd prime divide `n + 2`.
  suffices h : 3 ∣ n + 2 ∧ ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ r ≠ 2 ∧ r ∣ n + 2 by
    obtain ⟨h3d, r, hr, hr3, hr2, hrd⟩ := h
    have hr2' : 2 < r := lt_of_le_of_ne hr.two_le (Ne.symm hr2)
    exact one_lt_v₀_of_two_primes n 2 3 r Nat.prime_three hr (Ne.symm hr3) (by norm_num) hr2'
      h3d hrd (by omega)
  -- From now on `n` and `n + 1` each have at most one prime factor.
  have uA : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → p = q := by
    intro p q hp hq hpd hqd
    by_contra hne
    exact hA ⟨p, q, hp, hq, hne, hpd, hqd⟩
  have uB : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n + 1 → q ∣ n + 1 → p = q := by
    intro p q hp hq hpd hqd
    by_contra hne
    exact hB ⟨p, q, hp, hq, hne, hpd, hqd⟩
  rcases Nat.even_or_odd n with hev | hodd
  · -- `n` is even, hence a power of `2`.
    have h2n : 2 ∣ n := hev.two_dvd
    obtain ⟨a, ha⟩ : ∃ a, n = 2 ^ a :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd h0
        (fun {d} hd hdn => uA d 2 hd Nat.prime_two hdn h2n)⟩
    have ha5 : 5 ≤ a := by
      by_contra hlt
      have hlt' : a < 5 := by omega
      interval_cases a <;> omega
    rcases two_pow_mod_three a with ⟨hpar, hmod⟩ | ⟨hpar, hmod⟩
    · -- `a` is even: `n + 2 = 2 * (2 ^ (a - 1) + 1)` with `a - 1 ≥ 5` odd.
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have e : 2 ^ (b + 1) = 2 ^ b * 2 := pow_succ 2 b
      have hb := two_pow_mod_three b
      refine ⟨Nat.dvd_of_mod_eq_zero (by omega), ?_⟩
      obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_ne_three (2 ^ b + 1) (by omega)
        (fun c => two_pow_add_one_ne_three_pow b c (by omega))
      refine ⟨r, hr, hr3, ?_, ?_⟩
      · rintro rfl
        have h2b : 2 ∣ 2 ^ b := dvd_pow_self 2 (by omega)
        omega
      · have hn2 : n + 2 = 2 * (2 ^ b + 1) := by omega
        rw [hn2]
        exact Dvd.dvd.mul_left hrd 2
    · -- `a` is odd: `3 ∣ n + 1`, so `n + 1 = 2 ^ a + 1` is a power of `3`, which is impossible.
      exfalso
      have h3n : 3 ∣ n + 1 := Nat.dvd_of_mod_eq_zero (by omega)
      have hpow : n + 1 = 3 ^ (n + 1).primeFactorsList.length :=
        Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
          (fun {d} hd hdn => uB d 3 hd Nat.prime_three hdn h3n)
      exact two_pow_add_one_ne_three_pow a (n + 1).primeFactorsList.length (by omega) (by omega)
  · -- `n` is odd, so `n + 1` is even, hence a power of `2`.
    obtain ⟨t, ht⟩ := hodd
    have h2n : 2 ∣ n + 1 := ⟨t + 1, by omega⟩
    obtain ⟨a, ha⟩ : ∃ a, n + 1 = 2 ^ a :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
        (fun {d} hd hdn => uB d 2 hd Nat.prime_two hdn h2n)⟩
    have ha4 : 4 ≤ a := by
      by_contra hlt
      have hlt' : a < 4 := by omega
      interval_cases a <;> omega
    have h16' := two_pow_mod_sixteen ha4
    rcases two_pow_mod_three a with ⟨hpar, hmod⟩ | ⟨hpar, hmod⟩
    · -- `a` is even: `3 ∣ n`, so `n = 2 ^ a - 1` is a power of `3`, impossible modulo `16`.
      exfalso
      have h3n : 3 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
      have hpow : n = 3 ^ n.primeFactorsList.length :=
        Nat.eq_prime_pow_of_unique_prime_dvd h0
          (fun {d} hd hdn => uA d 3 hd Nat.prime_three hdn h3n)
      have h3c := three_pow_mod n.primeFactorsList.length
      omega
    · -- `a` is odd: `n + 2 = 2 ^ a + 1` is divisible by `3` and is not a power of `3`.
      refine ⟨Nat.dvd_of_mod_eq_zero (by omega), ?_⟩
      obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_ne_three (n + 2) (by omega)
        (fun c hc => two_pow_add_one_ne_three_pow a c ha4 (by omega))
      refine ⟨r, hr, hr3, ?_, hrd⟩
      rintro rfl
      omega

end OMA.E889

theorem OMA.solution : type_of% @Erdos889.erdos_889.variants.v0_gt_1 :=
  OMA.E889.main
