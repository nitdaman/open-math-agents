import FormalConjectures.ErdosProblems.«399»

-- Reduction Erdos399.erdos_399.variants.sum_two_squares.R1 of Erdős Problem 399 — sum two squares
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Split: H1 is the prime-gap input for 7 ≤ n ≤ 100 (a finite check); H2 is the same input for n > 100.
-- The prime-gap input for every n ≥ 7 is then assembled from H1 and H2, and the target follows.

namespace OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1

open Nat

/-- Finite part: for 7 ≤ n ≤ 100 there is a prime q ≡ 3 (mod 4) with n/2 < q ≤ n. -/
def H1 : Prop := ∀ n : ℕ, 7 ≤ n → n ≤ 100 →
  ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n

/-- Tail part: for every n > 100 there is a prime q ≡ 3 (mod 4) with n/2 < q ≤ n. -/
def H2 : Prop := ∀ n : ℕ, 100 < n →
  ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n

/-- A prime q with q ≤ n < 2q has padicValNat q n! = 1. -/
theorem padic_factorial_of_gap {n q : ℕ} (hq : q.Prime) (h1 : q ≤ n) (h2 : n < 2 * q) :
    padicValNat q n ! = 1 := by
  haveI := Fact.mk hq
  have hlog : Nat.log q n < 2 := by
    apply Nat.log_lt_of_lt_pow
    · exact (Nat.pos_of_ne_zero (by omega)) |>.ne'
    · nlinarith [hq.two_le]
  rw [padicValNat_factorial (b := 2) hlog]
  simp [Finset.sum_Ico_succ_top, Nat.div_eq_of_lt_le]
  rw [Nat.div_eq_of_lt_le] <;> omega

/-- If every n ≥ 7 has such a prime, then n! = x^2 + y^2 forces n ≤ 6. -/
theorem le_six_of_gap
    (hH : ∀ n : ℕ, 7 ≤ n → ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n)
    {n x y : ℕ} (h : n ! = x ^ 2 + y ^ 2) : n ≤ 6 := by
  by_contra hn
  push_neg at hn
  obtain ⟨q, hq, hq4, hlt, hle⟩ := hH n hn
  have hmem : q ∈ (n !).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_factorial hq.pos hle, Nat.factorial_ne_zero n⟩
  have hev := (Nat.eq_sq_add_sq_iff.mp ⟨x, y, h⟩) q hmem hq4
  rw [padic_factorial_of_gap hq hle hlt] at hev
  exact absurd hev (by decide)

theorem main : H1 → H2 → type_of% @Erdos399.erdos_399.variants.sum_two_squares := by
  intro hH1 hH2
  have hH : ∀ n : ℕ, 7 ≤ n → ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n := by
    intro n hn
    by_cases hb : n ≤ 100
    · exact hH1 n hn hb
    · exact hH2 n (by omega)
  intro n x y hxy h
  have hn := le_six_of_gap hH h
  have hx : x ≤ 26 := by
    have : x ^ 2 ≤ 720 := by
      have : n ! ≤ 6 ! := Nat.factorial_le hn
      have h6 : (6 : ℕ) ! = 720 := by decide
      omega
    nlinarith
  have hy : y ≤ 26 := by
    have : y ^ 2 ≤ 720 := by
      have : n ! ≤ 6 ! := Nat.factorial_le hn
      have h6 : (6 : ℕ) ! = 720 := by decide
      omega
    nlinarith
  interval_cases n <;> norm_num [Nat.factorial] at h <;>
    interval_cases x <;> interval_cases y <;> omega

end OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1
