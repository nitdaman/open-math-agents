import OMAReductions.R_Erdos399_erdos_399_variants_sum_two_squares_R1

-- Step Erdos399.erdos_399.variants.sum_two_squares.R1.H1: hypothesis H1 of reduction Erdos399.erdos_399.variants.sum_two_squares.R1
-- Credit: @JamesSlash
-- H1 := ∀ n : ℕ, 7 ≤ n → n ≤ 100 →   ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n
--
-- Proof: the primes 7, 11, 19, 31, 43, 59 are all congruent to 3 mod 4, and the
-- half-open windows [7, 14), [11, 22), [19, 38), [31, 62), [43, 86), [59, 118)
-- cover every n with 7 ≤ n ≤ 100.

namespace OMA.Erdos399SumTwoSquaresH1

theorem window (n : ℕ) (h1 : 7 ≤ n) (h2 : n ≤ 100) :
    ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n := by
  rcases Nat.lt_or_ge n 11 with h | h
  · exact ⟨7, by norm_num, by norm_num, by omega, by omega⟩
  rcases Nat.lt_or_ge n 19 with h' | h'
  · exact ⟨11, by norm_num, by norm_num, by omega, by omega⟩
  rcases Nat.lt_or_ge n 31 with h'' | h''
  · exact ⟨19, by norm_num, by norm_num, by omega, by omega⟩
  rcases Nat.lt_or_ge n 43 with h''' | h'''
  · exact ⟨31, by norm_num, by norm_num, by omega, by omega⟩
  rcases Nat.lt_or_ge n 59 with h'''' | h''''
  · exact ⟨43, by norm_num, by norm_num, by omega, by omega⟩
  · exact ⟨59, by norm_num, by norm_num, by omega, by omega⟩

end OMA.Erdos399SumTwoSquaresH1

theorem OMA.solution : OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1.H1 := by
  intro n h1 h2
  exact OMA.Erdos399SumTwoSquaresH1.window n h1 h2
