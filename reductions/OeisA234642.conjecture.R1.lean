import FormalConjectures.OEIS.«234642»

namespace OMA.R_OeisA234642_conjecture_R1

open OeisA234642

-- Odd remainders for the ordinary totient modulus.
def H1 : Prop := ∀ m : ℕ, Odd m → ∃ u : ℕ, Odd u ∧ ModTotientEq m u

-- Odd remainders for the half-totient modulus on odd inputs.
def H2 : Prop := ∀ m : ℕ, Odd m →
  ∃ u : ℕ, Odd u ∧ 2 < u ∧ u % (u.totient / 2) = m

lemma even_witness (h : H2) (m : ℕ) (hm : 0 < m) :
    ∃ x : ℕ, Even x ∧ ModTotientEq (2 * m) x := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.even_or_odd m with he | ho
    · obtain ⟨k, rfl⟩ := he
      obtain ⟨x, hx, hp, hr⟩ := ih k (by omega) (by omega)
      refine ⟨2*x, even_two_mul _, ?_⟩
      unfold ModTotientEq
      rw [Nat.totient_two_mul_of_even hx, Nat.mul_mod_mul_left, hr]
      constructor <;> omega
    · obtain ⟨u, hu, hlarge, hr⟩ := h m ho
      have he := (Nat.totient_even hlarge).two_dvd
      have heq : u.totient = 2 * (u.totient / 2) := by omega
      refine ⟨2*u, even_two_mul _, ?_⟩
      unfold ModTotientEq
      rw [Nat.totient_two_mul_of_odd hu]
      refine ⟨Nat.totient_pos.mpr (by omega), ?_⟩
      conv_lhs => rw [heq, Nat.mul_mod_mul_left, hr]

theorem main : H1 → H2 → type_of% @OeisA234642.conjecture := by
  intro h1 h2 n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a_0]
  have hex : ∃ x, ModTotientEq n x := by
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨k, rfl⟩ := he
      obtain ⟨x, _, hx⟩ := even_witness h2 k (by omega)
      exact ⟨x, by simpa [two_mul] using hx⟩
    · obtain ⟨x, _, hx⟩ := h1 n ho
      exact ⟨x, hx⟩
  exact Nat.totient_pos.mp (Nat.sInf_mem hex).1

end OMA.R_OeisA234642_conjecture_R1
