import FormalConjectures.OEIS.«83753»

namespace OMA.R_OeisA83753_conjecture_R1

open OeisA83753

-- Odd-length palindromes at prime exponents.
def H1 : Prop := ∀ x p : ℕ, 1 < x → p.Prime → 5 ≤ p →
  Odd (Nat.digits 10 (x ^ p)).length → ¬ IsDecimalPalindrome (x ^ p)

-- The three minimal composite exponents, for odd digit lengths.
def H2 : Prop := ∀ x e : ℕ, 1 < x → (e = 6 ∨ e = 8 ∨ e = 9) →
  Odd (Nat.digits 10 (x ^ e)).length → ¬ IsDecimalPalindrome (x ^ e)

-- For even digit lengths it suffices to study roots divisible by eleven.
def H3 : Prop := ∀ x e : ℕ, 1 < x → 11 ∣ x →
  ((e.Prime ∧ 5 ≤ e) ∨ e = 6 ∨ e = 8 ∨ e = 9) →
  Even (Nat.digits 10 (x ^ e)).length → ¬ IsDecimalPalindrome (x ^ e)

lemma exponent_divisor (k : ℕ) (hk : 5 ≤ k) :
    ∃ e, e ∣ k ∧ ((Nat.Prime e ∧ 5 ≤ e) ∨ e = 6 ∨ e = 8 ∨ e = 9) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hp : k.Prime
    · exact ⟨k, dvd_refl _, Or.inl ⟨hp, hk⟩⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hp
    by_cases h₁ : 5 ≤ a
    · obtain ⟨e, hd, he⟩ := ih a ha h₁
      exact ⟨e, dvd_mul_of_dvd_left hd _, he⟩
    by_cases h₂ : 5 ≤ b
    · obtain ⟨e, hd, he⟩ := ih b hb h₂
      exact ⟨e, dvd_mul_of_dvd_right hd _, he⟩
    have : a ≤ 4 := by omega
    have : b ≤ 4 := by omega
    interval_cases a <;> interval_cases b <;> norm_num at * <;>
      first | exact ⟨6, by decide, Or.inr (Or.inl rfl)⟩
            | exact ⟨8, by decide, Or.inr (Or.inr (Or.inl rfl))⟩
            | exact ⟨9, by decide, Or.inr (Or.inr (Or.inr rfl))⟩

theorem main : H1 → H2 → H3 → type_of% @OeisA83753.conjecture := by
  intro h₁ h₂ h₃ m k hm hpal hk
  rintro ⟨x, rfl⟩
  obtain ⟨e, ⟨q, rfl⟩, he⟩ := exponent_divisor k hk
  rw [Nat.mul_comm e q, pow_mul] at hm hpal
  let y := x ^ q
  change IsDecimalPalindrome (y ^ e) at hpal
  have hy : 1 < y := by
    by_contra! h
    exact (not_le_of_gt hm) (by simpa using (Nat.pow_le_pow_left h e))
  rcases Nat.even_or_odd (Nat.digits 10 (y ^ e)).length with hl | hl
  · have hd := Nat.eleven_dvd_of_palindrome (List.Palindrome.of_reverse_eq hpal.symm) hl
    exact h₃ y e hy ((show Nat.Prime 11 by decide).dvd_of_dvd_pow hd) he hl hpal
  · rcases he with ⟨hp, hge⟩ | hc
    · exact h₁ y e hy hp hge hl hpal
    · exact h₂ y e hy hc hl hpal

end OMA.R_OeisA83753_conjecture_R1
