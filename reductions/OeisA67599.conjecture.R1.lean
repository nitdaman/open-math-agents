import FormalConjectures.OEIS.«67599»
import Mathlib.Data.Nat.Digits.Lemmas

/-! # Fixed points from a prime in a decimal progression -/

-- Credit: @ArtemCherbaev
namespace OMA.R_OeisA67599_conjecture_R1

-- A prime in a sequence of exact integer quotients supplies the last factor.
def H1 : Prop :=
  ∃ t : ℕ, Nat.Prime ((7400 * 10 ^ (135 + 199 * t) + 1) / 2391)

-- The factorization consists of four sevens followed by the larger prime.
def H2 : Prop :=
  ∀ q : ℕ, 7 < q → q.Prime →
    OeisA67599.a (2401 * q) = 740 * 10 ^ (Nat.digits 10 q).length + 10 * q + 1

theorem main : H1 → H2 → type_of% @OeisA67599.conjecture := by
  rintro ⟨t, hprime⟩ hencode
  let k := 135 + 199 * t
  let b := (10 : ℕ) ^ k
  let q := (7400 * b + 1) / 2391
  have hperiod : (10 : ℕ) ^ 199 ≡ 1 [MOD 2391] := by decide
  have hbmod : b ≡ 10 ^ 135 [MOD 2391] := by
    change (10 : ℕ) ^ (135 + 199 * t) ≡ 10 ^ 135 [MOD 2391]
    rw [pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hperiod.pow t).mul_left ((10 : ℕ) ^ 135)
  have hbase : 7400 * (10 : ℕ) ^ 135 + 1 ≡ 0 [MOD 2391] := by decide
  have hdiv : 2391 ∣ 7400 * b + 1 := Nat.modEq_zero_iff_dvd.mp
    ((((Nat.ModEq.refl 7400).mul hbmod).add (Nat.ModEq.refl 1)).trans hbase)
  have heq : q * 2391 = 7400 * b + 1 := Nat.div_mul_cancel hdiv
  have hb : 10 ≤ b := by
    change 10 ≤ (10 : ℕ) ^ (135 + 199 * t)
    rw [pow_add]
    exact le_trans (by decide : 10 ≤ (10 : ℕ) ^ 135)
      (Nat.le_mul_of_pos_right _ (by positivity))
  have hl : k < (Nat.digits 10 q).length :=
    (Nat.lt_digits_length_iff (by decide) q).2 (show b ≤ q by omega)
  have hu : (Nat.digits 10 q).length ≤ k + 1 := by
    apply (Nat.digits_length_le_iff (by decide) q).2
    rw [pow_succ]
    change q < b * 10
    omega
  have hd : (Nat.digits 10 q).length = k + 1 := by omega
  refine ⟨2401 * q, by omega, ?_⟩
  rw [hencode q (by omega) hprime, hd, pow_succ]
  change 740 * (b * 10) + 10 * q + 1 = 2401 * q
  omega

end OMA.R_OeisA67599_conjecture_R1
