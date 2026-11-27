import OMAReductions.R_OeisA245212_conjecture_R1

/-! A245212 has a positive gap on every odd product of two distinct prime powers.
For such n the gap is at least n times its divisor count divided by eight.
This continues the prime-power reduction in project PR 488 for Jaroslav Krizek’s OEIS conjecture.
The remaining odd cases are separated by whether twice the totient reaches n. -/

namespace OMA.R_OeisA245212_conjecture_R1_H1_R1

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The finite geometric sum at a prime bounded below by c + 1. -/
private lemma geom_bound (p c e : ℕ) (hp : c + 1 ≤ p) :
    c * (∑ j ∈ range (e + 1), p ^ j) ≤ (c + 1) * p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ]
    simp only [pow_succ p e]
    nlinarith only [ih, Nat.mul_le_mul_right (p^e) hp]

/-- The loss of one in the leading coefficient is important for small exponents. -/
private lemma weighted_bound (p c e : ℕ) (hp : c + 1 ≤ p) :
    c * (∑ j ∈ range (e + 1), p ^ j * (j + 1)) ≤ ((c + 1) * e + c) * p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hcoef : (c + 1) * e + c ≤ (e + 1) * p := by
      calc
        _ ≤ (e + 1) * (c + 1) := by nlinarith
        _ ≤ (e + 1) * p := Nat.mul_le_mul_left _ hp
    rw [sum_range_succ]
    simp only [pow_succ p e]
    nlinarith only [ih, Nat.mul_le_mul_right (p^e) hcoef]

private lemma moment_mul (u v : ℕ) (hc : u.Coprime v) :
    (∑ d ∈ (u*v).divisors, d * d.divisors.card) =
    (∑ d ∈ u.divisors, d * d.divisors.card) * (∑ d ∈ v.divisors, d * d.divisors.card) := by
  let F : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta
  have hf : F.IsMultiplicative :=
    (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
  have he (n : ℕ) : F n = ∑ d ∈ n.divisors, d * d.divisors.card := by
    change ((ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta) n = _
    rw [ArithmeticFunction.mul_zeta_apply]
    simp only [pmul_apply, id_apply, sigma_zero_apply]
  simpa only [he] using hf.map_mul_of_coprime hc

private lemma moment_at_power (p e : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^e).divisors, d * d.divisors.card) =
    ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [Nat.divisors_prime_pow hp, card_map, card_range]

private lemma sharp_bound (p q e f : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (he : 0 < e) (hf : 0 < f) :
    8 * ((∑ d ∈ (p^e*q^f).divisors, d*d.divisors.card) + σ 1 (p^e*q^f)) ≤
      15 * ((p^e*q^f) * (p^e*q^f).divisors.card) := by
  have hc : (p^e).Coprime (q^f) := (((Nat.coprime_primes hp hq).mpr hpq.ne).pow_left e).pow_right f
  rw [moment_mul _ _ hc, moment_at_power p e hp, moment_at_power q f hq,
      isMultiplicative_sigma.map_mul_of_coprime hc, hc.card_divisors_mul]
  simp only [Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hq, card_map, card_range,
    sigma_apply_prime_pow hp, sigma_apply_prime_pow hq, mul_one]
  have hw := Nat.mul_le_mul (weighted_bound p 2 e hp3) (weighted_bound q 4 f hq5)
  have hs := Nat.mul_le_mul (geom_bound p 2 e hp3) (geom_bound q 4 f hq5)
  have hcoef : (3*e+2)*(5*f+4)+15 ≤ 15*((e+1)*(f+1)) := by nlinarith
  nlinarith only [hw, hs, Nat.mul_le_mul_right (p^e*q^f) hcoef]

private lemma gap_of_bound (n : ℕ) (hn : n ≠ 0)
    (h : 8 * ((∑ d ∈ n.divisors, d*d.divisors.card) + σ 1 n) ≤ 15 * (n*n.divisors.card)) :
    (n : ℤ)*n.divisors.card ≤ 8 * (OeisA245212.a n - (σ 1 n : ℤ)) := by
  have hs : (∑ d ∈ n.divisors, d*d.divisors.card) =
      n*n.divisors.card + ∑ d ∈ n.properDivisors, d*d.divisors.card := by
    calc
      _ = ∑ d ∈ insert n n.properDivisors, d*d.divisors.card := by rw [Nat.insert_self_properDivisors hn]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  rw [hs] at h
  have hz : (8:ℤ) * (((n:ℤ) * n.divisors.card +
        ∑ d ∈ n.properDivisors, (d:ℤ) * d.divisors.card) + (σ 1 n : ℤ)) ≤
        15 * ((n:ℤ) * n.divisors.card) := by exact_mod_cast h
  unfold OeisA245212.a
  omega

/-- Remaining inputs for which twice the totient is at least n. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → ¬ IsPrimePow n → n ≤ 2 * n.totient →
    (¬ ∃ p q e f : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 3 ≤ p ∧ 5 ≤ q ∧
      0 < e ∧ 0 < f ∧ n = p^e*q^f) → OeisA245212.a n ≠ (σ 1 n : ℤ)

/-- Remaining inputs for which twice the totient is below n. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → ¬ IsPrimePow n → 2 * n.totient < n →
    (¬ ∃ p q e f : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 3 ≤ p ∧ 5 ≤ q ∧
      0 < e ∧ 0 < f ∧ n = p^e*q^f) → OeisA245212.a n ≠ (σ 1 n : ℤ)

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1.H1 := by
  intro smallRatio largeRatio n hn ho hpp
  by_cases rep : ∃ p q e f : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 3 ≤ p ∧ 5 ≤ q ∧
      0 < e ∧ 0 < f ∧ n = p^e*q^f
  · obtain ⟨p,q,e,f,hp,hq,hpq,hp3,hq5,he,hf,hnrep⟩ := rep
    have hb := sharp_bound p q e f hp hq hpq hp3 hq5 he hf
    rw [← hnrep] at hb
    have hgap := gap_of_bound n (by omega) hb
    have hcard : 0 < n.divisors.card := card_pos.mpr ⟨n, Nat.mem_divisors.mpr ⟨dvd_refl _, by omega⟩⟩
    have hpos : (0:ℤ) < (n:ℤ)*n.divisors.card := by exact_mod_cast Nat.mul_pos (by omega : 0 < n) hcard
    intro heq
    rw [heq, sub_self, mul_zero] at hgap
    omega
  · by_cases hs : n ≤ 2 * n.totient
    · exact smallRatio n hn ho hpp hs rep
    · exact largeRatio n hn ho hpp (by omega) rep

end OMA.R_OeisA245212_conjecture_R1_H1_R1
