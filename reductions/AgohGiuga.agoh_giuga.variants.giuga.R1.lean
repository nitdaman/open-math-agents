import FormalConjectures.Wikipedia.AgohGiuga

/-!
# Reduction of the Agoh-Giuga conjecture (Giuga's formulation)

Reduction `AgohGiuga.agoh_giuga.variants.giuga.R1` by `@hackoria`.
Splits Giuga's conjecture (1950) along Giuga's own characterization:
- `main` proves the prime direction directly via Fermat's Little Theorem and applies Korselt's criterion.
- `H1` (known, Giuga 1950): every strong Giuga number is a Carmichael number.
- `H2` (known, Giuga 1950): every strong Giuga number satisfies `p ∣ (n / p - 1)` for all prime `p ∣ n`.
- `H3` (open core): no composite squarefree integer satisfies both Korselt's and Giuga's divisibility conditions.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1

open AgohGiuga

-- Giuga (1950): every strong Giuga number is a Carmichael number.
def H1 : Prop :=
  ∀ n : ℕ, IsStrongGiuga n → IsCarmichael n

-- Giuga (1950): every strong Giuga number satisfies p | (n / p - 1) for every prime factor p.
def H2 : Prop :=
  ∀ n : ℕ, IsStrongGiuga n → ∀ p ∈ n.primeFactors, p ∣ (n / p - 1)

-- Open arithmetic core: no composite squarefree integer simultaneously satisfies
-- Korselt's condition (p - 1) | (n - 1) and Giuga's condition p | (n / p - 1) for all prime factors p.
def H3 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n →
    (∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1)) →
    (∀ p ∈ n.primeFactors, p ∣ (n / p - 1)) → False

lemma prime_dvd_sum_pow (p : ℕ) (hp : p.Prime) :
    p ∣ 1 + ∑ i ∈ Finset.Ioo 0 p, i ^ (p - 1 : ℕ) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
  have hsum : ∑ i ∈ Finset.Ioo 0 p, ((i ^ (p - 1 : ℕ) : ℕ) : ZMod p) =
      ∑ _i ∈ Finset.Ioo 0 p, (1 : ZMod p) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.cast_pow]
    rw [Finset.mem_Ioo] at hi
    have hi0 : (i : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd hi.1 h) (not_le_of_gt hi.2)
    exact ZMod.pow_card_sub_one_eq_one hi0
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioo, Nat.sub_zero]
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hp.one_le, ZMod.natCast_self]

theorem main : H1 → H2 → H3 → type_of% @AgohGiuga.agoh_giuga.variants.giuga := by
  intro h1 h2 h3 p hp2
  constructor
  · exact prime_dvd_sum_pow p
  · intro hdvd
    by_contra hnp
    have hcomp : p.Composite := by
      dsimp [Nat.Composite]
      exact ⟨by omega, hnp⟩
    have hsg : IsStrongGiuga p := ⟨hcomp, hdvd⟩
    have hcarm : IsCarmichael p := h1 p hsg
    have ⟨hsqf, hkorselt⟩ := (AgohGiuga.korselts_criterion p hcomp).mp hcarm
    have hgiuga := h2 p hsg
    refine h3 p hcomp hsqf ?_ hgiuga
    intro q hq
    have ⟨hq_prime, hq_dvd, _⟩ := Nat.mem_primeFactors.mp hq
    exact hkorselt q hq_prime hq_dvd

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1
