import FormalConjectures.Wikipedia.RegularPrimes

-- Reduction RegularPrimes.isRegularPrime_iff_Bernoulli.R1 of Infinite Regular Primes — isRegularPrime iff Bernoulli
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The two halves of Kummer's criterion

Kummer's criterion identifies regularity of `p` (the non-divisibility of the class number of
`ℚ(ζ_p)`) with the non-divisibility of the numerators of `B 2, B 4, …, B (p - 3)`.  The two
implications are proved by completely different means, and it is worth separating them.

* `H1` (regularity obstructs Bernoulli divisibility) is the half that goes through the analytic
  class number formula: an irregular index `k` is a zero of the `p`-adic `L`-function, which forces
  `p` into the class number.  This is the direction that produces *irregular* primes.
* `H2` (Bernoulli divisibility obstructs regularity) is the half that converts a concrete
  divisibility `p ∣ (B k).num` into a statement about the class group, via Kummer's construction of
  an unramified cyclic extension and the reflection theorem for the `p`-part of the class group.

Neither direction is in Mathlib.  Together they are the statement, and the assembly is formal.
-/

namespace OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R1

open scoped NumberField

/-- A regular prime `p` divides the numerator of none of `B 2, B 4, …, B (p - 3)`. -/
def H1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], RegularPrimes.IsRegularPrime p →
    ∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num

/-- If `p` divides the numerator of none of `B 2, B 4, …, B (p - 3)`, then `p` is regular. -/
def H2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    (∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num) →
    RegularPrimes.IsRegularPrime p

theorem main : H1 → H2 → type_of% @RegularPrimes.isRegularPrime_iff_Bernoulli := by
  intro h1 h2 p hp
  apply Iff.intro
  · exact @h1 p hp
  · exact @h2 p hp

end OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R1
