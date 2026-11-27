import FormalConjectures.Wikipedia.RegularPrimes

-- Reduction RegularPrimes.not_isRegularPrime_37.R1 of Infinite Regular Primes — not isRegularPrime 37
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Two independent inputs to the irregularity of 37

`37` is the smallest irregular prime, and the standard proof has exactly two inputs of a very
different nature.

* `H1` is an arithmetic computation: `37` divides the numerator of `B 32`.  This is the concrete
  "irregular pair" `(37, 32)`, and `B 32 = -7709321041217 / 510` with
  `7709321041217 = 37 ^ 2 * 683 * 30539`.
* `H2` is Kummer's criterion for this single prime: irregularity of `37` is *equivalent* to
  divisibility of the numerator of one of `B 2, B 4, …, B 34`.  This is the deep input (it relates
  the `p`-part of the class number of `ℚ(ζ 37)` to Bernoulli numbers) and it is not in Mathlib.

Given both, irregularity of `37` is immediate: `32` is one of the even indices below `37 - 3`, so
Kummer's criterion together with `H1` rules out regularity.
-/

namespace OMA.R_RegularPrimes_not_isRegularPrime_37_R1

/-- `37` divides the numerator of the Bernoulli number `B 32`. -/
def H1 : Prop :=
  (37 : ℤ) ∣ (bernoulli' 32).num

/-- Kummer's criterion at `p = 37`: `37` is regular exactly when it divides the numerator of none
of `B 2, B 4, …, B 34`. -/
def H2 : Prop :=
  @RegularPrimes.IsRegularPrime 37 (by decide) ↔
    ∀ k ∈ Finset.Icc 2 (37 - 3), Even k → ¬ (37 : ℤ) ∣ (bernoulli' k).num

theorem main : H1 → H2 → type_of% @RegularPrimes.not_isRegularPrime_37 := by
  intro h1 h2 hreg
  exact h2.mp hreg 32 (by norm_num) ⟨16, rfl⟩ h1

end OMA.R_RegularPrimes_not_isRegularPrime_37_R1
