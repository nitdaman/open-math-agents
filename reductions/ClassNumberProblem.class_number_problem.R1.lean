import FormalConjectures.Wikipedia.ClassNumberProblem

-- Reduction ClassNumberProblem.class_number_problem.R1
-- Credit: @GuillaumeBAUD-coder

namespace OMA.R_ClassNumberProblem_class_number_problem_R1

-- Minkowski's bound and the norm criterion for quadratic prime ideals.
def H1 : Prop :=
  ∀ d : ℤ, Squarefree d → d > 1 →
    (ClassNumberProblem.IsClassNumberOne d ↔
      let D := if d % 4 = 1 then d else 4 * d
      let s := D % 2
      ∀ q : ℕ, Nat.Prime q → 4 * (q : ℤ) ^ 2 ≤ D →
        (∃ t : ℤ, (q : ℤ) ∣ t ^ 2 - s * t + (s ^ 2 - D) / 4) →
        ∃ x y : ℤ, (x - s * y) % 2 = 0 ∧
          (x ^ 2 - D * y ^ 2 = 4 * (q : ℤ) ∨ x ^ 2 - D * y ^ 2 = -4 * (q : ℤ)))

-- Infinitude formulated using only congruences and integer norm equations.
def H2 : Prop :=
  { d : ℤ | Squarefree d ∧ d > 1 ∧
    (let D := if d % 4 = 1 then d else 4 * d
     let s := D % 2
     ∀ q : ℕ, Nat.Prime q → 4 * (q : ℤ) ^ 2 ≤ D →
       (∃ t : ℤ, (q : ℤ) ∣ t ^ 2 - s * t + (s ^ 2 - D) / 4) →
       ∃ x y : ℤ, (x - s * y) % 2 = 0 ∧
         (x ^ 2 - D * y ^ 2 = 4 * (q : ℤ) ∨ x ^ 2 - D * y ^ 2 = -4 * (q : ℤ))) }.Infinite

theorem main : H1 → H2 → type_of% @ClassNumberProblem.class_number_problem := by
  intro algebra arithmetic
  refine Set.Infinite.mono ?_ arithmetic
  intro d hd
  exact ⟨hd.1, hd.2.1, (algebra d hd.1 hd.2.1).2 hd.2.2⟩

end OMA.R_ClassNumberProblem_class_number_problem_R1
