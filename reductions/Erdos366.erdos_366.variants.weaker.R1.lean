import FormalConjectures.ErdosProblems.«366»

-- Reduction Erdos366.erdos_366.variants.weaker.R1 of Erdős Problem 366 — weaker
-- Credit: @maxime-fleury
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos366_erdos_366_variants_weaker_R1

/-- A pair of consecutive `3`-full integers, the first one bounded by `100000`:
this is a finite search that can be settled by computation. -/
def H1 : Prop := ∃ n : ℕ, 0 < n ∧ n ≤ 100000 ∧ Nat.Full 3 n ∧ Nat.Full 3 (n + 1)

/-- A pair of consecutive `3`-full integers beyond `100000`: the genuinely
asymptotic part of the question. -/
def H2 : Prop := ∃ n : ℕ, 100000 < n ∧ Nat.Full 3 n ∧ Nat.Full 3 (n + 1)

theorem main : H1 → H2 → type_of% @Erdos366.erdos_366.variants.weaker := by
  rintro ⟨n, hn0, -, hf⟩ _
  exact ⟨n, hn0, hf⟩

end OMA.R_Erdos366_erdos_366_variants_weaker_R1
