import FormalConjectures.ErdosProblems.«137»

-- Reduction Erdos137.erdos_137.R1 of Erdős Problem 137
-- Credit: @maxime-fleury
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos137_erdos_137_R1

/-- A powerful product of three consecutive positive integers. -/
def H1 : Prop := ∃ n : ℕ, (∏ x ∈ Finset.Ioc n (n + 3), x).Powerful

/-- A powerful product of four consecutive positive integers. -/
def H2 : Prop := ∃ n : ℕ, (∏ x ∈ Finset.Ioc n (n + 4), x).Powerful

theorem main : H1 → H2 → type_of% @Erdos137.erdos_137 := by
  intro h1 h2
  exact ⟨3, by norm_num, h1⟩

end OMA.R_Erdos137_erdos_137_R1
