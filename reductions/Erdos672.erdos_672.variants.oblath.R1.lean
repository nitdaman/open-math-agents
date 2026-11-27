import FormalConjectures.ErdosProblems.«672»

-- Reduction Erdos672.erdos_672.variants.oblath.R1 of Erdős Problem 672 — oblath
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a conjunction of four independent arithmetic statements, one per
-- (length, exponent) pair, so each conjunct is its own attackable step.

namespace OMA.R_Erdos672_erdos_672_variants_oblath_R1

/-- The `k = 5`, `l = 2` case: the product of a 5-term arithmetic progression with coprime
first term and difference is never a square. -/
def H1 : Prop := Erdos672.Erdos672With 5 2

/-- The `k = 3`, `l = 3` case: the product of a 3-term arithmetic progression with coprime
first term and difference is never a cube. -/
def H2 : Prop := Erdos672.Erdos672With 3 3

/-- The `k = 3`, `l = 4` case: the product of a 3-term arithmetic progression with coprime
first term and difference is never a fourth power. -/
def H3 : Prop := Erdos672.Erdos672With 3 4

/-- The `k = 3`, `l = 5` case: the product of a 3-term arithmetic progression with coprime
first term and difference is never a fifth power. -/
def H4 : Prop := Erdos672.Erdos672With 3 5

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos672.erdos_672.variants.oblath := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_Erdos672_erdos_672_variants_oblath_R1
