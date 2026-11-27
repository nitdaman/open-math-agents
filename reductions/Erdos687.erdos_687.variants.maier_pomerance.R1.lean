import FormalConjectures.ErdosProblems.«687»

/-!
# Splitting the Maier–Pomerance bound for Jacobsthal's function

The conjecture is split into a stronger arithmetic estimate with a fixed power
of `log log`, and a purely analytic comparison showing that any fixed power of
`log log` is absorbed by an arbitrary fixed extra power of `log`.
-/

namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1

open Asymptotics Erdos687 Filter
open scoped Topology

/-- A stronger arithmetic estimate: `Y` is bounded by `x log² x (log log x)^C`
for some fixed nonnegative real exponent `C`. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) * Real.log x ^ (2 : ℝ) * Real.log (Real.log x) ^ C)

/-- Analytic comparison: any fixed power of `log log x` is eventually dominated
by an arbitrary fixed extra power of `log x`. -/
def H2 : Prop :=
  ∀ C ε : ℝ, 0 < ε →
    (fun x : ℕ ↦ (x : ℝ) * Real.log x ^ (2 : ℝ) * Real.log (Real.log x) ^ C)
      =O[atTop] (fun x : ℕ ↦ (x : ℝ) * Real.log x ^ (2 + ε))

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.variants.maier_pomerance := by
  rintro ⟨C, _, hY⟩ hcmp ε hε
  exact hY.trans (hcmp C ε hε)

end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1
