import FormalConjectures.Paper.PudlakFiniteDomainConjectures

/-! # Polynomial-time retractions and optimal proof systems -/
-- Credit: @steveDOTdigital
namespace OMA.R_PudlakFiniteDomain_sat_no_p_optimal_proof_system_variants_exists_of_P_eq_NP_R1
open ComplexityTheory PudlakFiniteDomain

-- On acceptance keep the input word, otherwise return a fixed word.
def H1 : Prop := ∀ (L : DecisionProblem) (fallback : List Bool), IsPolyTime L →
    IsPolyTime (fun w => if L w then w else fallback)

-- A polynomial-time retraction onto the language is an optimal proof system.
-- The competing proof system itself supplies the translation.
def H2 : Prop := ∀ (L : DecisionProblem) (r : List Bool → List Bool), IsPolyTime r →
    (∀ w, L (r w) = true) → (∀ w, L w = true → r w = w) → IsPOptimalProofSystem L r

theorem main : H1 → H2 → type_of% @PudlakFiniteDomain.sat_no_p_optimal_proof_system.variants.exists_of_P_eq_NP := by
  intro branch retract eq L complete nonemptyL
  obtain ⟨y,hy⟩ := nonemptyL
  have dec : L ∈ P := eq ▸ complete.mem
  let r := fun w => if L w then w else y
  refine ⟨r, retract L r (branch L y dec) ?_ ?_⟩
  · intro w
    by_cases h : L w = true
    · simpa [r,h] using h
    · simpa [r,h] using hy
  · intro w hw
    simp [r,hw]
end OMA.R_PudlakFiniteDomain_sat_no_p_optimal_proof_system_variants_exists_of_P_eq_NP_R1
