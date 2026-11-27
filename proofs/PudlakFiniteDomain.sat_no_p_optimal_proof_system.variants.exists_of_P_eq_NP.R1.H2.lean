import OMAReductions.R_PudlakFiniteDomain_sat_no_p_optimal_proof_system_variants_exists_of_P_eq_NP_R1

/-! # A retraction simulates every competing proof system -/
-- Credit: @steveDOTdigital
open ComplexityTheory PudlakFiniteDomain

theorem OMA.solution : OMA.R_PudlakFiniteDomain_sat_no_p_optimal_proof_system_variants_exists_of_P_eq_NP_R1.H2 := by
  intro L r time sound fixed
  refine ⟨⟨time, fun y => ⟨fun hy => ⟨y, fixed y hy⟩, ?_⟩⟩, ?_⟩
  · rintro ⟨w,rfl⟩
    exact sound w
  · intro Q hQ
    exact ⟨Q, hQ.1, fun w => fixed (Q w) ((hQ.2 (Q w)).2 ⟨w,rfl⟩)⟩
