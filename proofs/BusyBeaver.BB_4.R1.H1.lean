import OMAReductions.R_BusyBeaver_BB_4_R1

/-! # A four-state machine halting after 107 transitions -/
-- Credit: @steveDOTdigital

open Turing Turing.BusyBeaver BusyBeaver
namespace OMA.BB4Witness
private def champion : Machine (Fin 2) (Fin 4) := fun q s =>
  match q.val,s.val with
  | 0,0 => some (some 1, ⟨1,.right⟩)
  | 0,_ => some (some 1, ⟨1,.left⟩)
  | 1,0 => some (some 0, ⟨1,.left⟩)
  | 1,_ => some (some 2, ⟨0,.left⟩)
  | 2,0 => some (none,   ⟨1,.right⟩)
  | 2,_ => some (some 3, ⟨1,.left⟩)
  | _,0 => some (some 3, ⟨1,.right⟩)
  | _,_ => some (some 0, ⟨0,.right⟩)
private theorem stop : champion.multiStep (Machine.init []) 108 = none := by rfl
private theorem live : (champion.multiStep (Machine.init []) 107).isSome := by rfl
theorem witness : OMA.R_BusyBeaver_BB_4_R1.H1 := by
  let C : Candidate 4 :=
    { Γ := Fin 2
      Λ := Fin 4
      Γ_fintype := inferInstance
      Γ_card := Fintype.card_fin _
      Γ_inhabited := inferInstance
      Λ_fintype := inferInstance
      Λ_card := Fintype.card_fin _
      Λ_inhabited := inferInstance
      M := champion
      M_isHalting := (Machine.isHalting_iff_exists_haltsAt champion).mpr ⟨107,stop⟩ }
  refine ⟨C,?_⟩
  exact Machine.haltingNumber_def champion 107 (Option.isSome_iff_exists.mp live) stop
end OMA.BB4Witness

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1.H1 := OMA.BB4Witness.witness
