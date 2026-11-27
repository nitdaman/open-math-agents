import FormalConjectures.Wikipedia.BusyBeaver

/-! # The four-state witness and the upper bound on indexed machines -/
-- Credit: @steveDOTdigital
namespace OMA.R_BusyBeaver_BB_4_R1
open Turing Turing.BusyBeaver BusyBeaver
def H1 : Prop := ∃ C : Candidate 4, C.M.haltingNumber = (107 : ℕ)
def H2 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)), M.IsHalting → ∀ k : ℕ, M.haltingNumber = k → k ≤ 107

theorem normalize (n : ℕ) [NeZero n] (C : Candidate n) :
    ∃ M : Machine (Fin 2) (Fin n), M.IsHalting ∧ M.haltingNumber = C.M.haltingNumber := by
  classical
  let a := (Fintype.equivFinOfCardEq C.Γ_card).setValue default (default : Fin 2)
  let b := (Fintype.equivFinOfCardEq C.Λ_card).setValue default (default : Fin n)
  let f : PointedMap C.Γ (Fin 2) := ⟨a,by simp [a]⟩
  let conf (s : Cfg C.Γ C.Λ) : Cfg (Fin 2) (Fin n) := ⟨s.q.map b,s.tape.map f⟩
  let M : Machine (Fin 2) (Fin n) := fun q t =>
    (C.M (b.symm q) (a.symm t)).map (fun (q',cmd) => (q'.map b, Stmt.write (f cmd.symbol) cmd.dir))
  have step (s : Cfg C.Γ C.Λ) : M.step (conf s) = (C.M.step s).map conf := by
    obtain ⟨q,T⟩ := s
    cases q with
    | none => rfl
    | some q =>
      simp only [Machine.step,conf,Option.map_some,Tape.map_fst,M]
      change ((C.M (b.symm (b q)) (a.symm (a T.head))).map _).map _ = _
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      cases h : C.M q T.head with
      | none => rfl
      | some z =>
        obtain ⟨q',⟨t,d⟩⟩ := z
        simp [Tape.map_move,Tape.map_write]
  have start : conf (Machine.init []) = Machine.init [] := by
    simp [conf,Machine.init,Tape.map_mk₁,b]
  have trace (k : ℕ) : M.multiStep (Machine.init []) k = (C.M.multiStep (Machine.init []) k).map conf := by
    induction k with
    | zero => simp [start]
    | succ k ih =>
      rw [Machine.multiStep_succ,Machine.multiStep_succ,ih]
      cases he : C.M.multiStep (Machine.init []) k with
      | none => rfl
      | some s => exact step s
  have stops (k : ℕ) : M.HaltsAfter (Machine.init []) k ↔ C.M.HaltsAfter (Machine.init []) k := by
    simp only [Machine.HaltsAfter,trace,Option.map_eq_none_iff]
  refine ⟨M,?_,?_⟩
  · obtain ⟨k,hk⟩ := (Machine.isHalting_iff_exists_haltsAt _).mp C.M_isHalting
    exact (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k,(stops k).mpr hk⟩
  · unfold Machine.haltingNumber
    congr 1
    ext e
    constructor <;> rintro ⟨k,hk,rfl⟩
    · exact ⟨k,(stops k).mp hk,rfl⟩
    · exact ⟨k,(stops k).mpr hk,rfl⟩

theorem main : H1 → H2 → type_of% @BusyBeaver.BB_4 := by
  intro witness bound
  let S := {n : ℕ | ∃ C : Candidate 4, C.M.haltingNumber = n}
  have hm : 107 ∈ S := witness
  have hub : ∀ k ∈ S, k ≤ 107 := by
    rintro k ⟨C,hC⟩
    obtain ⟨M,hM,h⟩ := normalize 4 C
    exact bound M hM k (h.trans hC)
  change sSup S = 107
  exact le_antisymm (csSup_le ⟨107,hm⟩ hub) (le_csSup ⟨107,hub⟩ hm)
end OMA.R_BusyBeaver_BB_4_R1
