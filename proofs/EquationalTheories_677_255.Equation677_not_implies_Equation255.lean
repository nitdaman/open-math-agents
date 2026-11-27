import FormalConjectures.Other.EquationalTheories_677_255

-- Problem: Equational Theories
-- Upstream: formal-conjectures FormalConjectures/Other/EquationalTheories_677_255.lean:48 (declaration EquationalTheories_677_255.Equation677_not_implies_Equation255)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace EquationalTheories_677_255
namespace OMA

inductive T : Type
  | a : T
  | node : T → T → T

open T

open scoped Classical in
def Sub : T → T → Prop
  | _, a => False
  | x, node l r => x = l ∨ x = r ∨ Sub x l ∨ Sub x r

theorem sub_size : ∀ x y : T, Sub x y → sizeOf x < sizeOf y
  | _, a, h => False.elim h
  | x, node l r, h => by
    rcases h with h | h | h | h
    · subst h; simp; try omega
    · subst h; simp; try omega
    · have := sub_size x l h; simp; try omega
    · have := sub_size x r h; simp; try omega

open scoped Classical in
noncomputable def op : T → T → T
  | x, a => node x a
  | x, node yl yr =>
    if h : Sub x (node yl yr) then
      if yr = op (op x yl) x then yl else node x (node yl yr)
    else node x (node yl yr)
termination_by x y => sizeOf y
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := sub_size x _ h; simp at this; omega)

noncomputable instance : Magma T := ⟨op⟩

theorem op_a (x : T) : op x a = node x a := by
  rw [op]

theorem t255_fail : ¬ Equation255 T := by
  intro h
  have h1 := h a
  have e : ((a ◇ a) ◇ a) ◇ a = node (node (node a a) a) a := by
    show op (op (op a a) a) a = _
    rw [op_a, op_a, op_a]
  rw [e] at h1
  cases h1

open scoped Classical in
theorem op_node (x yl yr : T) : op x (node yl yr) =
    if Sub x (node yl yr) ∧ yr = op (op x yl) x then yl else node x (node yl yr) := by
  rw [op]
  by_cases h : Sub x (node yl yr) <;> by_cases e : yr = op (op x yl) x <;> simp [h, e]

theorem lemA (x yl yr : T) :
    op x (node yl yr) = node x (node yl yr) ∨
    (op x (node yl yr) = yl ∧ Sub x (node yl yr) ∧ yr = op (op x yl) x) := by
  rw [op_node]
  split_ifs with h
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl rfl

theorem lemA2 (p q : T) : op p q = node p q ∨
    (sizeOf p < sizeOf q ∧ sizeOf (op p q) < sizeOf q ∧ Sub p q) := by
  cases q with
  | a => exact Or.inl (op_a p)
  | node l r =>
    rcases lemA p l r with h | ⟨h1, h2, _⟩
    · exact Or.inl h
    · right
      refine ⟨sub_size _ _ h2, ?_, h2⟩
      rw [h1]; simp; omega

theorem lemB (x y : T) : op x (op (op y x) y) = node x (op (op y x) y) := by
  generalize hz : op y x = z
  generalize hu : op z y = u
  cases u with
  | a => exact op_a x
  | node ul ur =>
    rcases lemA x ul ur with h | ⟨hv, hsub, hur⟩
    · exact h
    exfalso
    have hxu := sub_size x _ hsub
    rcases lemA2 z y with hu2 | ⟨hzy, huy, _⟩
    · rw [hu] at hu2
      injection hu2 with e1 e2
      subst ul
      subst ur
      rcases lemA2 y x with hz2 | ⟨hyx, hzx, _⟩
      · rw [hz] at hz2
        subst hz2
        rcases lemA x y x with hw | ⟨hw, _, _⟩
        · rw [hw] at hur
          rcases lemA2 (node x (node y x)) x with hy | ⟨hs, _, _⟩
          · rw [hy] at hur
            have := congrArg sizeOf hur
            simp at this
            omega
          · simp at hs
            omega
        · rw [hw] at hur
          rw [hz] at hur
          have := congrArg sizeOf hur
          simp at this
          omega
      · rw [hz] at hzx
        rcases lemA2 (op x z) x with hy | ⟨hs, _, _⟩
        · rw [hy] at hur
          have := congrArg sizeOf hur
          simp at this
          omega
        · rcases lemA2 x z with hw | ⟨hs2, _, _⟩
          · rw [hw] at hs
            simp at hs
            omega
          · omega
    · rcases lemA2 y x with hz2 | ⟨hyx, hzx, _⟩
      · rw [hz] at hz2
        have := congrArg sizeOf hz2
        simp at this
        omega
      · rw [hu] at huy
        omega

theorem t677 : Equation677 T := by
  intro x y
  show x = op y (op x (op (op y x) y))
  rw [lemB, op_node]
  have hs : Sub y (node x (op (op y x) y)) := by
    rcases lemA2 y x with hz | ⟨_, _, hyx⟩
    · rcases lemA2 (op y x) y with hu | ⟨h1, _, _⟩
      · right; right; right; rw [hu]
        exact Or.inr (Or.inl rfl)
      · rw [hz] at h1
        simp at h1
        omega
    · right; right; left; exact hyx
  rw [if_pos ⟨hs, rfl⟩]

end OMA

end EquationalTheories_677_255

theorem OMA.solution : type_of% @EquationalTheories_677_255.Equation677_not_implies_Equation255 :=
  ⟨EquationalTheories_677_255.OMA.T, inferInstance, EquationalTheories_677_255.OMA.t677,
    EquationalTheories_677_255.OMA.t255_fail⟩
