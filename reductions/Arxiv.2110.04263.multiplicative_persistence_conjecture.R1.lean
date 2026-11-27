import FormalConjectures.Arxiv.«2110.04263».MultiplicativePersistence

namespace OMA.R_Arxiv_2110_04263_multiplicative_persistence_conjecture_R1

open Arxiv.«2110.04263»

private lemma classify (l : List ℕ) (hl : ∀ x ∈ l, x < 10) :
    l.prod = 0 ∨ ∃ a b c d : ℕ, l.prod = 2^a * 3^b * 5^c * 7^d := by
  induction l with
  | nil => exact Or.inr ⟨0, 0, 0, 0, by decide⟩
  | cons x xs ih =>
    obtain hz | ⟨a,b,c,d,h⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    · simp [hz]
    have hx := hl x List.mem_cons_self
    rw [List.prod_cons, h]
    interval_cases x
    · simp
    · exact Or.inr ⟨a, b, c, d, by ring⟩
    · exact Or.inr ⟨a+1, b, c, d, by ring⟩
    · exact Or.inr ⟨a, b+1, c, d, by ring⟩
    · exact Or.inr ⟨a+2, b, c, d, by ring⟩
    · exact Or.inr ⟨a, b, c+1, d, by ring⟩
    · exact Or.inr ⟨a+1, b+1, c, d, by ring⟩
    · exact Or.inr ⟨a, b, c, d+1, by ring⟩
    · exact Or.inr ⟨a+3, b, c, d, by ring⟩
    · exact Or.inr ⟨a, b+2, c, d, by ring⟩

private lemma zero_of_ten_dvd (m : ℕ) (hm : 10 ∣ m) : digitProduct m = 0 := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [digitProduct, Nat.digits_def' (by decide) (Nat.succ_pos _),
      Nat.mod_eq_zero_of_dvd hm, List.prod_cons, zero_mul]

/-- First products with no factor five. -/
def H1 : Prop :=
  ∀ a b c : ℕ, (digitProduct^[10]) (2^a * 3^b * 7^c) < 10

/-- Odd first products containing a factor five. -/
def H2 : Prop :=
  ∀ b c d : ℕ, (digitProduct^[10]) (3^b * 5^(c+1) * 7^d) < 10

theorem main : H1 → H2 → type_of% @Arxiv.«2110.04263».multiplicative_persistence_conjecture := by
  intro h₁ h₂ n
  cases n with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ n =>
    have h := classify (Nat.digits 10 (n+1)) (fun _ => Nat.digits_lt_base (by decide))
    change digitProduct (n+1) = 0 ∨ _ at h
    rcases h with hz | ⟨a,b,c,d,h⟩
    · exact ⟨1, by decide, by simpa [hz]⟩
    change digitProduct (n+1) = _ at h
    cases c with
    | zero =>
      exact ⟨11, by decide, by simpa [Function.iterate_succ_apply _ 10, h] using h₁ a b d⟩
    | succ c =>
      cases a with
      | zero =>
        exact ⟨11, by decide, by simpa [Function.iterate_succ_apply _ 10, h] using h₂ b c d⟩
      | succ a =>
        have hd : 10 ∣ digitProduct (n+1) := ⟨2^a * 3^b * 5^c * 7^d, by rw [h]; ring⟩
        exact ⟨2, by decide, by simpa [Function.iterate_succ_apply, zero_of_ten_dvd _ hd]⟩

end OMA.R_Arxiv_2110_04263_multiplicative_persistence_conjecture_R1
