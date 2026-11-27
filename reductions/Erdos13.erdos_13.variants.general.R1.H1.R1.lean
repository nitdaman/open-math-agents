import OMAReductions.R_Erdos13_erdos_13_variants_general_R1

/-! # Erdős 13, the sparse terminal interval

At arity two the required estimate follows from Bedert's theorem. At
higher arities an unbounded excess forces a positive proportion of
small elements, of even elements, and of multiples of three. These three
groups can overlap. The density constraints come from estimates for the
subsets obtained by removing each of those groups. -/

-- Credit: @jenil-bodhani

namespace OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1

open Finset

/-- The two-summand case, without a terminal-density assumption. -/
def H1 : Prop :=
  ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ), A ⊆ Icc 1 (3*m) → m+K < A.card →
    ∃ a ∈ A, ∃ b : Fin 2 → ℕ, (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i

/-- Necessary density conditions on a sparse admissible set with large excess. -/
def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → m+K < A.card →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m ∧
    m < (24*r*r*(r+1)+1)*(A.filter (fun a => r*a < (r+1)*m)).card ∧
    m < (3*r+4)*(A.filter (fun a => 3 ∣ a)).card ∧
    m < (r+2)*(A.filter (fun a => 2 ∣ a)).card

/-- The remaining configurations have many small divisors, even elements,
and multiples of three, while every terminal group of blocks has excess. -/
def H3 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → m+K < A.card →
    (∀ j < m, m-j < (A.filter fun a => (r+1)*j < a).card) →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m →
    m < (24*r*r*(r+1)+1)*(A.filter (fun a => r*a < (r+1)*m)).card →
    m < (3*r+4)*(A.filter (fun a => 3 ∣ a)).card →
    m < (r+2)*(A.filter (fun a => 2 ∣ a)).card →
    ∃ a ∈ A, ∃ b : Fin r → ℕ, (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i

theorem main : H1 → H2 → H3 → OMA.R_Erdos13_erdos_13_variants_general_R1.H1 := by
  intro two densities core r hr
  rcases eq_or_lt_of_le hr with h | h
  · subst r
    obtain ⟨K, bound⟩ := two
    exact ⟨K, fun m A sub excess _ _ => bound m A sub excess⟩
  have hr3 : 3 ≤ r := h
  obtain ⟨K, necessary⟩ := densities r hr3
  obtain ⟨L, finish⟩ := core r hr3
  refine ⟨max K L, ?_⟩
  intro m A sub excess record sparse
  by_contra no
  have free (a) (ha : a ∈ A) (b : Fin r → ℕ)
      (hb : ∀ i, b i ∈ A) (hlt : ∀ i, a < b i) (dvd : a ∣ ∑ i, b i) : False :=
    no ⟨a, ha, b, fun i => ⟨hb i, hlt i⟩, dvd⟩
  obtain ⟨terminal, low, three, even⟩ := necessary m A sub (by omega) sparse free
  exact no (finish m A sub (by omega) record sparse terminal low three even)

end OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1
