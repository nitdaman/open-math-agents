import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1

open CategoryTheory Filter

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R1

/-- Count groups of class three whose third lower-central subgroup has order
2^k in the indicated range. This includes every fixed positive k eventually. -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  let C : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) := ⋃ k ∈ (Finset.range (m+1)).filter (fun k => 1 ≤ k ∧ 100000000*(k+5)^2+10000000 ≤ m),
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧
      Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2^k ∧ ((⊤ : Subgroup G).lowerCentralSeries 2) ≤ Subgroup.center G}
  (16*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

/-- Count the part of the parent problem outside the class-three range in H1. -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let C : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) := ⋃ k ∈ (Finset.range (m+1)).filter (fun k => 1 ≤ k ∧ 100000000*(k+5)^2+10000000 ≤ m),
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧
      Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2^k ∧ ((⊤ : Subgroup G).lowerCentralSeries 2) ≤ Subgroup.center G}
  let X := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧
    ¬commutator G ≤ Subgroup.center G ∧ 2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2)}
  (16*(X \ C).ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1.H3 := by
  intro h1 h2
  filter_upwards [h1,h2] with m h₁ h₂
  let C : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) := ⋃ k ∈ (Finset.range (m+1)).filter (fun k => 1 ≤ k ∧ 100000000*(k+5)^2+10000000 ≤ m),
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧
      Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2^k ∧ ((⊤ : Subgroup G).lowerCentralSeries 2) ≤ Subgroup.center G}
  let X := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧
    ¬commutator G ≤ Subgroup.center G ∧ 2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2)}
  have hX : X.Finite := (OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1.finite_order_classes _).subset (by
    rintro _ ⟨G,⟨h,_,_⟩,rfl⟩;exact ⟨G,h,rfl⟩)
  have hC : C.Finite := (OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1.finite_order_classes (2^m)).subset (by
    intro z hz
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hz
    obtain ⟨_,G,⟨h,_,_⟩,rfl⟩ := Set.mem_iUnion.mp hk
    exact ⟨G,h,rfl⟩)
  have sub : X ⊆ C ∪ (X \ C) := by
    intro z hz
    by_cases h : z∈C
    · exact Or.inl h
    · exact Or.inr ⟨hz,h⟩
  have bound := (Set.ncard_le_ncard sub (hC.union (hX.subset Set.sdiff_subset))).trans (Set.ncard_union_le ..)
  change (16*C.ncard)^27*_≤_ at h₁
  change (16*(X \ C).ncard)^27*_≤_ at h₂
  change (8*X.ncard)^27*_≤_
  by_cases h : 8*X.ncard ≤ 16*C.ncard
  · exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h 27)).trans h₁
  · exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : 8*X.ncard ≤ 16*(X \ C).ncard) 27)).trans h₂

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R1
