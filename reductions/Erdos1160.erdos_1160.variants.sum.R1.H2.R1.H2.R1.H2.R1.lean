import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance

open Filter CategoryTheory

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1

/-- Order-two-power groups of nilpotency class at most two. -/
def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop,
    (4 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ commutator G ≤ Subgroup.center G}).ncard)^27 *
        2^(9*m^2) ≤ 2^(2*m^3)

/-- Higher-class groups whose third lower central subgroup has order at most two. -/
def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop,
    (8 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ Subgroup.center G ∧
        Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ≤ 2}).ncard)^27 *
        2^(9*m^2) ≤ 2^(2*m^3)

/-- Higher-class groups whose third lower central subgroup has order greater than two. -/
def H3 : Prop :=
  ∀ᶠ m : ℕ in atTop,
    (8 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ Subgroup.center G ∧
        2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2)}).ncard)^27 *
        2^(9*m^2) ≤ 2^(2*m^3)

lemma finite_order_classes (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}).Finite := by
  letI : Finite (Group (Fin n)) :=
    Finite.of_injective (fun h : Group (Fin n) => h.mul) (fun _ _ h => Group.ext h)
  let q := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0})
  let code (h : Group (Fin n)) := let _ := h; q (FiniteGrp.of (Fin n))
  apply (Set.finite_range code).subset
  rintro _ ⟨G,hG,rfl⟩
  let _ := Fintype.ofFinite G
  have hh : Fintype.card G = n := (Nat.card_eq_fintype_card (α := G)).symm.trans hG
  let e : Fin n ≃ G := (Fintype.equivFinOfCardEq hh).symm
  let h := e.group
  let _ := h
  let K : FiniteGrp := FiniteGrp.of (Fin n)
  let eg : K ≃* G := e.mulEquiv
  exact ⟨h, Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X := K.toGrp) (Y := G.toGrp) eg)⟩⟩

lemma weighted_bound (x a b c t u : ℕ) (h : x ≤ a+b+c)
    (ha : (4*a)^27*t ≤ u) (hb : (8*b)^27*t ≤ u) (hc : (8*c)^27*t ≤ u) :
    (2*x)^27*t ≤ u := by
  rcases le_total b c with hbc | hcb
  · by_cases hbig : 2*c ≤ a
    · exact (Nat.mul_le_mul_right t (Nat.pow_le_pow_left (by omega : 2*x ≤ 4*a) 27)).trans ha
    · exact (Nat.mul_le_mul_right t (Nat.pow_le_pow_left (by omega : 2*x ≤ 8*c) 27)).trans hc
  · by_cases hbig : 2*b ≤ a
    · exact (Nat.mul_le_mul_right t (Nat.pow_le_pow_left (by omega : 2*x ≤ 4*a) 27)).trans ha
    · exact (Nat.mul_le_mul_right t (Nat.pow_le_pow_left (by omega : 2*x ≤ 8*b) 27)).trans hb

theorem main : H1 → H2 → H3 → OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1.H2 := by
  intro hlow hsmall hlarge
  unfold H1 at hlow
  unfold H2 at hsmall
  unfold H3 at hlarge
  unfold OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1.H2
  filter_upwards [hlow,hsmall,hlarge] with m hl hs hg
  let q := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0})
  let D (G : FiniteGrp.{0}) := Nat.card G = 2^m
  let C (G : FiniteGrp.{0}) := commutator G ≤ Subgroup.center G
  let k (G : FiniteGrp.{0}) := Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2)
  let X := q '' {G : FiniteGrp.{0} | D G ∧
    ¬ (frattini G ≤ Subgroup.center G ∧ ∀ x : frattini G, x*x=1)}
  let A := q '' {G : FiniteGrp.{0} | D G ∧ C G}
  let B := q '' {G : FiniteGrp.{0} | D G ∧ ¬C G ∧ k G ≤ 2}
  let F := q '' {G : FiniteGrp.{0} | D G ∧ ¬C G ∧ 2 < k G}
  have sub : X ⊆ (A∪B)∪F := by
    rintro _ ⟨G,⟨hD,_⟩,rfl⟩
    by_cases hC : C G
    · exact Or.inl (Or.inl ⟨G,⟨hD,hC⟩,rfl⟩)
    · by_cases h2 : k G ≤ 2
      · exact Or.inl (Or.inr ⟨G,⟨hD,hC,h2⟩,rfl⟩)
      · exact Or.inr ⟨G,⟨hD,hC,Nat.lt_of_not_ge h2⟩,rfl⟩
  have hf : ((A∪B)∪F).Finite := by
    apply (finite_order_classes (2^m)).subset
    rintro _ ((⟨G,h,rfl⟩ | ⟨G,h,rfl⟩) | ⟨G,h,rfl⟩) <;> exact ⟨G,h.1,rfl⟩
  have hn := (Set.ncard_le_ncard sub hf).trans (Set.ncard_union_le (A∪B) F)
  exact weighted_bound X.ncard A.ncard B.ncard F.ncard _ _ (by
    have hab := Set.ncard_union_le A B
    omega) hl hs hg

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1
