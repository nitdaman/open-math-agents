import FormalConjectures.ErdosProblems.«94»
import Mathlib.Geometry.Euclidean.PerpBisector

/-! Equal-distance triples bound the second moment of the distance multiplicities. -/

open Finset EuclideanGeometry
open scoped BigOperators

namespace ErdosDistanceMoment

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def incident (P : Finset Point) (p : Point) (u : ℝ) : ℕ :=
  open Classical in (P.filter fun q => dist p q = u).card

noncomputable def centers (P : Finset Point) (q r : Point) : ℕ :=
  open Classical in (P.filter fun p => dist p q = dist p r).card

theorem bisector_collinear {q r : Point} (hqr : q ≠ r) :
    Collinear ℝ (AffineSubspace.perpBisector q r : Set Point) := by
  apply collinear_iff_finrank_le_one.mpr
  rw [← AffineSubspace.direction_eq_vectorSpan, AffineSubspace.direction_perpBisector]
  have hs : Module.finrank ℝ (ℝ ∙ (r -ᵥ q)) = 1 :=
    finrank_span_singleton (vsub_ne_zero.mpr hqr.symm)
  have htotal := (ℝ ∙ (r -ᵥ q)).finrank_add_finrank_orthogonal
  rw [hs, finrank_euclideanSpace_fin] at htotal
  omega

theorem centers_le_two {P : Finset Point} (hP : NonTrilinear (P : Set Point))
    {q r : Point} (hqr : q ≠ r) : centers P q r ≤ 2 := by
  classical
  by_contra! hn
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < (P.filter fun p => dist p q = dist p r).card from hn)
  obtain ⟨haP, had⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbP, hbd⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcP, hcd⟩ := Finset.mem_filter.mp hc
  apply hP haP hbP hcP hab hbc hac
  apply (bisector_collinear hqr).subset
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff,
    AffineSubspace.mem_coe, AffineSubspace.mem_perpBisector_iff_dist_eq]
  exact ⟨had, hbd, hcd⟩

theorem multiplicity_le_incident (P : Finset Point) (u : ℝ) :
    distanceMultiplicity P u ≤ ∑ p ∈ P, incident P p u := by
  classical
  unfold distanceMultiplicity
  refine (Nat.div_le_self _ _).trans ?_
  have hsub : (P.offDiag.filter fun x : Point × Point => dist x.1 x.2 = u) ⊆
      ((P.product P).filter fun x : Point × Point => dist x.1 x.2 = u) := by
    intro x hx
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hx
    obtain ⟨h1, h2, _⟩ := Finset.mem_offDiag.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hd⟩
  refine (Finset.card_le_card hsub).trans_eq ?_
  simp only [Finset.card_filter, incident]
  change (∑ x ∈ P ×ˢ P, (if dist x.1 x.2 = u then 1 else 0 : ℕ)) = _
  rw [Finset.sum_product]

theorem incident_sq (P : Finset Point) (p : Point) (u : ℝ) :
    incident P p u ^ 2 = ∑ q ∈ P, ∑ r ∈ P,
      if dist p q = u ∧ dist p r = u then 1 else 0 := by
  classical
  unfold incident
  rw [pow_two, ← Finset.card_product, ← Finset.filter_product,
    Finset.card_filter, Finset.sum_product]

theorem point_moment_le (P : Finset Point) (p : Point) :
    (∑ u ∈ distanceSet P, incident P p u ^ 2) ≤
      ∑ q ∈ P, ∑ r ∈ P, if dist p q = dist p r then 1 else 0 := by
  classical
  simp_rw [incident_sq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro r _
  by_cases heq : dist p q = dist p r
  · simp only [← heq, and_self, ↓reduceIte, Finset.sum_ite_eq]
    split_ifs <;> omega
  · have himp (u : ℝ) : ¬ (dist p q = u ∧ dist p r = u) :=
      fun h => heq (h.1.trans h.2.symm)
    simp [heq, himp]

theorem sum_centers_le (P : Finset Point) (hP : NonTrilinear (P : Set Point))
    {q : Point} (hq : q ∈ P) : (∑ r ∈ P, centers P q r) ≤ 3 * P.card := by
  classical
  rw [← Finset.sum_erase_add P _ hq]
  have hdiag : centers P q q = P.card := by simp [centers]
  rw [hdiag]
  have hoff : (∑ r ∈ P.erase q, centers P q r) ≤ ∑ _r ∈ P.erase q, (2 : ℕ) := by
    apply Finset.sum_le_sum
    intro r hr
    exact centers_le_two hP (Finset.ne_of_mem_erase hr).symm
  simp only [Finset.sum_const, Nat.nsmul_eq_mul] at hoff
  have hcard := Finset.card_erase_le (s := P) (a := q)
  omega

theorem second_incidence_le (P : Finset Point) (hP : NonTrilinear (P : Set Point)) :
    (∑ u ∈ distanceSet P, ∑ p ∈ P, incident P p u ^ 2) ≤ 3 * P.card ^ 2 := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ p ∈ P, ∑ u ∈ distanceSet P, incident P p u ^ 2) ≤
        ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, if dist p q = dist p r then 1 else 0 :=
      Finset.sum_le_sum (fun p _ => point_moment_le P p)
    _ = ∑ q ∈ P, ∑ r ∈ P, centers P q r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_comm]
      simp only [centers, Finset.card_filter]
    _ ≤ ∑ _q ∈ P, 3 * P.card := Finset.sum_le_sum (fun _ hq => sum_centers_le P hP hq)
    _ = 3 * P.card ^ 2 := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]; ring

theorem distance_moment_le (P : Finset Point) (hP : NonTrilinear (P : Set Point)) :
    (∑ u ∈ distanceSet P, distanceMultiplicity P u ^ 2) ≤ 3 * P.card ^ 3 := by
  classical
  calc
    (∑ u ∈ distanceSet P, distanceMultiplicity P u ^ 2) ≤
        ∑ u ∈ distanceSet P, P.card * ∑ p ∈ P, incident P p u ^ 2 := by
      apply Finset.sum_le_sum
      intro u _
      have hcs : (∑ p ∈ P, incident P p u) ^ 2 ≤
          P.card * ∑ p ∈ P, incident P p u ^ 2 := by
        simpa [Finset.sum_const, nsmul_eq_mul] using
          (Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1 : ℕ)) (fun p => incident P p u))
      exact (Nat.pow_le_pow_left (multiplicity_le_incident P u) 2).trans hcs
    _ = P.card * (∑ u ∈ distanceSet P, ∑ p ∈ P, incident P p u ^ 2) := by rw [Finset.mul_sum]
    _ ≤ P.card * (3 * P.card ^ 2) := Nat.mul_le_mul_left _ (second_incidence_le P hP)
    _ = 3 * P.card ^ 3 := by ring

end ErdosDistanceMoment

theorem OMA.solution : type_of% @Erdos94.erdos_94.variants.no_three_on_a_line := by
  refine ⟨3, by norm_num, ?_⟩
  intro P hP
  exact_mod_cast ErdosDistanceMoment.distance_moment_le P hP