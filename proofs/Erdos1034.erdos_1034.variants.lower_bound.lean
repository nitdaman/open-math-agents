import FormalConjectures.ErdosProblems.«1034»
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The book bound is due independently to Edwards and to Khadzhiivanov and Nikiforov.
We use the degree and triangle counts from Béla Bollobás and Vladimir Nikiforov,
“Books in graphs,” European J. Combin. 26 (2005), 259–270.
https://doi.org/10.1016/j.ejc.2004.01.007
-/

open Finset Filter SimpleGraph

namespace OMA

private abbrev OrderedTriangle {V : Type} (G : SimpleGraph V) :=
  Σ d : G.Dart, ↥(G.commonNeighbors d.fst d.snd)

/-- Cyclically rotate the three vertices of an ordered triangle. -/
private def rotateTriangle {V : Type} (G : SimpleGraph V) :
    OrderedTriangle G ≃ OrderedTriangle G where
  toFun p :=
    ⟨⟨(p.1.snd, p.2.val), p.2.property.2⟩,
      ⟨p.1.fst, p.1.adj.symm, p.2.property.1.symm⟩⟩
  invFun p :=
    ⟨⟨(p.2.val, p.1.fst), p.2.property.1.symm⟩,
      ⟨p.1.snd, p.2.property.2.symm, p.1.adj⟩⟩
  left_inv := by rintro ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩; rfl

section Count

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private abbrev common (u v : V) : ℝ := Fintype.card (G.commonNeighbors u v)

private lemma common_eq_inter_card [DecidableEq V] (u v : V) :
    Fintype.card (G.commonNeighbors u v) = (G.neighborFinset u ∩ G.neighborFinset v).card := by
  rw [← Set.toFinset_card]
  congr 1
  ext x
  simp [G.mem_commonNeighbors]

private lemma sum_dart_fst (f : V → ℝ) :
    (∑ d : G.Dart, f d.fst) = ∑ v : V, (G.degree v : ℝ) * f v := by
  let e : (Σ v : V, ↥(G.neighborSet v)) ≃ G.Dart :=
    ⟨fun p => ⟨(p.1, p.2.val), p.2.property⟩, fun d => ⟨d.fst, d.snd, d.adj⟩,
      by rintro ⟨v, w, _⟩; rfl, by rintro ⟨⟨u, v⟩, _⟩; rfl⟩
  calc
    _ = ∑ p : Σ v : V, ↥(G.neighborSet v), f p.1 := (e.sum_comp fun d => f d.fst).symm
    _ = _ := by simp [Fintype.sum_sigma, nsmul_eq_mul, G.card_neighborSet_eq_degree]

private lemma sum_dart_snd (f : V → ℝ) :
    (∑ d : G.Dart, f d.snd) = ∑ v : V, (G.degree v : ℝ) * f v := by
  let e : G.Dart ≃ G.Dart := ⟨Dart.symm, Dart.symm, Dart.symm_symm, Dart.symm_symm⟩
  calc
    _ = ∑ d : G.Dart, f d.fst := e.sum_comp fun d => f d.fst
    _ = _ := sum_dart_fst G f

private lemma sum_triangle_dart (f : G.Dart → ℝ) :
    (∑ p : OrderedTriangle G, f p.1) =
      ∑ d : G.Dart, common G d.fst d.snd * f d := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, common]

private lemma edge_degrees (u v : V) :
    (G.degree u : ℝ) + G.degree v - Fintype.card V ≤ common G u v := by
  classical
  let X := G.neighborFinset u
  let Y := G.neighborFinset v
  have hcard := Finset.card_union_add_card_inter X Y
  have hle := Finset.card_le_univ (X ∪ Y)
  have hu : X.card = G.degree u := G.card_neighborFinset_eq_degree u
  have hv : Y.card = G.degree v := G.card_neighborFinset_eq_degree v
  rw [hu, hv, ← common_eq_inter_card G u v] at hcard
  exact sub_le_iff_le_add.mpr (by exact_mod_cast (show G.degree u + G.degree v ≤
    Fintype.card (G.commonNeighbors u v) + Fintype.card V by omega))

private lemma three_degrees (u v w : V) :
    (G.degree u : ℝ) + G.degree v + G.degree w ≤
      Fintype.card V + (common G u v + common G v w + common G w u) := by
  classical
  let X := G.neighborFinset u
  let Y := G.neighborFinset v
  let Z := G.neighborFinset w
  have hu : X.card = G.degree u := G.card_neighborFinset_eq_degree u
  have hv : Y.card = G.degree v := G.card_neighborFinset_eq_degree v
  have hw : Z.card = G.degree w := G.card_neighborFinset_eq_degree w
  have huv : (X ∩ Y).card = Fintype.card (G.commonNeighbors u v) :=
    (common_eq_inter_card G u v).symm
  have hvw : (Y ∩ Z).card = Fintype.card (G.commonNeighbors v w) :=
    (common_eq_inter_card G v w).symm
  have hwu : (Z ∩ X).card = Fintype.card (G.commonNeighbors w u) :=
    (common_eq_inter_card G w u).symm
  have hxy := Finset.card_union_add_card_inter X Y
  have hxyz := Finset.card_union_add_card_inter (X ∪ Y) Z
  have hN := Finset.card_le_univ ((X ∪ Y) ∪ Z)
  have hsub : (X ∪ Y) ∩ Z ⊆ (Y ∩ Z) ∪ (Z ∩ X) := by
    intro a ha
    simp only [Finset.mem_inter, Finset.mem_union] at ha ⊢
    tauto
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact_mod_cast (show G.degree u + G.degree v + G.degree w ≤
    Fintype.card V + (Fintype.card (G.commonNeighbors u v) +
      Fintype.card (G.commonNeighbors v w) + Fintype.card (G.commonNeighbors w u)) by omega)

end Count

private lemma exists_large_book {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 0 < Fintype.card V)
    (hdensity : (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card) :
    ∃ d : G.Dart, (Fintype.card V : ℝ) < 6 * common G d.fst d.snd := by
  classical
  let n : ℝ := Fintype.card V
  let m : ℝ := G.edgeFinset.card
  let degree (v : V) : ℝ := G.degree v
  let t (d : G.Dart) : ℝ := common G d.fst d.snd
  let q (d : G.Dart) : ℝ := degree d.fst + degree d.snd - n
  let I : ℝ := ∑ d : G.Dart, q d
  let J : ℝ := ∑ d : G.Dart, t d
  let K : ℝ := ∑ d : G.Dart, t d ^ 2
  let L : ℝ := ∑ d : G.Dart, t d * q d
  have hnR : 0 < n := Nat.cast_pos.mpr hn
  have hm : 0 < m := (by positivity : 0 ≤ n ^ 2 / 4).trans_lt hdensity
  have hdeg : (∑ v : V, degree v) = 2 * m := by
    change (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ)
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hcard : (Fintype.card G.Dart : ℝ) = 2 * m := by
    change (Fintype.card G.Dart : ℝ) = 2 * (G.edgeFinset.card : ℝ)
    exact_mod_cast G.dart_card_eq_twice_card_edges
  have hCauchy : (∑ v : V, degree v) ^ 2 ≤ n * ∑ v : V, degree v ^ 2 := by
    simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := degree))
  have hdegree_square : m * n < ∑ v : V, degree v ^ 2 := by
    have hprod : n * (m * n) < (2 * m) ^ 2 := by
      have hden : 0 < m - n ^ 2 / 4 := sub_pos.mpr hdensity
      nlinarith only [mul_pos hm hden]
    rw [hdeg] at hCauchy
    by_contra h
    exact (hprod.trans_le hCauchy).not_ge (mul_le_mul_of_nonneg_left (le_of_not_gt h) hnR.le)
  have hI : 0 < I := by
    have hfst := sum_dart_fst G degree
    have hsnd := sum_dart_snd G degree
    have h : I = 2 * (∑ v : V, degree v ^ 2) - 2 * m * n := by
      simp only [I, q, Finset.sum_sub_distrib, Finset.sum_add_distrib, hfst, hsnd,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, pow_two, degree]
      ring
    linarith only [h, hdegree_square]
  have hp (d : G.Dart) : q d ≤ t d := edge_degrees G d.fst d.snd
  have hIJ : I ≤ J := Finset.sum_le_sum fun d _ => hp d
  have hJ : 0 < J := hI.trans_le hIJ
  have hdn : 0 < Fintype.card G.Dart := by
    have h := hcard.symm ▸ (show (0 : ℝ) < 2 * m by positivity)
    exact_mod_cast h
  have hDarts : (Finset.univ : Finset G.Dart).Nonempty :=
    Finset.card_pos.mp (by simpa only [Finset.card_univ] using hdn)
  obtain ⟨d₀, _, hd₀⟩ := Finset.exists_max_image (Finset.univ : Finset G.Dart) t hDarts
  let b := t d₀
  have max_le (d : G.Dart) : t d ≤ b := hd₀ d (Finset.mem_univ d)
  have ht_nonneg (d : G.Dart) : 0 ≤ t d := by dsimp [t]; positivity
  have hb : 0 < b := by
    by_contra h
    have hj : J ≤ 0 := Finset.sum_nonpos fun d _ => (max_le d).trans (le_of_not_gt h)
    exact hJ.not_ge hj

  -- Count each triangle using all six orders of its vertices.
  let P : ℝ := ∑ p : OrderedTriangle G, degree p.1.fst
  have hPageCount : (Fintype.card (OrderedTriangle G) : ℝ) = J := by
    unfold J OrderedTriangle
    rw [Fintype.card_sigma, Nat.cast_sum]
  have hdegree₂ : (∑ p : OrderedTriangle G, degree p.1.snd) = P :=
    (rotateTriangle G).sum_comp (fun p => degree p.1.fst)
  have hdegree₃ : (∑ p : OrderedTriangle G, degree p.2.val) = P :=
    ((rotateTriangle G).sum_comp (fun p => degree p.1.snd)).trans hdegree₂
  have hpage₁ : (∑ p : OrderedTriangle G, common G p.1.fst p.1.snd) = K := by
    change (∑ p : OrderedTriangle G, t p.1) = ∑ d : G.Dart, t d ^ 2
    simp only [pow_two]
    exact sum_triangle_dart G t
  have hpage₂ : (∑ p : OrderedTriangle G, common G p.1.snd p.2.val) = K :=
    ((rotateTriangle G).sum_comp (fun p => common G p.1.fst p.1.snd)).trans hpage₁
  have hpage₃ : (∑ p : OrderedTriangle G, common G p.2.val p.1.fst) = K :=
    ((rotateTriangle G).sum_comp (fun p => common G p.1.snd p.2.val)).trans hpage₂
  have hcap : P + P + P ≤ J * n + (K + K + K) := by
    have h : (∑ p : OrderedTriangle G, (degree p.1.fst + degree p.1.snd + degree p.2.val)) ≤
        (∑ p : OrderedTriangle G, (n + (common G p.1.fst p.1.snd +
          common G p.1.snd p.2.val + common G p.2.val p.1.fst))) :=
      Finset.sum_le_sum fun p _ => three_degrees G p.1.fst p.1.snd p.2.val
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hdegree₂, hdegree₃, hpage₁, hpage₂, hpage₃, hPageCount, P] using h
  have hL : P + P - J * n = L := by
    have h : (∑ p : OrderedTriangle G, (degree p.1.fst + degree p.1.snd - n)) = L :=
      sum_triangle_dart G q
    simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hdegree₂, hPageCount, P] using h

  -- Weight the two-neighborhood inequality by the remaining room in the largest book.
  have hweighted : b * I - L ≤ b * J - K := by
    have h : (∑ d : G.Dart, (b - t d) * q d) ≤ ∑ d : G.Dart, (b - t d) * t d :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hp d) (sub_nonneg.mpr (max_le d))
    simpa only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, ← pow_two, I, J, K, L] using h
  have hK : K ≤ b * J := by
    calc
      _ ≤ ∑ d : G.Dart, b * t d := Finset.sum_le_sum fun d _ => by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (max_le d) (ht_nonneg d)
      _ = _ := (Finset.mul_sum ..).symm
  have hfinal : 3 * b * I ≤ (6 * b - n) * J := by
    nlinarith only [hweighted, hcap, hL, hK]
  refine ⟨d₀, ?_⟩
  change n < 6 * b
  by_contra h
  have hright := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt h)) hJ.le
  have hleft : 0 < 3 * b * I := by positivity
  exact hleft.not_ge (hfinal.trans hright)

end OMA

theorem OMA.solution : type_of% @Erdos1034.erdos_1034.variants.lower_bound := by
  intro ε hε
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  intro G hdensity
  classical
  have hm : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hm] at hdensity
  obtain ⟨d, hd⟩ := OMA.exists_large_book G (by simpa only [Fintype.card_fin] using Nat.lt_of_succ_le hn) (by simpa using hdensity)
  let Y := G.neighborFinset d.fst ∩ G.neighborFinset d.snd
  have hY : (Y.card : ℝ) = OMA.common G d.fst d.snd := by
    exact_mod_cast (OMA.common_eq_inter_card G d.fst d.snd).symm
  have hlarge : (n : ℝ) < 6 * (Y.card : ℝ) := by
    rw [hY]
    simpa only [Fintype.card_fin] using hd
  have hpos : 0 < Y.card := by
    exact_mod_cast (show 0 < (Y.card : ℝ) by linarith [show 0 ≤ (n : ℝ) by positivity])
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have adjacencies {v : Fin n} (hv : v ∈ Y) : G.Adj d.fst v ∧ G.Adj d.snd v := by
    exact ⟨(G.mem_neighborFinset d.fst v).mp (Finset.mem_inter.mp hv).1,
      (G.mem_neighborFinset d.snd v).mp (Finset.mem_inter.mp hv).2⟩
  refine ⟨{d.fst, d.snd, w}, is3Clique_triple_iff.mpr ⟨d.adj, (adjacencies hw).1,
    (adjacencies hw).2⟩, Y, ?_, ?_⟩
  · intro y hy
    refine ⟨d.fst, by simp, d.snd, by simp, d.fst_ne_snd, (adjacencies hy).1.symm,
      (adjacencies hy).2.symm⟩
  · calc
      _ ≤ (1 / 6 : ℝ) * n := mul_le_mul_of_nonneg_right (sub_le_self _ hε.le) (by positivity)
      _ ≤ _ := by linarith