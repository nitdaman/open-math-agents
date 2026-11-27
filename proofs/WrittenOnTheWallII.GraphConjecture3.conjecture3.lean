import FormalConjectures.WrittenOnTheWallII.GraphConjecture3
import Mathlib.Combinatorics.SimpleGraph.Star

/-! A spanning tree containing the star at a vertex has at least as many
leaves as that vertex has neighbors. An independent dominating set containing
the vertex avoids its entire neighborhood. Credit: @Deldor14. -/
open SimpleGraph Finset
namespace OMA.Temperature
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
open scoped Classical in
private lemma leaves_bound [DecidableRel G.Adj] (T : SimpleGraph V) (ht : T ≤ G)
    (hT : T.IsTree) (s : Finset V) (hs : ∀ v ∈ s, (G.toSubgraph T ht).degree v = 1) :
    (s.card : ℝ) ≤ Ls G := by
  classical
  let S := G.toSubgraph T ht
  let leaves (Z : G.Subgraph) := Z.verts.toFinset.filter (fun v => Z.degree v = 1)
  have iso : S.coe ≃g T :=
    { toEquiv := Equiv.Set.univ V
      map_rel_iff' := by intros; rfl }
  have hS : S.IsSpanning ∧ S.coe.IsTree := ⟨SimpleGraph.toSubgraph.isSpanning T ht, iso.isTree_iff.mpr hT⟩
  have hj : s ⊆ leaves S := by
    intro v hv; exact Finset.mem_filter.mpr ⟨by simp [S], hs v hv⟩
  have hb : (s.card : ℝ) ≤ (leaves S).card := by exact_mod_cast Finset.card_le_card hj
  unfold Ls
  apply hb.trans
  apply le_csSup
  · refine ⟨(Fintype.card V : ℝ), ?_⟩
    rintro _ ⟨Z, _,rfl⟩
    dsimp only
    exact Nat.cast_le.mpr (Finset.card_le_univ _)
  · exact ⟨S,hS,rfl⟩


private lemma tree_degree_le [DecidableRel G.Adj] (ht : G.IsTree) (a : V) :
    G.degree a ≤ (univ.filter (fun v => G.degree v = 1)).card := by
  classical
  have hw (v : V) : (2 : ℕ) + (if v = a then G.degree a else 0) ≤
      G.degree v + (if G.degree v = 1 then 1 else 0) + (if v = a then 2 else 0) := by
    have hpos := ht.connected.preconnected.degree_pos_of_nontrivial v
    by_cases hv : v = a
    · subst v; simp only [if_true]; split <;> omega
    · by_cases h1 : G.degree v = 1 <;> simp only [if_neg hv, h1, if_true, if_false, add_zero] <;> omega
  have hsum := Finset.sum_le_sum (s := univ) (fun v _ => hw v)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_boole] at hsum
  have hdeg := G.sum_degrees_eq_twice_card_edges
  have hedge := ht.card_edgeFinset
  simp at hsum
  omega

private lemma degree_le_leaves [DecidableRel G.Adj] (hc : G.Connected) (v : V) :
    (G.degree v : ℝ) ≤ Ls G := by
  classical
  let H := G ⊓ starGraph v
  have hH : H.IsAcyclic := (isTree_starGraph v).isAcyclic.anti inf_le_right
  obtain ⟨T,hHT,hTG,ht⟩ := hc.exists_isTree_le_of_le_of_isAcyclic (show H ≤ G from inf_le_left) hH
  have he : G.neighborFinset v ⊆ T.neighborFinset v := by
    intro w hw
    have ha := (G.mem_neighborFinset v w).mp hw
    exact (T.mem_neighborFinset v w).mpr (hHT ⟨ha,starGraph_center_adj ha.ne⟩)
  have hdeg : G.degree v ≤ T.degree v := Finset.card_le_card he
  have bound := leaves_bound T hTG ht (univ.filter fun x => T.degree x = 1)
    (fun w hw => by rw [SimpleGraph.degree_toSubgraph]; exact (mem_filter.mp hw).2)
  exact (show (G.degree v : ℝ) ≤ ((univ.filter fun x => T.degree x = 1).card : ℕ) by
    exact_mod_cast hdeg.trans (tree_degree_le ht v)).trans bound

private lemma domination_bound [DecidableRel G.Adj] (v : V) :
    G.indepDominationNumber + G.degree v ≤ Fintype.card V := by
  classical
  let A := univ.filter fun s : Finset V => G.IsIndepSet s
  have hseed : {v} ∈ A := by
    simp only [A, mem_filter, mem_univ, true_and]
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb
    exact (hab (ha.trans hb.symm)).elim
  obtain ⟨s,hvs,hmax⟩ := A.exists_le_maximal hseed
  have hs : G.IsIndepSet s := (mem_filter.mp hmax.prop).2
  have hv : v ∈ s := hvs (by simp)
  have hdom : G.IsDominating s := by
    intro x
    by_contra! h
    have hext : insert x s ∈ A := by
      apply mem_filter.mpr ⟨mem_univ _,?_⟩
      intro a ha b hb hab had
      simp only [mem_coe, mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact hab rfl
      · exact h.2 b hb had
      · exact h.2 a ha had.symm
      · exact hs ha hb hab had
    exact h.1 (hmax.2 hext (subset_insert _ _) (mem_insert_self ..))
  have hsmall : G.indepDominationNumber ≤ s.card :=
    Nat.sInf_le (show ∃ D : Finset V, G.IsNIndepDominatingSet s.card D from ⟨s,hs,hdom,rfl⟩)
  have hd : Disjoint s (G.neighborFinset v) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    have had := (G.mem_neighborFinset v w).mp hw'
    exact hs hv hw had.ne had
  have hcard := (s ∪ G.neighborFinset v).card_le_univ
  rw [card_union_of_disjoint hd, card_neighborFinset_eq_degree] at hcard
  omega
end OMA.Temperature

open OMA.Temperature in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture3.conjecture3 := by
  intro V _ _ G _ _ hc
  classical
  obtain ⟨v,_,he⟩ := Finset.mem_image.mp
    (Finset.max'_mem (Finset.univ.image (temp_v G)) (Finset.image_nonempty.mpr Finset.univ_nonempty))
  have hv : temp_v G v = MaxTemp G := he
  rw [← hv]
  have hn := G.degree_lt_card_verts v
  have hn' : (0:ℝ) < Fintype.card V - (G.degree v : ℝ) := sub_pos.mpr (by exact_mod_cast hn)
  have hid : (G.indepDominationNumber : ℝ) + G.degree v ≤ Fintype.card V := by
    exact_mod_cast domination_bound (G := G) v
  apply le_trans _ (degree_le_leaves hc v)
  rw [temp_v, if_neg (Ne.symm hn.ne), ← mul_div_assoc, div_le_iff₀ hn']
  nlinarith [mul_le_mul_of_nonneg_right hid (Nat.cast_nonneg (α := ℝ) (G.degree v))]
