import FormalConjectures.ErdosProblems.«1079»
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
At a maximum-degree vertex of degree d, the edges meeting the complement of the
neighborhood number at most d times the number of vertices outside the neighborhood.
Joining a smaller Turán graph to an independent set gives the matching extremal comparison.
-/

open SimpleGraph Finset Finset.Nat
open scoped BigOperators

private lemma edgeCount_compl_add {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  have hdis : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← edgeFinset_inf, ← edgeFinset_bot, edgeFinset_inj]
    exact inf_compl_eq_bot
  have htop : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    rw [← edgeFinset_sup, edgeFinset_inj]
    exact sup_compl_eq_top
  rw [← card_union_of_disjoint hdis, htop, card_edgeFinset_top_eq_card_choose_two]

private lemma choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  rw [Nat.add_choose_eq, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ]
  omega

private lemma ext_join (a b q : ℕ) (hq : 0 < q) :
    extremalNumber a (completeGraph (Fin (q + 1))) + a * b ≤
      extremalNumber (a + b) (completeGraph (Fin (q + 2))) := by
  classical
  let T := turanGraph a q
  let J := Tᶜ ⊕g (⊤ : SimpleGraph (Fin b))
  let color : Fin a ⊕ Fin b → Fin (q + 1)
    | .inl x => ⟨x.val % q, (Nat.mod_lt _ hq).trans (Nat.lt_succ_self q)⟩
    | .inr _ => ⟨q, Nat.lt_succ_self q⟩
  have hcol : Jᶜ.Colorable (q + 1) := by
    refine ⟨Coloring.mk color ?_⟩
    rintro (x | x) (y | y) hxy hc
    · have h : x ≠ y ∧ (x ≠ y → T.Adj x y) := by simpa [J, compl_adj] using hxy
      exact (turanGraph_adj.mp (h.2 h.1)) (congrArg Fin.val hc)
    · have hc' : x.val % q = q := congrArg Fin.val hc
      exact (Nat.ne_of_lt (Nat.mod_lt _ hq)) hc'
    · have hc' : q = y.val % q := congrArg Fin.val hc
      exact (Nat.ne_of_lt (Nat.mod_lt _ hq)) hc'.symm
    · simp [J, compl_adj] at hxy
  have hcf := hcol.cliqueFree (show q + 1 < q + 2 by omega)
  have hfree : (completeGraph (Fin (q + 2))).Free Jᶜ := by
    change (⊤ : SimpleGraph (Fin (q + 2))).Free Jᶜ
    rw [← cliqueFree_iff_top_free, Fintype.card_fin]
    exact hcf
  have hJle := card_edgeFinset_le_extremalNumber hfree
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hJle
  have hJcount : J.edgeFinset.card =
      Tᶜ.edgeFinset.card + (⊤ : SimpleGraph (Fin b)).edgeFinset.card := by
    simp only [edgeFinset_card]
    exact (Fintype.card_congr (edgeSetSumEquiv (G := Tᶜ)
      (H := (⊤ : SimpleGraph (Fin b))))).trans Fintype.card_sum
  have ht := edgeCount_compl_add T
  have hj := edgeCount_compl_add J
  rw [hJcount, card_edgeFinset_top_eq_card_choose_two, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin, choose_two_add] at hj
  rw [Fintype.card_fin] at ht
  have hcard : Jᶜ.edgeFinset.card = T.edgeFinset.card + a * b := by omega
  have : Nontrivial (Fin (q + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by simpa using (show 1 < q + 1 by omega))
  have hex : extremalNumber a (completeGraph (Fin (q + 1))) = T.edgeFinset.card := by
    change extremalNumber a (⊤ : SimpleGraph (Fin (q + 1))) = _
    rw [extremalNumber_top, Fintype.card_fin, Nat.add_sub_cancel]
  rwa [hcard, ← hex] at hJle

private lemma edges_split {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (hd : ∀ w, G.degree w ≤ G.degree v) :
    G.edgeSet.ncard ≤ {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard +
      (Fintype.card V - G.degree v) * G.degree v := by
  classical
  let inside : Finset (Sym2 V) := G.edgeFinset.filter fun e => ∀ x ∈ e, G.Adj v x
  let outside : Finset (Sym2 V) := G.edgeFinset.filter fun e => ¬ ∀ x ∈ e, G.Adj v x
  let far : Finset V := Finset.univ.filter fun w => ¬ G.Adj v w
  have hfar : far.card = Fintype.card V - G.degree v := by
    have hpart := card_filter_add_card_filter_not (s := (univ : Finset V)) (G.Adj v)
    rw [← G.neighborFinset_eq_filter, card_neighborFinset_eq_degree, card_univ] at hpart
    change G.degree v + far.card = Fintype.card V at hpart
    omega
  have hsub : outside ⊆ far.biUnion (fun w => G.incidenceFinset w) := by
    intro e he
    obtain ⟨heG, heout⟩ := mem_filter.mp he
    push Not at heout
    obtain ⟨w, hw, hnadj⟩ := heout
    refine mem_biUnion.mpr ⟨w, mem_filter.mpr ⟨mem_univ _, hnadj⟩, ?_⟩
    rw [G.incidenceFinset_eq_filter]
    exact mem_filter.mpr ⟨heG, hw⟩
  have hbound : outside.card ≤ far.card * G.degree v := by
    calc
      outside.card ≤ (far.biUnion (fun w => G.incidenceFinset w)).card := card_le_card hsub
      _ ≤ ∑ w ∈ far, (G.incidenceFinset w).card := card_biUnion_le
      _ ≤ ∑ _w ∈ far, G.degree v := by
        apply sum_le_sum
        intro w _
        rw [card_incidenceFinset_eq_degree]
        exact hd w
      _ = far.card * G.degree v := by simp
  have hpart := card_filter_add_card_filter_not
    (s := G.edgeFinset) (fun e => ∀ x ∈ e, G.Adj v x)
  change inside.card + outside.card = G.edgeFinset.card at hpart
  have hinside :
      inside.card = {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext e
    simp [inside]
  have hG : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [← hG, ← hinside, ← hpart, ← hfar]
  exact Nat.add_le_add_left hbound _

theorem OMA.solution : type_of% @Erdos1079.erdos_1079 := by
  intro r hr
  refine ⟨1 / 3, by norm_num, ?_⟩
  intro n hn G hG
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  let d := G.degree v
  have hd (w : Fin n) : G.degree w ≤ d := by
    rw [show d = G.maxDegree from hv.symm]
    exact G.degree_le_maxDegree w
  have hdn : d ≤ n := by
    simpa [d] using (show G.degree v ≤ Fintype.card (Fin n) from by
      rw [← card_neighborFinset_eq_degree, ← card_univ]
      exact card_le_card (subset_univ _))
  have hjoin (a : ℕ) (ha : a ≤ n) :
      extremalNumber a (completeGraph (Fin (r - 1))) + a * (n - a) ≤
        extremalNumber n (completeGraph (Fin r)) := by
    have hb := ext_join a (n - a) (r - 2) (by omega)
    rwa [Nat.add_sub_of_le ha, show r - 2 + 1 = r - 1 by omega,
      show r - 2 + 2 = r by omega] at hb
  have hsplit := edges_split G v hd
  rw [Fintype.card_fin] at hsplit
  refine ⟨v, ?_, ?_⟩
  · let a := n / 2
    have han : a ≤ n := by dsimp [a]; omega
    have hlow : a * (n - a) ≤ G.edgeSet.ncard :=
      (Nat.le_add_left _ _).trans ((hjoin a han).trans hG)
    have hsum : 2 * G.edgeSet.ncard ≤ n * d := by
      have h := G.sum_degrees_eq_twice_card_edges
      rw [← Set.ncard_coe_finset, coe_edgeFinset] at h
      rw [← h]
      calc
        (∑ w : Fin n, G.degree w) ≤ ∑ _w : Fin n, d :=
          sum_le_sum (fun w _ => hd w)
        _ = n * d := by simp
    have hmul : n * n ≤ (3 * a) * (2 * (n - a)) := by
      apply Nat.mul_le_mul <;> dsimp [a] <;> omega
    have hmul' : n * n ≤ 6 * (a * (n - a)) := by nlinarith
    have hnd : n ≤ 3 * d := by
      apply Nat.le_of_mul_le_mul_left (c := n) _ (by omega)
      nlinarith
    change (1 / 3 : ℝ) * n ≤ (d : ℝ)
    have hz : (n : ℝ) ≤ 3 * (d : ℝ) := by exact_mod_cast hnd
    linarith
  · have hh := (hjoin d hdn).trans (hG.trans hsplit)
    dsimp [d] at hh
    rw [Nat.mul_comm (n - G.degree v) (G.degree v)] at hh
    exact Nat.le_of_add_le_add_right hh