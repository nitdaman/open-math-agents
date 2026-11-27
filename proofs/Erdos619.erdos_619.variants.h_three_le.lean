import FormalConjectures.ErdosProblems.«619»

/-!
# The diameter-three extension bound for triangle-free graphs

The construction follows Erdős, Gyárfás and Ruszinkó, Combinatorica 18 (1998), Theorem 4.2.
-/

-- Credit: @amp2600

open SimpleGraph

namespace OMA.Erdos619Extension

lemma exists_independent_dominating_subset {V : Type*} (G : SimpleGraph V) (A : Finset V) :
    ∃ S : Finset V, S ⊆ A ∧ (S : Set V).Pairwise (fun a b => ¬ G.Adj a b) ∧
      ∀ a ∈ A, a ∈ S ∨ ∃ b ∈ S, G.Adj b a := by
  classical
  let candidates : Finset (Finset V) := A.powerset.filter fun S =>
    (S : Set V).Pairwise (fun a b => ¬ G.Adj a b)
  have hnonempty : candidates.Nonempty := ⟨∅, by simp [candidates]⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image candidates Finset.card hnonempty
  have hall : S ⊆ A ∧ (S : Set V).Pairwise (fun a b => ¬ G.Adj a b) := by
    simpa [candidates] using hS
  refine ⟨S, hall.1, hall.2, ?_⟩
  intro a ha
  by_cases hmem : a ∈ S
  · exact Or.inl hmem
  right
  by_contra hnone
  have hpair : ((insert a S : Finset V) : Set V).Pairwise (fun x y => ¬ G.Adj x y) := by
    rw [Finset.coe_insert, Set.pairwise_insert]
    refine ⟨hall.2, fun b hb _ => ⟨?_, ?_⟩⟩
    · exact fun hab => hnone ⟨b, hb, hab.symm⟩
    · exact fun hba => hnone ⟨b, hb, hba⟩
  have hinsert : insert a S ∈ candidates := by
    simpa [candidates] using And.intro (Finset.insert_subset ha hall.1) hpair
  have hcard := hmax (insert a S) hinsert
  rw [Finset.card_insert_of_notMem hmem] at hcard
  omega

lemma exists_star_extension {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (p : V) (S : Finset V) (hfar : ∀ s ∈ S, 2 < G.edist p s)
    (hindependent : (S : Set V).Pairwise (fun a b => ¬ G.Adj a b)) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧ (H \ G).edgeSet.ncard ≤ S.card ∧
      ∀ s ∈ S, H.Adj p s := by
  classical
  let edges := (fun s : V => s(p, s)) '' (S : Set V)
  let star := SimpleGraph.fromEdgeSet edges
  let H := G ⊔ star
  have hne (s : V) (hs : s ∈ S) : p ≠ s := by
    intro h
    subst s
    simpa using hfar p hs
  have hstar {a b : V} : star.Adj a b ↔ (a = p ∧ b ∈ S) ∨ (b = p ∧ a ∈ S) := by
    change (SimpleGraph.fromEdgeSet edges).Adj a b ↔ _
    rw [SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨⟨v, hv, he⟩, _⟩
      rcases Sym2.eq_iff.mp he with ⟨hpa, hvb⟩ | ⟨hpb, hva⟩
      · exact Or.inl ⟨hpa.symm, hvb ▸ hv⟩
      · exact Or.inr ⟨hpb.symm, hva ▸ hv⟩
    · rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
      · exact ⟨⟨b, hb, rfl⟩, hne b hb⟩
      · exact ⟨⟨a, ha, Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩, (hne a ha).symm⟩
  have hnoTriangle {s x : V} (hs : s ∈ S) (hsx : H.Adj s x) (hxp : H.Adj x p) : False := by
    have hsxG : G.Adj s x := by
      rcases (sup_adj G star s x).mp hsx with h | h
      · exact h
      · rcases hstar.mp h with ⟨hsp, _⟩ | ⟨hxp', _⟩
        · exact (hne s hs hsp.symm).elim
        · exact (hxp.ne hxp').elim
    rcases (sup_adj G star x p).mp hxp with h | h
    · apply (hfar s hs).not_ge
      calc
        G.edist p s ≤ G.edist p x + G.edist x s := G.edist_triangle
        _ = 2 := by rw [edist_eq_one_iff_adj.mpr h.symm, edist_eq_one_iff_adj.mpr hsxG.symm]; decide
    · have hx : x ∈ S := ((hstar.mp h).resolve_left fun hh => hxp.ne hh.1).2
      exact hindependent hs hx hsxG.ne hsxG
  have hnewTriangle {a b c : V} (hab : star.Adj a b)
      (hbc : H.Adj b c) (hca : H.Adj c a) : False := by
    rcases hstar.mp hab with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
    · exact hnoTriangle hb hbc hca
    · exact hnoTriangle ha hca.symm hbc.symm
  refine ⟨H, le_sup_left, ?_, ?_, fun s hs => (sup_adj G star p s).mpr
    (Or.inr (hstar.mpr (Or.inl ⟨rfl, hs⟩)))⟩
  · intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := is3Clique_iff.mp ht
    rcases (sup_adj G star a b).mp hab with habG | habStar
    · rcases (sup_adj G star a c).mp hac with hacG | hacStar
      · rcases (sup_adj G star b c).mp hbc with hbcG | hbcStar
        · exact hG {a, b, c} (is3Clique_triple_iff.mpr ⟨habG, hacG, hbcG⟩)
        · exact hnewTriangle hbcStar hac.symm hab
      · exact hnewTriangle hacStar hbc.symm hab.symm
    · exact hnewTriangle habStar hbc hac.symm
  · calc
      (H \ G).edgeSet.ncard ≤ edges.ncard := by
        refine Set.ncard_le_ncard ?_ ((Finset.finite_toSet S).image (fun v : V => s(p, v)))
        dsimp only [H, star]
        rw [edgeSet_sdiff, edgeSet_sup, edgeSet_fromEdgeSet]
        intro e he
        exact (he.1.resolve_left he.2).1
      _ ≤ S.card := by
        simpa only [edges, Set.ncard_coe_finset] using
          (Set.ncard_image_le (f := fun s : V => s(p, s)) (s := (S : Set V)))

-- Induct on the vertices that still need to be brought within distance three of each other.
lemma exists_bounded_extension {V : Type*} [Fintype V] (U : Finset V) (G : SimpleGraph V)
    (hG : G.CliqueFree 3) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧ (H \ G).edgeSet.ncard ≤ U.card ∧
      ∀ x ∈ U, ∀ y ∈ U, H.edist x y ≤ 3 := by
  classical
  induction U using Finset.strongInductionOn generalizing G with
  | _ U ih =>
    by_cases hU : U.Nonempty
    · obtain ⟨p, hp⟩ := hU
      let A := U.filter fun y => 2 < G.edist p y
      obtain ⟨S, hSA, hS, hdom⟩ := exists_independent_dominating_subset G A
      have hfar (y : V) (hy : y ∈ S) : 2 < G.edist p y := (Finset.mem_filter.mp (hSA hy)).2
      obtain ⟨K, hGK, hK, hcostK, hAdj⟩ := exists_star_extension G hG p S hfar hS
      let T := insert p S
      let R := U \ T
      have hTU : T ⊆ U := Finset.insert_subset hp (hSA.trans (Finset.filter_subset _ _))
      have hR : R ⊂ U := Finset.sdiff_ssubset hTU ⟨p, Finset.mem_insert_self p S⟩
      obtain ⟨H, hKH, hH, hcostH, hcloseR⟩ := ih R hR K hK
      have hcenter (y : V) (hy : y ∈ U) : K.edist p y ≤ 2 := by
        by_cases hya : 2 < G.edist p y
        · rcases hdom y (Finset.mem_filter.mpr ⟨hy, hya⟩) with hyS | ⟨s, hs, hsy⟩
          · rw [edist_eq_one_iff_adj.mpr (hAdj y hyS)]
            decide
          · calc
              K.edist p y ≤ K.edist p s + K.edist s y := K.edist_triangle
              _ = 2 := by
                rw [edist_eq_one_iff_adj.mpr (hAdj s hs), edist_eq_one_iff_adj.mpr (hGK hsy)]
                decide
        · exact (edist_anti hGK).trans (le_of_not_gt hya)
      have hblock (x : V) (hx : x ∈ T) : K.edist x p ≤ 1 := by
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · simp
        · exact edist_le_one_iff_adj_or_eq.mpr (Or.inl (hAdj x hxS).symm)
      have hcloseT (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ U) : H.edist x y ≤ 3 := by
        calc
          H.edist x y ≤ K.edist x y := edist_anti hKH
          _ ≤ K.edist x p + K.edist p y := K.edist_triangle
          _ ≤ 1 + 2 := add_le_add (hblock x hx) (hcenter y hy)
          _ = 3 := by decide
      refine ⟨H, hGK.trans hKH, hH, ?_, ?_⟩
      · have hedges : (H \ G).edgeSet ⊆ (H \ K).edgeSet ∪ (K \ G).edgeSet := by
          simp only [edgeSet_sdiff]
          intro e he
          by_cases hek : e ∈ K.edgeSet
          · exact Or.inr ⟨hek, he.2⟩
          · exact Or.inl ⟨he.1, hek⟩
        calc
          (H \ G).edgeSet.ncard ≤ ((H \ K).edgeSet ∪ (K \ G).edgeSet).ncard :=
            Set.ncard_le_ncard hedges
          _ ≤ (H \ K).edgeSet.ncard + (K \ G).edgeSet.ncard := Set.ncard_union_le _ _
          _ ≤ R.card + S.card := Nat.add_le_add hcostH hcostK
          _ ≤ U.card := by
            change (U \ T).card + S.card ≤ U.card
            rw [Finset.card_sdiff_of_subset hTU]
            have hSCard := Finset.card_le_card (Finset.subset_insert p S)
            have hTCard := Finset.card_le_card hTU
            change S.card ≤ T.card at hSCard
            omega
      · intro x hx y hy
        by_cases hxT : x ∈ T
        · exact hcloseT x hxT y hy
        by_cases hyT : y ∈ T
        · rw [edist_comm]
          exact hcloseT y hyT x hx
        exact hcloseR x (Finset.mem_sdiff.mpr ⟨hx, hxT⟩) y (Finset.mem_sdiff.mpr ⟨hy, hyT⟩)
    · refine ⟨G, le_rfl, hG, by simp, ?_⟩
      exact fun x hx => (hU ⟨x, hx⟩).elim

end OMA.Erdos619Extension

theorem OMA.solution : type_of% @Erdos619.erdos_619.variants.h_three_le := by
  intro V inst G _ hG
  obtain ⟨H, hGH, hH, hbudget, hclose⟩ :=
    OMA.Erdos619Extension.exists_bounded_extension Finset.univ G hG
  have hdiam : H.ediam ≤ 3 := ediam_le_iff.mpr fun u v => hclose u (by simp) v (by simp)
  have hmin : Erdos619.minNewEdges 3 G ≤ (H \ G).edgeSet.ncard := by
    unfold Erdos619.minNewEdges
    exact Nat.sInf_le ⟨H, hGH, hH, hdiam, rfl⟩
  exact hmin.trans (by simpa using hbudget)
