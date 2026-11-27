import OMAReductions.R_Erdos1182_erdos_1182_variants_befrs_lower_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The linear Ramsey bound follows by deleting a minimum-degree vertex and extending the copy. -/

open SimpleGraph

-- Step Erdos1182.erdos_1182.variants.befrs_lower.R1.H2: hypothesis H2 of reduction Erdos1182.erdos_1182.variants.befrs_lower.R1
-- Credit: @dk8827
-- H2 := ∀ (V : Type) [Fintype V] (H : SimpleGraph V) {m : ℕ} (C : SimpleGraph (Fin m)),     C.CliqueFree 3 → Fintype.card V + 2 * H.edgeSet.ncard ≤ m → H.IsContained Cᶜ  /-- When the host has at least `3 * l - 2` vertices, a blue copy of the induced graph with low-degree vertices removed extends to a blue copy of the graph. A red neighborhood of size at least `l` can also give a full blue copy directly. -/

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1.H2 := by
  intro V _ H m C htriangle hm
  classical
  have embeds : ∀ l (W : Type) [Fintype W] (G : SimpleGraph W),
      Fintype.card W = l → l + 2 * G.edgeSet.ncard ≤ m → G.IsContained Cᶜ := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      intro W _ G hcard hsize
      by_cases h0 : l = 0
      · have : IsEmpty W := Fintype.card_eq_zero_iff.mp (hcard.trans h0)
        exact IsContained.of_isEmpty
      have hl : 0 < l := Nat.pos_of_ne_zero h0
      have : Nonempty W := Fintype.card_pos_iff.mp (hcard ▸ hl)
      by_cases hlarge : ∃ v : Fin m, l ≤ (C.neighborFinset v).card
      · obtain ⟨v, hv⟩ := hlarge
        obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hv
        let f := (Fintype.equivFinOfCardEq hcard).toEmbedding.trans (S.orderEmbOfFin hScard).toEmbedding
        refine isContained_iff_exists_le_comap.mpr ⟨f, ?_⟩
        intro u w huw
        change Cᶜ.Adj (f u) (f w)
        rw [compl_adj]
        refine ⟨f.injective.ne (G.ne_of_adj huw), ?_⟩
        intro hc
        have hvu := (mem_neighborFinset C v _).mp (hS (S.orderEmbOfFin_mem hScard (Fintype.equivFinOfCardEq hcard u)))
        have hvw := (mem_neighborFinset C v _).mp (hS (S.orderEmbOfFin_mem hScard (Fintype.equivFinOfCardEq hcard w)))
        exact htriangle _ (is3Clique_triple_iff.mpr ⟨hvu, hvw, hc⟩)
      have hsmall (v : Fin m) : (C.neighborFinset v).card ≤ l - 1 := by
        have hh : ¬ l ≤ (C.neighborFinset v).card := fun h => hlarge ⟨v, h⟩
        omega
      obtain ⟨x, hx⟩ := G.exists_minimal_degree_vertex
      have he : G.edgeFinset.card = G.edgeSet.ncard := by
        rw [← coe_edgeFinset, Set.ncard_coe_finset]
      have hd : G.degree x * (l - 1) ≤ 2 * G.edgeSet.ncard := by
        calc
          _ ≤ G.degree x * l := Nat.mul_le_mul_left _ (Nat.sub_le ..)
          _ = ∑ _ : W, G.degree x := by simp [hcard, Nat.mul_comm]
          _ ≤ ∑ u : W, G.degree u := Finset.sum_le_sum fun u _ => hx ▸ G.minDegree_le_degree u
          _ = _ := G.sum_degrees_eq_twice_card_edges.trans (by rw [he])
      let U : Finset W := Finset.univ.erase x
      have hU : Fintype.card ↥U = l - 1 := by
        rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]
      have hG' : (G.induce (↑U : Set W)).edgeSet.ncard ≤ G.edgeSet.ncard := by
        rw [← coe_edgeFinset, ← coe_edgeFinset (G := G), Set.ncard_coe_finset, Set.ncard_coe_finset]
        rw [← card_filter_edgeFinset_toFinset_subset]
        exact Finset.card_filter_le _ _
      obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp
        (ih (l - 1) (by omega) ↥U (G.induce (↑U : Set W)) hU (by omega))
      let near : Finset U := Finset.univ.filter (fun u : U => G.Adj x u)
      have hnear : near.card ≤ G.degree x := by
        rw [← card_neighborFinset_eq_degree]
        let incl : U ↪ W := ⟨Subtype.val, Subtype.val_injective⟩
        rw [← Finset.card_map incl]
        apply Finset.card_le_card
        intro u hu
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hu
        exact (mem_neighborFinset G x _).mpr (Finset.mem_filter.mp hw).2
      let used : Finset (Fin m) := Finset.univ.map f
      let blocked := near.biUnion (fun u => C.neighborFinset (f u))
      have hused : used.card = l - 1 := by
        simp only [used, Finset.card_map, Finset.card_univ, hU]
      have hb : blocked.card ≤ 2 * G.edgeSet.ncard :=
        (Finset.card_biUnion_le_card_mul _ _ _ (fun u _ => hsmall (f u))).trans
          ((Nat.mul_le_mul_right _ hnear).trans hd)
      have hunion : (used ∪ blocked).card < (Finset.univ : Finset (Fin m)).card := by
        have ht := Finset.card_union_le used blocked
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hunion
      have hvne (u : U) : v ≠ f u := fun h => hv (Finset.mem_union_left _ (by
        rw [h]
        exact Finset.mem_map_of_mem f (Finset.mem_univ u)))
      have hvadj (u : U) (hu : G.Adj x u) : Cᶜ.Adj v (f u) := by
        rw [compl_adj]
        refine ⟨hvne u, fun had => hv (Finset.mem_union_right _ ?_)⟩
        exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩,
          (mem_neighborFinset C (f u) v).mpr had.symm⟩
      have hmem (u : W) (hu : u ≠ x) : u ∈ U := Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩
      let g (u : W) : Fin m := if hu : u ≠ x then f ⟨u, hmem u hu⟩ else v
      have hgx : g x = v := dif_neg (not_not.mpr rfl)
      have hg (u : W) (hu : u ≠ x) : g u = f ⟨u, hmem u hu⟩ := dif_pos hu
      refine isContained_iff_exists_le_comap.mpr ⟨⟨g, ?_⟩, ?_⟩
      · intro u w huw
        by_cases hu : u = x
        · subst u
          by_contra hw
          have hwx : w ≠ x := fun he => hw he.symm
          exact hvne ⟨w, hmem w hwx⟩ (hgx.symm.trans (huw.trans (hg w hwx)))
        · by_cases hw : w = x
          · subst w
            exact (hvne ⟨u, hmem u hu⟩ (hgx.symm.trans (huw.symm.trans (hg u hu)))).elim
          · rw [hg u hu, hg w hw] at huw
            exact congrArg Subtype.val (f.injective huw)
      · intro u w huw
        change Cᶜ.Adj (g u) (g w)
        by_cases hu : u = x
        · subst u
          have hw := (G.ne_of_adj huw).symm
          rw [hgx, hg w hw]
          exact hvadj ⟨w, hmem w hw⟩ huw
        · by_cases hw : w = x
          · subst w
            rw [hg u hu, hgx]
            exact (hvadj ⟨u, hmem u hu⟩ huw.symm).symm
          · rw [hg u hu, hg w hw]
            exact hf (show (G.induce (↑U : Set W)).Adj ⟨u, hmem u hu⟩ ⟨w, hmem w hw⟩ from huw)
  exact embeds (Fintype.card V) V H rfl hm
