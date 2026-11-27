import OMAReductions.R_Erdos1182_erdos_1182_variants_befrs_lower_R1_H1_R1

-- Step Erdos1182.erdos_1182.variants.befrs_lower.R1.H1.R1.H1: hypothesis H1 of reduction Erdos1182.erdos_1182.variants.befrs_lower.R1.H1.R1
-- Credit: @dk8827
-- H1 := ∀ {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m)),     4 ≤ l → 2 * l - 1 ≤ m → G.Connected → C.CliqueFree 3 →     (∃ x, (G.neighborSet x).ncard = 1) →     ∃ H : SimpleGraph (Fin (l - 1)), H.Connected ∧       H.edgeSet.ncard + 1 ≤ G.edgeSet.ncard ∧ (H.IsContained Cᶜ → G.IsContained Cᶜ)  /-- Shortening a suspended path with adjacent degree-two vertices preserves the obstruction. If the two other endpoints coincide, replace the triangle by a leaf. -/

/-! Delete a leaf and extend a copy into the complement. -/

open SimpleGraph

lemma path_avoids_leaf {V : Type} {G : SimpleGraph V} {x a : V}
    (unique : ∀ u, G.Adj x u → u = a) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hu : u ≠ x) (hv : v ≠ x) :
    x ∉ p.support := by
  induction p with
  | nil => simpa using Ne.symm hu
  | @cons u w v huw p ih =>
    have hn := List.nodup_cons.mp (show (u :: p.support).Nodup from hp.support_nodup)
    have hw : w ≠ x := by
      intro he
      subst w
      cases p with
      | nil => exact hv rfl
      | @cons _ z _ hxz p =>
        have huz : u = z := (unique u huw.symm).trans (unique z hxz).symm
        have hz : z ∈ (Walk.cons hxz p).support := by simp
        exact hn.1 (by rw [huz]; exact hz)
    intro hx
    change x ∈ u :: p.support at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu rfl
    · exact ih (Walk.IsPath.mk' hn.2) hw hv hx

lemma leaf_embedding {l m : ℕ} (G : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m))
    (hlm : 2 * l - 1 ≤ m) (hC : C.CliqueFree 3)
    (x a : Fin l) (hxa : G.Adj x a) (unique : ∀ u, G.Adj x u → u = a)
    (U : Finset (Fin l)) (hU : U = Finset.univ.erase x)
    (hcopy : (G.induce (↑U : Set (Fin l))).IsContained Cᶜ) : G.IsContained Cᶜ := by
  classical
  by_cases hlarge : ∃ v : Fin m, l ≤ (C.neighborFinset v).card
  · obtain ⟨v, hv⟩ := hlarge
    obtain ⟨S, hS, hc⟩ := Finset.exists_subset_card_eq hv
    refine isContained_iff_exists_le_comap.mpr ⟨(S.orderEmbOfFin hc).toEmbedding, ?_⟩
    intro u w huw
    change Cᶜ.Adj (S.orderEmbOfFin hc u) (S.orderEmbOfFin hc w)
    rw [compl_adj]
    refine ⟨(S.orderEmbOfFin hc).injective.ne (G.ne_of_adj huw), ?_⟩
    intro hh
    have hu := (mem_neighborFinset C v _).mp (hS (S.orderEmbOfFin_mem hc u))
    have hw := (mem_neighborFinset C v _).mp (hS (S.orderEmbOfFin_mem hc w))
    exact hC _ (is3Clique_triple_iff.mpr ⟨hu, hw, hh⟩)
  have hu (u : Fin l) (hne : u ≠ x) : u ∈ U := by
    rw [hU]
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ u⟩
  obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp hcopy
  let A : ↥U := ⟨a, hu a (G.ne_of_adj hxa.symm)⟩
  let used : Finset (Fin m) := Finset.univ.map f
  let red := C.neighborFinset (f A)
  have hused : used.card = l - 1 := by
    simp only [used, Finset.card_map, Finset.card_univ]
    change Fintype.card ↥U = _
    rw [Fintype.card_coe, hU, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
  have hred : red.card < l := Nat.lt_of_not_ge (fun h => hlarge ⟨f A, h⟩)
  have hl : 0 < l := (Nat.zero_le x.val).trans_lt x.isLt
  have hc : (used ∪ red).card < (Finset.univ : Finset (Fin m)).card := by
    have hh := Finset.card_union_le used red
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨y, _, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hyne (u : ↥U) : y ≠ f u := fun eq => hy
    (Finset.mem_union_left _ (eq ▸ Finset.mem_map_of_mem f (Finset.mem_univ u)))
  have hya : Cᶜ.Adj y (f A) := (compl_adj C _ _).mpr ⟨hyne A, fun h => hy
    (Finset.mem_union_right _ ((mem_neighborFinset C (f A) y).mpr h.symm))⟩
  let g (u : Fin l) : Fin m := if h : u ≠ x then f ⟨u, hu u h⟩ else y
  have hgx : g x = y := dif_neg (not_not.mpr rfl)
  have hg (u : Fin l) (h : u ≠ x) : g u = f ⟨u, hu u h⟩ := dif_pos h
  refine isContained_iff_exists_le_comap.mpr ⟨⟨g, ?_⟩, ?_⟩
  · intro u w huw
    by_cases hux : u = x
    · subst u
      by_contra hw
      have hwx : w ≠ x := fun e => hw e.symm
      exact hyne ⟨w, hu w hwx⟩ (hgx.symm.trans (huw.trans (hg w hwx)))
    · by_cases hwx : w = x
      · subst w
        exact (hyne ⟨u, hu u hux⟩ (hgx.symm.trans (huw.symm.trans (hg u hux)))).elim
      · rw [hg u hux, hg w hwx] at huw
        exact congrArg Subtype.val (f.injective huw)
  · have preserve_from_x (u : Fin l) (h : G.Adj x u) : Cᶜ.Adj (g x) (g u) := by
      have hua := unique u h
      subst u
      rw [hgx, hg a (G.ne_of_adj hxa.symm)]
      exact hya
    intro u w huw
    change Cᶜ.Adj (g u) (g w)
    by_cases hux : u = x
    · subst u
      exact preserve_from_x w huw
    · by_cases hwx : w = x
      · subst w
        exact (preserve_from_x u huw.symm).symm
      · rw [hg u hux, hg w hwx]
        exact hf (show (G.induce (↑U : Set (Fin l))).Adj ⟨u, hu u hux⟩ ⟨w, hu w hwx⟩ from huw)

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1_H1_R1.H1 := by
  intro l m G C hl hm hG hC hex
  classical
  obtain ⟨x, hx⟩ := hex
  have hxdeg : G.degree x = 1 := by
    rw [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, coe_neighborFinset, hx]
  obtain ⟨a, hxa, uniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hxdeg
  let U := (Finset.univ : Finset (Fin l)).erase x
  have hcard : Fintype.card ↥U = l - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  let G' := G.induce (↑U : Set (Fin l))
  let A : ↥U := ⟨a, Finset.mem_erase.mpr ⟨G.ne_of_adj hxa.symm, Finset.mem_univ _⟩⟩
  have hconn : G'.Connected := by
    refine (connected_iff _).mpr ⟨?_, ⟨A⟩⟩
    intro u v
    obtain ⟨p, hp⟩ := (hG.preconnected u v).exists_isPath
    have ha (w : Fin l) (hw : w ∈ p.support) : w ∈ U :=
      Finset.mem_erase.mpr ⟨fun e => path_avoids_leaf uniq p hp
        (Finset.mem_erase.mp u.property).1 (Finset.mem_erase.mp v.property).1 (e ▸ hw),
        Finset.mem_univ _⟩
    exact ⟨p.induce (↑U : Set (Fin l)) ha⟩
  have hedge : G'.edgeSet.ncard + 1 ≤ G.edgeSet.ncard := by
    rw [← coe_edgeFinset, ← coe_edgeFinset (G := G), Set.ncard_coe_finset, Set.ncard_coe_finset]
    change (G.induce (↑U : Set (Fin l))).edgeFinset.card + 1 ≤ G.edgeFinset.card
    rw [← card_filter_edgeFinset_toFinset_subset]
    let E := G.edgeFinset.filter (fun e => e.toFinset ⊆ U)
    have hdis : Disjoint E (G.incidenceFinset x) := by
      apply Finset.disjoint_left.mpr
      intro e he hinc
      rw [incidenceFinset_eq_filter, Finset.mem_filter] at hinc
      have hxU := (Finset.mem_filter.mp he).2 (Sym2.mem_toFinset.mpr hinc.2)
      exact (Finset.mem_erase.mp hxU).1 rfl
    have hle : (E ∪ G.incidenceFinset x).card ≤ G.edgeFinset.card :=
      Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (G.incidenceFinset_subset x))
    rw [Finset.card_union_of_disjoint hdis, card_incidenceFinset_eq_degree, hxdeg] at hle
    exact hle
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let H := G'.comap e
  let i : H ≃g G' := { toEquiv := e, map_rel_iff' := Iff.rfl }
  refine ⟨H, i.connected_iff.mpr hconn, ?_, ?_⟩
  · have he : H.edgeSet.ncard = G'.edgeSet.ncard := by
      rw [← coe_edgeFinset, ← coe_edgeFinset (G := G'), Set.ncard_coe_finset, Set.ncard_coe_finset]
      exact i.card_edgeFinset_eq
    omega
  · intro hcopy
    exact leaf_embedding G C hm hC x a hxa uniq U rfl
      (IsContained.trans ⟨i.symm.toCopy⟩ hcopy)
