import OMAReductions.R_Erdos1182_erdos_1182_variants_befrs_lower_R1

/-! Reinsert low-degree vertices into a copy in the complement of a triangle-free graph. -/

open SimpleGraph

-- Step Erdos1182.erdos_1182.variants.befrs_lower.R1.H3: hypothesis H3 of reduction Erdos1182.erdos_1182.variants.befrs_lower.R1
-- Credit: @dk8827
-- H3 := ∀ {l m : ℕ} (H : SimpleGraph (Fin l)) (C : SimpleGraph (Fin m)),     C.CliqueFree 3 → 3 * l - 2 ≤ m →     ∀ (D : Finset (Fin l)), (∀ x ∈ D, (H.neighborSet x).ncard ≤ 2) →     (H.induce (↑Dᶜ : Set (Fin l))).IsContained Cᶜ → H.IsContained Cᶜ  /-- The standard complete bipartite obstruction. This argument adapts the project proof of the Ramsey lower bound by @ldy985. -/

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_befrs_lower_R1.H3 := by
  intro l m H C htriangle hm D hdeg hcopy
  classical
  by_cases hl : 0 < l
  swap
  · have : IsEmpty (Fin l) := ⟨fun v => by have := v.isLt; omega⟩
    exact IsContained.of_isEmpty
  have hmpos : 0 < m := by omega
  have neighborSet_card (x : Fin l) : (H.neighborFinset x).card = (H.neighborSet x).ncard := by
    rw [← Set.ncard_coe_finset, coe_neighborFinset]
  by_cases hlarge : ∃ v : Fin m, l ≤ (C.neighborFinset v).card
  · obtain ⟨v, hv⟩ := hlarge
    obtain ⟨W, hW, hcard⟩ := Finset.exists_subset_card_eq hv
    refine isContained_iff_exists_le_comap.mpr ⟨(W.orderEmbOfFin hcard).toEmbedding, ?_⟩
    intro u w huw
    change Cᶜ.Adj (W.orderEmbOfFin hcard u) (W.orderEmbOfFin hcard w)
    rw [compl_adj]
    refine ⟨(W.orderEmbOfFin hcard).injective.ne (H.ne_of_adj huw), ?_⟩
    intro hc
    have hvu := (mem_neighborFinset C v _).mp (hW (W.orderEmbOfFin_mem hcard u))
    have hvw := (mem_neighborFinset C v _).mp (hW (W.orderEmbOfFin_mem hcard w))
    exact htriangle _ (is3Clique_triple_iff.mpr ⟨hvu, hvw, hc⟩)
  have hsmall (v : Fin m) : (C.neighborFinset v).card ≤ l - 1 := by
    have hv : ¬ l ≤ (C.neighborFinset v).card := fun hv => hlarge ⟨v, hv⟩
    omega
  let Partial (U : Finset (Fin l)) (f : Fin l → Fin m) : Prop :=
    Set.InjOn f (↑U : Set (Fin l)) ∧
      ∀ x ∈ U, ∀ y ∈ U, H.Adj x y → Cᶜ.Adj (f x) (f y)
  have extend (E : Finset (Fin l)) : E ⊆ D →
      (∃ f, Partial Eᶜ f) → H.IsContained Cᶜ := by
    refine Finset.strongInductionOn E ?_
    intro E ih hED hpartial
    obtain ⟨f, hfinj, hfadj⟩ := hpartial
    by_cases hE : E.Nonempty
    swap
    · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
      subst E
      have hmem (x : Fin l) : x ∈ (∅ : Finset (Fin l))ᶜ := by simp
      refine isContained_iff_exists_le_comap.mpr ⟨⟨f, ?_⟩, ?_⟩
      · intro x y hxy
        exact hfinj (hmem x) (hmem y) hxy
      · intro x y hxy
        exact hfadj x (hmem x) y (hmem y) hxy
    obtain ⟨x, hx⟩ := hE
    let U := Eᶜ
    have hxu : x ∉ U := fun hp => (Finset.mem_compl.mp hp) hx
    have hU : U.card ≤ l - 1 := by
      have hlt := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr (show U ≠ Finset.univ from
        fun h => hxu (by rw [h]; exact Finset.mem_univ x)))
      rw [Finset.card_univ, Fintype.card_fin] at hlt
      omega
    let N := H.neighborFinset x ∩ U
    have hN : N.card ≤ 2 := by
      have hle : N.card ≤ (H.neighborFinset x).card :=
        Finset.card_le_card Finset.inter_subset_left
      rw [neighborSet_card] at hle
      exact hle.trans (hdeg x (hED hx))
    let used := U.image f
    let blocked := N.biUnion (fun u => C.neighborFinset (f u))
    have hb : blocked.card ≤ 2 * (l - 1) := by
      have hle : blocked.card ≤ N.card * (l - 1) :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun u _ => hsmall (f u))
      exact hle.trans (Nat.mul_le_mul_right _ hN)
    have hused : used.card ≤ l - 1 := Finset.card_image_le.trans hU
    have hunion : (used ∪ blocked).card < (Finset.univ : Finset (Fin m)).card := by
      have ht := Finset.card_union_le used blocked
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hunion
    have hvused : v ∉ used := fun hv' => hv (Finset.mem_union_left _ hv')
    have hvblocked : v ∉ blocked := fun hv' => hv (Finset.mem_union_right _ hv')
    have hvne (u : Fin l) (hu : u ∈ U) : v ≠ f u :=
      fun he => hvused (he ▸ Finset.mem_image_of_mem f hu)
    have hvadj (u : Fin l) (hu : u ∈ U) (hxu_adj : H.Adj x u) : Cᶜ.Adj v (f u) := by
      rw [compl_adj]
      refine ⟨hvne u hu, fun he => hvblocked ?_⟩
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_inter.mpr ⟨(mem_neighborFinset H x u).mpr hxu_adj, hu⟩,
        (mem_neighborFinset C (f u) v).mpr he.symm⟩
    apply ih (E.erase x) (Finset.erase_ssubset hx) ((Finset.erase_subset x E).trans hED)
    refine ⟨Function.update f x v, ?_⟩
    rw [Finset.compl_erase]
    change Partial (insert x U) _
    have hfupdate (u : Fin l) (hu : u ∈ U) : Function.update f x v u = f u :=
      Function.update_of_ne (show u ≠ x from fun h => hxu (h ▸ hu)) _ _
    constructor
    · intro u hu w hw he
      change u ∈ insert x U at hu
      change w ∈ insert x U at hw
      rcases Finset.mem_insert.mp hu with hux | hu'
      · subst u
        rcases Finset.mem_insert.mp hw with hwx | hw'
        · subst w
          rfl
        · rw [Function.update_self, hfupdate w hw'] at he
          exact (hvne w hw' he).elim
      · rcases Finset.mem_insert.mp hw with hwx | hw'
        · subst w
          rw [hfupdate u hu', Function.update_self] at he
          exact (hvne u hu' he.symm).elim
        · rw [hfupdate u hu', hfupdate w hw'] at he
          exact hfinj hu' hw' he
    · intro u hu w hw he
      rcases Finset.mem_insert.mp hu with hux | hu'
      · subst u
        rcases Finset.mem_insert.mp hw with hwx | hw'
        · subst w
          exact (H.loopless.irrefl _ he).elim
        · rw [Function.update_self, hfupdate w hw']
          exact hvadj w hw' he
      · rcases Finset.mem_insert.mp hw with hwx | hw'
        · subst w
          rw [hfupdate u hu', Function.update_self]
          exact (hvadj u hu' he.symm).symm
        · rw [hfupdate u hu', hfupdate w hw']
          exact hfadj u hu' w hw' he
  apply extend D Finset.Subset.rfl
  obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp hcopy
  let f' (u : Fin l) : Fin m := if hu : u ∈ Dᶜ then f ⟨u, hu⟩ else ⟨0, hmpos⟩
  have hf' (u : Fin l) (hu : u ∈ Dᶜ) : f' u = f ⟨u, hu⟩ := dif_pos hu
  refine ⟨f', ?_, ?_⟩
  · intro u hu w hw he
    rw [hf' u hu, hf' w hw] at he
    exact congrArg Subtype.val (f.injective he)
  · intro u hu w hw he
    rw [hf' u hu, hf' w hw]
    exact hf (show (H.induce (↑Dᶜ : Set (Fin l))).Adj ⟨u, hu⟩ ⟨w, hw⟩ from he)
