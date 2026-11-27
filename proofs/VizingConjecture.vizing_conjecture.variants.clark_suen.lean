import FormalConjectures.Wikipedia.VizingConjecture

/-! The Clark–Suen inequality `γ(G) γ(H) ≤ 2 γ(G □ H)`, by the original double counting.
Fix a minimum dominating set `U` of `G` and send each vertex `x` of `G` to a dominator
`c x ∈ U`. For `u ∈ U` let `P u` be the projection to `H` of the part of `D` lying over the cell
of `u`, and `Q u` the vertices of `H` not dominated by `P u`. Then `|P u| + |Q u| ≥ γ(H)`,
`∑ |P u| ≤ |D|` and `∑ |Q u| ≤ |D|`. -/

open SimpleGraph

namespace OMA

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The projection to `H` of the part of `D` over the cell of `u`. -/
def cP (D : Finset (α × β)) (c : α → α) (u : α) : Finset β :=
  (D.filter (fun p => c p.1 = u)).image Prod.snd

/-- The vertices of `H` which `cP D c u` does not dominate. -/
def cQ (H : SimpleGraph β) [DecidableRel H.Adj] (D : Finset (α × β)) (c : α → α) (u : α) :
    Finset β :=
  Finset.univ.filter (fun y => y ∉ cP D c u ∧ ∀ z ∈ cP D c u, ¬ H.Adj y z)

lemma step1 (H : SimpleGraph β) [DecidableRel H.Adj] (D : Finset (α × β)) (c : α → α) (u : α) :
    H.dominationNumber ≤ (cP D c u).card + (cQ H D c u).card := by
  have hdom : H.IsDominating (↑(cP D c u ∪ cQ H D c u) : Set β) := by
    intro y
    by_cases h1 : y ∈ cP D c u
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left _ h1))
    · by_cases h2 : ∃ z ∈ cP D c u, H.Adj y z
      · obtain ⟨z, hz, hyz⟩ := h2
        exact Or.inr ⟨z, Finset.mem_coe.mpr (Finset.mem_union_left _ hz), hyz⟩
      · refine Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right _ ?_))
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, ?_⟩
        intro z hz hyz
        exact h2 ⟨z, hz, hyz⟩
  exact (dominationNumber_le_of_isDominating H _ hdom).trans (Finset.card_union_le _ _)

lemma step2 (D : Finset (α × β)) (c : α → α) (U : Finset α) (hcU : ∀ x, c x ∈ U) :
    ∑ u ∈ U, (cP D c u).card ≤ D.card := by
  have h : D.card = ∑ u ∈ U, (D.filter (fun p => c p.1 = u)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => hcU p.1)
  rw [h]
  exact Finset.sum_le_sum (fun u _ => Finset.card_image_le)

lemma step3_aux (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel H.Adj]
    (D : Finset (α × β)) (hD : (G □ H).IsDominating (D : Set (α × β))) (U : Finset α)
    (hUmin : G.dominationNumber = U.card) (c : α → α) (hcU : ∀ x, c x ∈ U)
    (hcA : ∀ x, x = c x ∨ G.Adj x (c x)) (y : β) :
    (U.filter (fun u => y ∈ cQ H D c u)).card ≤ (D.filter (fun p => p.2 = y)).card := by
  have hdom : G.IsDominating
      (↑((D.filter (fun p => p.2 = y)).image Prod.fst ∪
        (U \ U.filter (fun u => y ∈ cQ H D c u))) : Set α) := by
    intro x
    by_cases hx : c x ∈ U.filter (fun u => y ∈ cQ H D c u)
    · have hy : y ∈ cQ H D c (c x) := (Finset.mem_filter.mp hx).2
      obtain ⟨-, hyP, hyA⟩ := Finset.mem_filter.mp hy
      rcases hD (x, y) with h | ⟨⟨w, z⟩, hw, hadj⟩
      · exfalso
        apply hyP
        exact Finset.mem_image.mpr
          ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_coe.mp h, rfl⟩, rfl⟩
      · rw [boxProd_adj] at hadj
        rcases hadj with ⟨hxw, hyz⟩ | ⟨hyz, hxw⟩
        · have hyz' : y = z := hyz
          have hxw' : G.Adj x w := hxw
          refine Or.inr ⟨w, Finset.mem_coe.mpr (Finset.mem_union_left _ ?_), hxw'⟩
          exact Finset.mem_image.mpr
            ⟨(w, z), Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hw, hyz'.symm⟩, rfl⟩
        · exfalso
          have hxw' : x = w := hxw
          have hyz' : H.Adj y z := hyz
          have hz : z ∈ cP D c (c x) := by
            refine Finset.mem_image.mpr
              ⟨(w, z), Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hw, ?_⟩, rfl⟩
            change c w = c x
            rw [hxw']
          exact hyA z hz hyz'
    · have hmem : c x ∈ U \ U.filter (fun u => y ∈ cQ H D c u) :=
        Finset.mem_sdiff.mpr ⟨hcU x, hx⟩
      rcases hcA x with h | h
      · refine Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right _ ?_))
        have e : (x ∈ U \ U.filter (fun u => y ∈ cQ H D c u)) =
            (c x ∈ U \ U.filter (fun u => y ∈ cQ H D c u)) := congrArg (fun t => t ∈ _) h
        rw [e]
        exact hmem
      · exact Or.inr ⟨c x, Finset.mem_coe.mpr (Finset.mem_union_right _ hmem), h⟩
  have h1 := dominationNumber_le_of_isDominating G _ hdom
  have h2 := Finset.card_union_le ((D.filter (fun p => p.2 = y)).image Prod.fst)
    (U \ U.filter (fun u => y ∈ cQ H D c u))
  have h3 := Finset.card_sdiff_add_card_eq_card
    (Finset.filter_subset (fun u => y ∈ cQ H D c u) U)
  have h4 : ((D.filter (fun p => p.2 = y)).image Prod.fst).card ≤
      (D.filter (fun p => p.2 = y)).card := Finset.card_image_le
  omega

lemma step3 (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel H.Adj]
    (D : Finset (α × β)) (hD : (G □ H).IsDominating (D : Set (α × β))) (U : Finset α)
    (hUmin : G.dominationNumber = U.card) (c : α → α) (hcU : ∀ x, c x ∈ U)
    (hcA : ∀ x, x = c x ∨ G.Adj x (c x)) :
    ∑ u ∈ U, (cQ H D c u).card ≤ D.card := by
  have e1 : ∀ u, (cQ H D c u).card = ∑ y : β, if y ∈ cQ H D c u then 1 else 0 := by
    intro u
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp
  have e2 : ∑ u ∈ U, (cQ H D c u).card =
      ∑ y : β, (U.filter (fun u => y ∈ cQ H D c u)).card := by
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.card_filter]
  have e3 : D.card = ∑ y : β, (D.filter (fun p => p.2 = y)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ p.2)
  rw [e2, e3]
  exact Finset.sum_le_sum (fun y _ => step3_aux G H D hD U hUmin c hcU hcA y)

lemma key (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel H.Adj]
    (D : Finset (α × β)) (hD : (G □ H).IsDominating (D : Set (α × β))) (U : Finset α)
    (hU : G.IsDominating (U : Set α)) (hUmin : G.dominationNumber = U.card) :
    U.card * H.dominationNumber ≤ 2 * D.card := by
  have hc : ∀ x, ∃ u, u ∈ U ∧ (x = u ∨ G.Adj x u) := by
    intro x
    rcases hU x with h | ⟨w, hw, hadj⟩
    · exact ⟨x, Finset.mem_coe.mp h, Or.inl rfl⟩
    · exact ⟨w, Finset.mem_coe.mp hw, Or.inr hadj⟩
  choose c hcU hcA using hc
  have hsum : ∑ _u ∈ U, H.dominationNumber ≤
      ∑ u ∈ U, ((cP D c u).card + (cQ H D c u).card) :=
    Finset.sum_le_sum (fun u _ => step1 H D c u)
  rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib] at hsum
  have h2 := step2 D c U hcU
  have h3 := step3 G H D hD U hUmin c hcU hcA
  omega

end OMA

theorem OMA.solution : type_of% @VizingConjecture.vizing_conjecture.variants.clark_suen := by
  intro α β _ _ _ _ G H
  classical
  obtain ⟨D, hD, hDc⟩ := exists_isNDominatingSet_dominationNumber (G □ H)
  obtain ⟨U, hU, hUc⟩ := exists_isNDominatingSet_dominationNumber G
  have h := OMA.key G H D hD U hU hUc.symm
  rw [hDc, hUc] at h
  exact h
