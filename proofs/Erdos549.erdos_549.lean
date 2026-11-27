import FormalConjectures.ErdosProblems.«549»

/-!
A red-blue coloring on fifteen vertices avoids the double star with bipartition sizes four and
eight. In red there is just one candidate for the degree-eight center, and in blue there are none.
-/

open SimpleGraph Finset

private def starForward : (Fin 4 ⊕ Fin 8) → (Fin 4 ⊕ Fin 8) → Prop
  | .inl i, .inr j => i = 0 ∨ j = 0
  | _, _ => False

private instance : DecidableRel starForward := by
  intro x y
  cases x <;> cases y <;> unfold starForward <;> infer_instance

private def doubleStar : SimpleGraph (Fin 4 ⊕ Fin 8) := fromRel starForward

private instance : DecidableRel doubleStar.Adj :=
  inferInstanceAs (DecidableRel (fromRel starForward).Adj)

private lemma star_first (j : Fin 8) : doubleStar.Adj (.inl 0) (.inr j) := by
  simp [doubleStar, fromRel_adj, starForward]

private lemma star_second (i : Fin 4) : doubleStar.Adj (.inl i) (.inr 0) := by
  simp [doubleStar, fromRel_adj, starForward]

private lemma doubleStar_isTree : doubleStar.IsTree := by
  rw [isTree_iff_connected_and_card]
  constructor
  · refine (connected_iff_exists_forall_reachable _).mpr ⟨.inl 0, fun x => ?_⟩
    cases x with
    | inl i => exact (star_first 0).reachable.trans (star_second i).reachable.symm
    | inr j => exact (star_first j).reachable
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
    decide +kernel

-- Vertex zero is joined to 1 through 8. Vertices 9 through 14 induce a clique.
-- Among 1 through 8 the only missing edges are the cross edges between 1 through 3
-- and 4 through 6, plus the edge from 7 to 8. The two six-vertex sets 1 through 6
-- and 9 through 14 are joined by a cycle that alternates between them.
private def redForward (a b : Fin 15) : Prop :=
  a < b ∧ ((a = 0 ∧ b ≤ 8) ∨
    (1 ≤ a ∧ b ≤ 8 ∧ ¬ ((a ≤ 3 ∧ 4 ≤ b ∧ b ≤ 6) ∨ (a = 7 ∧ b = 8))) ∨
    9 ≤ a ∨
    (1 ≤ a ∧ a ≤ 6 ∧ 9 ≤ b ∧ (b.val - 9 = a.val - 1 ∨ b.val - 9 = a.val % 6)))

private instance : DecidableRel redForward := by
  intro a b
  unfold redForward
  infer_instance

private def red : SimpleGraph (Fin 15) := fromRel redForward

private instance : DecidableRel red.Adj :=
  inferInstanceAs (DecidableRel (fromRel redForward).Adj)

private theorem red_degree : ∀ v : Fin 15, red.degree v = if v = 0 then 8 else 7 := by
  decide +kernel

private theorem blue_degree : ∀ v : Fin 15, redᶜ.degree v < 8 := by
  decide +kernel

private theorem red_outside_degree :
    ∀ v : Fin 15, red.Adj 0 v →
      ((univ : Finset (Fin 15)).filter fun w => red.Adj v w ∧ ¬ red.Adj 0 w ∧ w ≠ 0).card ≤ 2 := by
  decide +kernel

private lemma right_leaves {G : SimpleGraph (Fin 15)} (f : doubleStar.Copy G) :
    (univ.image fun j : Fin 8 => f (.inr j)).card = 8 := by
  have hinj : Function.Injective (fun j : Fin 8 => f (.inr j)) :=
    fun _ _ h => Sum.inr.inj (f.injective h)
  rw [card_image_of_injective _ hinj]
  simp

private lemma right_leaves_subset {G : SimpleGraph (Fin 15)} [DecidableRel G.Adj]
    (f : doubleStar.Copy G) :
    (univ.image fun j : Fin 8 => f (.inr j)) ⊆ G.neighborFinset (f (.inl 0)) := by
  intro v hv
  obtain ⟨j, -, rfl⟩ := mem_image.mp hv
  simpa only [mem_neighborFinset, Copy.toHom_apply] using f.toHom.map_adj (star_first j)

private lemma no_red_copy : ¬ doubleStar.IsContained red := by
  rintro ⟨f⟩
  have hc := right_leaves f
  have hs := right_leaves_subset f
  have hdeg := card_le_card hs
  rw [hc, card_neighborFinset_eq_degree, red_degree] at hdeg
  have hv : f (.inl 0) = 0 := by
    by_contra hne
    simp [hne] at hdeg
  have hright : (univ.image fun j : Fin 8 => f (.inr j)) =
      red.neighborFinset (f (.inl 0)) := by
    refine eq_of_subset_of_card_le hs ?_
    rw [hc, card_neighborFinset_eq_degree, red_degree, hv, if_pos rfl]
  let leftLeaves := univ.image fun i : Fin 3 => f (.inl i.succ)
  have hlcard : leftLeaves.card = 3 := by
    dsimp [leftLeaves]
    have hinj : Function.Injective (fun i : Fin 3 => f (.inl i.succ)) :=
      fun _ _ h => Fin.succ_injective _ (Sum.inl.inj (f.injective h))
    rw [card_image_of_injective _ hinj]
    simp
  let otherCenter := f (.inr 0)
  have hadj : red.Adj 0 otherCenter := by
    rw [← hv]
    exact f.toHom.map_adj (star_first 0)
  have hsub : leftLeaves ⊆
      (univ : Finset (Fin 15)).filter fun w => red.Adj otherCenter w ∧ ¬ red.Adj 0 w ∧ w ≠ 0 := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := mem_image.mp hw
    refine mem_filter.mpr ⟨mem_univ _, (f.toHom.map_adj (star_second i.succ)).symm, ?_, ?_⟩
    · intro ha
      have hmem : f (.inl i.succ) ∈ red.neighborFinset (f (.inl 0)) :=
        by simpa only [mem_neighborFinset, hv] using ha
      rw [← hright] at hmem
      obtain ⟨j, -, heq⟩ := mem_image.mp hmem
      exact (by simp : (Sum.inr j : Fin 4 ⊕ Fin 8) ≠ Sum.inl i.succ) (f.injective heq)
    · intro heq
      have h := Sum.inl.inj (f.injective (heq.trans hv.symm))
      exact (Fin.succ_ne_zero i) h
  have hle := (card_le_card hsub).trans (red_outside_degree _ hadj)
  omega

private lemma no_blue_copy : ¬ doubleStar.IsContained redᶜ := by
  rintro ⟨f⟩
  have hle := card_le_card (right_leaves_subset f)
  rw [right_leaves f, card_neighborFinset_eq_degree] at hle
  exact (not_le_of_gt (blue_degree _)) hle

theorem OMA.solution : type_of% @Erdos549.erdos_549 := by
  intro h
  have hramsey : diagonalGraphRamsey doubleStar = 15 :=
    h 4 (by decide) doubleStar doubleStar_isTree
      (fun _ _ => by simp [doubleStar, fromRel_adj, starForward])
      (fun _ _ => by simp [doubleStar, fromRel_adj, starForward])
  let S : Set ℕ := {n | ∀ C : SimpleGraph (Fin n), doubleStar.IsContained C ∨ doubleStar.IsContained Cᶜ}
  change sInf S = 15 at hramsey
  have hnonempty : S.Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty.mp hS, Nat.sInf_empty] at hramsey
    omega
  have hmem : 15 ∈ S := hramsey ▸ Nat.sInf_mem hnonempty
  exact (hmem red).elim no_red_copy no_blue_copy