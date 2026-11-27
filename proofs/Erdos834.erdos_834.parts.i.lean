import FormalConjectures.ErdosProblems.«834»

-- Problem: Erdős Problem 834 — i
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/834.lean (declaration Erdos834.erdos_834.parts.i)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Proof idea: if a vertex `v` lies in at least `7` edges, the links `f \ {v}` of those edges
form a graph with at least `7` edges in which every edge `l` admits a set of at most two
vertices, disjoint from `l`, meeting every other edge. Such a graph has at most `6` edges
(a degree count plus a short case analysis). -/

namespace OMA.Erdos834

open Finset

variable {α : Type*} [DecidableEq α]

lemma eq_pair_of_mem {l : Finset α} (hl : l.card = 2) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l = {a, b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  · rw [hl, card_pair hab]

/-- Critical property of a family of pairs. -/
def Crit (L : Finset (Finset α)) : Prop :=
  ∀ l ∈ L, ∃ T : Finset α, T.card ≤ 2 ∧ Disjoint T l ∧ ∀ l' ∈ L, l' ≠ l → ∃ t ∈ T, t ∈ l'

lemma star_sub {L : Finset (Finset α)} (h2 : ∀ l ∈ L, l.card = 2) {x : α} {l0 : Finset α}
    (hx : x ∈ l0) {T : Finset α} (hT : Disjoint T l0)
    (hTc : ∀ l' ∈ L, l' ≠ l0 → ∃ t ∈ T, t ∈ l') :
    (L.filter (x ∈ ·)).erase l0 ⊆ T.image (fun t => ({x, t} : Finset α)) := by
  intro l hl
  simp only [mem_erase, mem_filter] at hl
  obtain ⟨hne, hlL, hxl⟩ := hl
  obtain ⟨t, htT, htl⟩ := hTc l hlL hne
  have hxt : x ≠ t := by
    rintro rfl
    exact Finset.disjoint_left.mp hT htT hx
  rw [mem_image]
  exact ⟨t, htT, (eq_pair_of_mem (h2 l hlL) hxl htl hxt).symm⟩

lemma deg_le {L : Finset (Finset α)} (h2 : ∀ l ∈ L, l.card = 2) (hc : Crit L) (x : α) :
    (L.filter (x ∈ ·)).card ≤ 3 := by
  rcases (L.filter (x ∈ ·)).eq_empty_or_nonempty with h | ⟨l0, hl0⟩
  · rw [h]; simp
  · have hl0' := mem_filter.mp hl0
    obtain ⟨T, hT2, hTd, hTc⟩ := hc l0 hl0'.1
    have hs := star_sub h2 hl0'.2 hTd hTc
    have h1 := card_le_card hs
    have h3 := card_image_le (s := T) (f := fun t => ({x, t} : Finset α))
    have h4 := card_erase_add_one hl0
    omega

lemma graph_bound (L : Finset (Finset α)) (h2 : ∀ l ∈ L, l.card = 2) (hc : Crit L) :
    L.card ≤ 6 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨e, he⟩ : L.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨T, hT2, hTd, hTc⟩ := hc e he
  have hsub : L.erase e ⊆ T.biUnion (fun t => L.filter (t ∈ ·)) := by
    intro l hl
    obtain ⟨hne, hlL⟩ := mem_erase.mp hl
    obtain ⟨t, htT, htl⟩ := hTc l hlL hne
    exact mem_biUnion.mpr ⟨t, htT, mem_filter.mpr ⟨hlL, htl⟩⟩
  have hcardE : L.card = (L.erase e).card + 1 := (card_erase_add_one he).symm
  have hb : (T.biUnion (fun t => L.filter (t ∈ ·))).card ≤ T.card * 3 := by
    calc _ ≤ ∑ t ∈ T, (L.filter (t ∈ ·)).card := card_biUnion_le
      _ ≤ ∑ _t ∈ T, 3 := sum_le_sum (fun t _ => deg_le h2 hc t)
      _ = T.card * 3 := by rw [sum_const, smul_eq_mul]
  have h6 := card_le_card hsub
  have hT : T.card = 2 := by omega
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hT
  set Ax := L.filter (x ∈ ·) with hAx
  set Ay := L.filter (y ∈ ·) with hAy
  have hsub2 : L.erase e ⊆ Ax ∪ Ay := by
    intro l hl
    have := hsub hl
    simp only [mem_biUnion, mem_insert, mem_singleton] at this
    obtain ⟨t, ht, htl⟩ := this
    rcases ht with rfl | rfl
    · exact mem_union_left _ htl
    · exact mem_union_right _ htl
  have hx3 : Ax.card ≤ 3 := deg_le h2 hc x
  have hy3 : Ay.card ≤ 3 := deg_le h2 hc y
  have hu := card_le_card hsub2
  have hui := card_union_add_card_inter Ax Ay
  have hAx3 : Ax.card = 3 := by omega
  have hAy3 : Ay.card = 3 := by omega
  have hint : (Ax ∩ Ay).card = 0 := by omega
  rw [card_eq_zero] at hint
  obtain ⟨l0, hl0⟩ : Ax.Nonempty := by rw [← Finset.card_pos]; omega
  have hl0' := mem_filter.mp hl0
  obtain ⟨T0, hT02, hT0d, hT0c⟩ := hc l0 hl0'.1
  have hs := star_sub h2 hl0'.2 hT0d hT0c
  have hcard_er : (Ax.erase l0).card = 2 := by
    have := card_erase_add_one hl0; omega
  have himg := card_image_le (s := T0) (f := fun t => ({x, t} : Finset α))
  have heq : Ax.erase l0 = T0.image (fun t => ({x, t} : Finset α)) :=
    eq_of_subset_of_card_le hs (by omega)
  have hyT0 : y ∉ T0 := by
    intro hy
    have hmem : ({x, y} : Finset α) ∈ Ax.erase l0 := by
      rw [heq]; exact mem_image.mpr ⟨y, hy, rfl⟩
    have hL : ({x, y} : Finset α) ∈ L := (mem_filter.mp (mem_of_mem_erase hmem)).1
    have : ({x, y} : Finset α) ∈ Ax ∩ Ay := by
      rw [mem_inter]
      exact ⟨mem_filter.mpr ⟨hL, by simp⟩, mem_filter.mpr ⟨hL, by simp⟩⟩
    rw [hint] at this
    simp at this
  have hsy : Ay ⊆ T0.image (fun t => ({y, t} : Finset α)) := by
    intro l hl
    have hl' := mem_filter.mp hl
    have hne : l ≠ l0 := by
      rintro rfl
      have : l ∈ Ax ∩ Ay := mem_inter.mpr ⟨hl0, hl⟩
      rw [hint] at this
      simp at this
    obtain ⟨t, htT, htl⟩ := hT0c l hl'.1 hne
    have hyt : y ≠ t := by rintro rfl; exact hyT0 htT
    exact mem_image.mpr ⟨t, htT, (eq_pair_of_mem (h2 l hl'.1) hl'.2 htl hyt).symm⟩
  have := card_le_card hsy
  have himg2 := card_image_le (s := T0) (f := fun t => ({y, t} : Finset α))
  omega

end OMA.Erdos834

open OMA.Erdos834 Finset in
theorem OMA.solution : type_of% @Erdos834.erdos_834.parts.i := by
  rintro ⟨n, H, hU, -, hnot, hcrit, hdeg⟩
  -- H is nonempty
  obtain ⟨e, he⟩ : H.Nonempty := by
    rcases H.eq_empty_or_nonempty with h | h
    · exact absurd ⟨∅, by simp, by simp [h]⟩ hnot
    · exact h
  obtain ⟨v, hv⟩ : e.Nonempty := by
    rw [← Finset.card_pos, hU e he]; norm_num
  have hdv := hdeg v
  unfold Finset.hypergraphDegree at hdv
  set L := (H.filter (v ∈ ·)).image (fun f => f.erase v) with hL
  have hLcard : L.card = (H.filter (v ∈ ·)).card := by
    apply card_image_of_injOn
    intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    simp only at hab
    rw [← insert_erase ha', ← insert_erase hb', hab]
  have h2 : ∀ l ∈ L, l.card = 2 := by
    intro l hl
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hl
    have hf' := mem_filter.mp hf
    rw [card_erase_of_mem hf'.2, hU f hf'.1]
  have hc : Crit L := by
    intro l hl
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hl
    have hf' := mem_filter.mp hf
    obtain ⟨T, hT2, hTc⟩ := hcrit f hf'.1
    have hdisj : Disjoint T f := by
      rw [Finset.disjoint_left]
      intro t htT htf
      apply hnot
      refine ⟨T, hT2, ?_⟩
      intro g hg
      by_cases hgf : g = f
      · subst hgf; exact ⟨t, htT, htf⟩
      · exact hTc g (by simp [hgf, hg])
    refine ⟨T, hT2, Finset.disjoint_of_subset_right (erase_subset _ _) hdisj, ?_⟩
    intro l' hl' hne
    obtain ⟨f', hf'', rfl⟩ := mem_image.mp hl'
    have hf''' := mem_filter.mp hf''
    have hff : f' ≠ f := by rintro rfl; exact hne rfl
    obtain ⟨t, htT, htf'⟩ := hTc f' (by simp [hff, hf'''.1])
    have htv : t ≠ v := by
      rintro rfl
      exact Finset.disjoint_left.mp hdisj htT hf'.2
    exact ⟨t, htT, mem_erase.mpr ⟨htv, htf'⟩⟩
  have := graph_bound L h2 hc
  omega
