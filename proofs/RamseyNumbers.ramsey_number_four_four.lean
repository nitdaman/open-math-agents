import FormalConjectures.Wikipedia.RamseyNumbers

/-! The parity argument forces R(3,4) ≤ 9. Splitting into neighbors and
non-neighbors gives R(4,4) ≤ 18, and the Paley graph on 17 vertices
certifies sharpness. Credit: @Deldor14. -/
open SimpleGraph Finset RamseyNumbers
namespace OMA.Ramsey44

private lemma two (l : ℕ) : IsGraphRamsey l 2 l := by
  intro G ⟨hg,hc⟩
  rw [cliqueFree_two] at hg
  subst G
  apply hc univ
  refine ⟨?_, by simp⟩
  intro x _ y _ h
  simpa using h

private lemma degree_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k l r : ℕ} (hR : IsGraphRamsey r k l)
    (hG : G.CliqueFree (k+1)) (hGc : Gᶜ.CliqueFree l) (v : V) : G.degree v < r := by
  classical
  by_contra! hdeg
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (s := G.neighborFinset v) (α := Fin r) (by simpa using hdeg)
  let H := G.comap e
  let emb : H ↪g G := Embedding.comap e G
  apply hR H
  constructor
  · intro s hs
    have hs' : G.IsNClique k (s.map e) := IsNClique.mono (map_comap_le e G) hs.map
    apply hG (insert v (s.map e))
    apply hs'.insert
    rintro w hw
    obtain ⟨i,_,rfl⟩ := mem_map.mp hw
    exact (G.mem_neighborFinset v _).mp (he ⟨i,rfl⟩)
  · exact CliqueFree.comap (Embedding.complEquiv.toFun emb).isContained hGc

private lemma sym_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k l r : ℕ} (hR : IsGraphRamsey r l k)
    (hG : G.CliqueFree k) (hGc : Gᶜ.CliqueFree (l+1)) (v : V) :
    Fintype.card V - 1 - G.degree v < r := by
  classical
  rw [← degree_compl]
  exact degree_bound Gᶜ hR hGc (by simpa using hG) v

private lemma three_three : IsGraphRamsey 6 3 3 := by
  intro G ⟨hG,hGc⟩
  classical
  have hA := degree_bound G (two 3) hG hGc 0
  have hB := sym_degree G (two 3) hG hGc 0
  simp only [Fintype.card_fin] at hB
  omega

private lemma three_four : IsGraphRamsey 9 3 4 := by
  intro G ⟨hG,hGc⟩
  classical
  have hd (v : Fin 9) : G.degree v = 3 := by
    have hA := degree_bound G (two 4) hG hGc v
    have hB := sym_degree G three_three hG hGc v
    simp only [Fintype.card_fin] at hB
    omega
  have h := G.sum_degrees_eq_twice_card_edges
  simp [hd] at h
  omega

private lemma upper : IsGraphRamsey 18 4 4 := by
  intro G ⟨hG,hGc⟩
  classical
  have hA := degree_bound G three_four hG hGc 0
  have hB := sym_degree G three_four hG hGc 0
  simp only [Fintype.card_fin] at hB
  omega

private def linked (x y : Fin 17) : Bool :=
  Nat.testBit 107286 ((17 + y.val - x.val) % 17)

private def P : SimpleGraph (Fin 17) where
  Adj x y := linked x y = true
  symm := by
    have h : ∀ x y : Fin 17, linked x y = linked y x := by decide +kernel
    constructor
    intro x y hx; rwa [← h]
  loopless := ⟨by
    intro x
    have h : ∀ y : Fin 17, linked y y = false := by decide +kernel
    simp [h]⟩

private def search {V : Type*} [LinearOrder V] (adj : V → V → Bool) :
    ℕ → List V → Bool
  | 0, _ => true
  | n+1, L => L.any fun u => search adj n (L.filter fun v => decide (u < v) && adj u v)

private lemma search_complete {V : Type*} [LinearOrder V] (G : SimpleGraph V)
    (adj : V → V → Bool) (hadj : ∀ ⦃u v⦄, G.Adj u v → adj u v = true)
    {n : ℕ} {s : Finset V} {L : List V} (hs : G.IsNClique n s) (hL : ∀ x ∈ s, x ∈ L) :
    search adj n L = true := by
  induction n generalizing s L with
  | zero => rfl
  | succ n ih =>
    have hne : s.Nonempty := card_pos.mp (hs.card_eq ▸ Nat.succ_pos _)
    let u := s.min' hne
    have hu : u ∈ s := s.min'_mem hne
    apply List.any_eq_true.mpr
    refine ⟨u, hL u hu, ih (s := s.erase u) (by simpa using hs.erase_of_mem hu) ?_⟩
    intro x hx
    obtain ⟨hxne,hxs⟩ := mem_erase.mp hx
    have hux : u < x := lt_of_le_of_ne (s.min'_le x hxs) hxne.symm
    exact List.mem_filter.mpr ⟨hL x hxs, by simp [hux,hadj (hs.isClique hu hxs hxne.symm)]⟩

private def vertices : List (Fin 17) := List.finRange 17

private def nonedge (u v : Fin 17) : Bool := decide (u ≠ v) && !(linked u v)
private lemma lower : ¬ IsGraphRamsey 17 4 4 := by
  intro h
  apply h P
  constructor
  · intro s hs
    have z := search_complete P linked (fun {_ _} h => h) hs (L := vertices)
      (fun x _ => by simp [vertices])
    have test : search linked 4 vertices = false := by decide +kernel
    rw [test] at z; contradiction
  · intro s hs
    have z := search_complete Pᶜ nonedge (fun {u v} h => by
      have hn : ¬ linked u v = true := h.2
      simp [nonedge,h.1,Bool.eq_false_iff.mpr hn]) hs (L := vertices)
      (fun x _ => by simp [vertices])
    have test : search nonedge 4 vertices = false := by decide +kernel
    rw [test] at z; contradiction
end OMA.Ramsey44

open OMA.Ramsey44 in
theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_four_four := by
  rw [classicalRamsey_eq_sInf]
  let S := {n : ℕ | IsGraphRamsey n 4 4}
  have hm : sInf S ∈ S := Nat.sInf_mem ⟨18,upper⟩
  apply le_antisymm (Nat.sInf_le upper)
  by_contra! h
  have mono : Monotone (fun n => IsGraphRamsey n 4 4) := by
    apply monotone_nat_of_le_succ
    exact fun n => IsGraphRamsey.succ n 4 4
  exact lower (mono (show sInf S ≤ 17 by dsimp [S]; omega) hm)
