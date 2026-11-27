import FormalConjectures.ErdosProblems.«762»

/-! A finite instance of Steiner's construction from arXiv:2408.02400, Section 3.

The first eleven vertices form the graph in Lemma 3.1. The last eight form an
independent set with selected neighborhoods in the first eleven vertices.
-/

open SimpleGraph

namespace Erdos762Steiner

/-- Adjacency rows, each encoded by the bits of a natural number.
The first four vertices form a clique. -/
private def rows : Array ℕ :=
  #[131022, 236445, 425595, 450807, 375726, 252892, 367533, 485755, 455411, 483703,
    522245, 1271, 1399, 1949, 1965, 1403, 1779, 1966, 2012]

private def edge (a b : ℕ) : Bool := rows[a]!.testBit b

private def graph : SimpleGraph (Fin 19) where
  Adj a b := edge a b = true
  symm := by
    have h : ∀ a b : Fin 19, edge a b = edge b a := by decide +kernel
    exact ⟨fun {a b} hab => (h a b).symm.trans hab⟩
  loopless := by
    have h : ∀ a : Fin 19, edge a a = false := by decide +kernel
    exact ⟨fun a hab => Bool.false_ne_true ((h a).symm.trans hab)⟩

/-- Search extensions of a prefix by checking each new entry against every earlier entry. -/
private def search {k : ℕ} (rel : ℕ → ℕ → Fin k → Fin k → Bool) :
    ℕ → List (Fin k) → Bool
  | 0, _ => true
  | m + 1, assigned =>
    (List.finRange k).any fun c =>
      (assigned.zipIdx.all fun (d, i) => rel i assigned.length d c) &&
        search rel m (assigned ++ [c])

private lemma search_complete {k n : ℕ} (rel : ℕ → ℕ → Fin k → Fin k → Bool)
    (f : Fin n → Fin k) (hf : ∀ i j : Fin n, i < j → rel i j (f i) (f j) = true)
    (m : ℕ) (p : List (Fin k)) (hsize : p.length + m = n)
    (hp : ∀ i (hi : i < p.length), p[i] = f ⟨i, by omega⟩) :
    search rel m p = true := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    let j : Fin n := ⟨p.length, by omega⟩
    rw [search, List.any_eq_true]
    refine ⟨f j, List.mem_finRange _, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · rw [List.all_eq_true]
      rintro ⟨c, i⟩ hi
      obtain ⟨hidx, hval⟩ := getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hi)
      rw [← hval, hp i hidx]
      exact hf ⟨i, by omega⟩ j hidx
    · apply ih (p ++ [f j]) (by simp; omega)
      intro i hi
      by_cases h : i < p.length
      · rw [List.getElem_append_left h, hp i h]
      · have he : i = p.length := by simp at hi; omega
        subst i
        simp [j]

private def properRel (i j : ℕ) (a b : Fin 6) : Bool :=
  a != b || !edge i j

private def cocoRel (types : Fin 3 → Bool) (i j : ℕ) (a b : Fin 3) : Bool :=
  a != b || (edge i j == types a)

private def cliqueRel (_ _ : ℕ) (a b : Fin 19) : Bool :=
  (a < b) && edge a b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma no_proper_search : search properRel 15 [0,1,2,3] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma no_coco_search (types : Fin 3 → Bool) : search (cocoRel types) 19 [] = false := by
  revert types
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private lemma no_clique_search : search cliqueRel 5 [] = false := by decide +kernel

private lemma clique_num : graph.cliqueNum = 4 := by
  have complete : ∀ a b : Fin 19, a ≤ 3 → b ≤ 3 → a ≠ b → edge a b = true := by decide +kernel
  have hcl : graph.IsClique ({0,1,2,3} : Finset (Fin 19)) := by
    intro a ha b hb hab
    refine complete a b ?_ ?_ hab
    · simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide
    · simp at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide
  have hcard : ({0,1,2,3} : Finset (Fin 19)).card = 4 := by decide
  have hlo := hcard ▸ IsClique.card_le_cliqueNum (tc := hcl)
  apply le_antisymm _ hlo
  by_contra! h
  obtain ⟨s, hs⟩ := graph.exists_isNClique_cliqueNum
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (s := s) (n := 5) (by
    rw [hs.card_eq]; omega)
  let emb := t.orderEmbOfFin htc
  have ht : graph.IsClique t := IsClique.subset (Finset.coe_subset.mpr hts) hs.isClique
  have hsearch := search_complete cliqueRel emb (fun i j hij => by
    have hlt := emb.strictMono hij
    have he := ht (t.orderEmbOfFin_mem htc i) (t.orderEmbOfFin_mem htc j) hlt.ne
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hlt, he⟩) 5 [] (by simp) (by simp)
  rw [no_clique_search] at hsearch
  contradiction

private lemma not_six_colorable : ¬ graph.Colorable 6 := by
  rintro ⟨c⟩
  let e (i : Fin 4) : Fin 19 := Fin.castLE (by omega) i
  let f (i : Fin 4) : Fin 6 := Fin.castLE (by omega) i
  have he : Function.Injective (c ∘ e) := by
    intro i j hc
    by_contra! hne
    have h : ∀ a b : Fin 4, a ≠ b → graph.Adj (e a) (e b) := by
      change ∀ a b : Fin 4, a ≠ b → edge a b = true
      decide +kernel
    exact (c.valid (h i j hne)) hc
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair (c ∘ e) f he (Fin.castLE_injective _)
  have hrel (i j : Fin 19) (hij : i < j) : properRel i j (p (c i)) (p (c j)) = true := by
    cases hed : edge i j with
    | false => simp [properRel, hed]
    | true =>
      have hne := c.valid (show graph.Adj i j from hed)
      simpa [properRel, hed] using hne
  have hprefix (i : ℕ) (hi : i < ([0,1,2,3] : List (Fin 6)).length) :
      ([0,1,2,3] : List (Fin 6))[i] = p (c ⟨i, by simp at hi; omega⟩) := by
    have hget : ∀ j : Fin 4, ([0,1,2,3] : List (Fin 6))[j.val] = f j := by
      intro j
      fin_cases j <;> rfl
    exact (hget ⟨i, hi⟩).trans (hp ⟨i, hi⟩).symm
  have hsearch := search_complete properRel (p ∘ c) hrel 15 [0,1,2,3] (by decide) hprefix
  rw [no_proper_search] at hsearch
  contradiction

private lemma no_three_cocolor : ¬ graph.Cocolorable 3 := by
  classical
  rintro ⟨c, hc⟩
  let types (i : Fin 3) := if graph.induce {v | c v = i} = ⊥ then false else true
  have hrel (i j : Fin 19) (hij : i < j) : cocoRel types i j (c i) (c j) = true := by
    by_cases he : c i = c j
    · have hi : i ∈ {v | c v = c i} := rfl
      have hj : j ∈ {v | c v = c i} := he.symm
      by_cases hbot : graph.induce {v | c v = c i} = ⊥
      · have hne := (eq_bot_iff_forall_not_adj.mp hbot) ⟨i, hi⟩ ⟨j, hj⟩
        change edge i j ≠ true at hne
        simp [cocoRel, ← he, types, hbot, Bool.eq_false_iff.mpr hne]
      · have htop := (hc (c i)).resolve_left hbot
        have hadj : (⊤ : SimpleGraph {v | c v = c i}).Adj ⟨i, hi⟩ ⟨j, hj⟩ :=
          fun h => hij.ne (congrArg Subtype.val h)
        rw [← htop] at hadj
        change edge i j = true at hadj
        simp [cocoRel, ← he, types, hbot, hadj]
    · simp [cocoRel, he]
  have hsearch := search_complete (cocoRel types) c hrel 19 [] (by simp) (by simp)
  rw [no_coco_search] at hsearch
  contradiction

private def sevenColor (i : Fin 19) : Fin 7 :=
  (![0,1,2,3,0,1,4,2,3,5,1,3,5,4,4,2,3,0,6] : Fin 19 → Fin 7) i

private def fourCocolor (i : Fin 19) : Fin 4 :=
  (![1,2,1,2,2,3,3,2,3,3,1,0,0,0,0,0,0,0,0] : Fin 19 → Fin 4) i

private lemma chi_eq : graph.chromaticNumber = 7 := by
  have hproper : ∀ a b : Fin 19, edge a b = true → sevenColor a ≠ sevenColor b := by
    decide +kernel
  apply le_antisymm
  · exact chromaticNumber_le_iff_colorable.mpr ⟨⟨sevenColor, fun h => hproper _ _ h⟩⟩
  · by_contra! h
    apply not_six_colorable
    apply chromaticNumber_le_iff_colorable.mp
    exact Order.le_of_lt_add_one h

private lemma zeta_eq : graph.cochromaticNumber = 4 := by
  classical
  have hclasses : ∀ a b : Fin 19, a ≠ b → fourCocolor a = fourCocolor b →
      edge a b = (fourCocolor a != 0) := by decide +kernel
  apply le_antisymm
  · have hc : graph.Cocolorable 4 := by
      refine ⟨fourCocolor, fun i => ?_⟩
      by_cases hi : i = 0
      · left
        rw [eq_bot_iff_forall_not_adj]
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        have hadj : graph.Adj a b := hab
        have he := hclasses a b hadj.ne (show fourCocolor a = fourCocolor b from ha.trans hb.symm)
        change edge a b = true at hab
        change fourCocolor a = i at ha
        simp [ha, hi, hab] at he
      · right
        apply top_unique
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        have he := hclasses a b (fun e => hab (Subtype.ext e)) (ha.trans hb.symm)
        change edge a b = true
        change fourCocolor a = i at ha
        exact he.trans (ha.symm ▸ (bne_iff_ne.mpr hi : (i != 0) = true))
    exact iInf₂_le 4 hc
  · apply le_iInf₂
    intro n hn
    by_contra! h
    have hn3 : n ≤ 3 := by exact_mod_cast (show (n : ℕ∞) ≤ 3 from Order.le_of_lt_add_one h)
    obtain ⟨c, hc⟩ := hn
    apply no_three_cocolor
    refine ⟨Fin.castLE hn3 ∘ c, fun i => ?_⟩
    by_cases hi : ∃ j, Fin.castLE hn3 j = i
    · obtain ⟨j, rfl⟩ := hi
      have he : {v | (Fin.castLE hn3 ∘ c) v = Fin.castLE hn3 j} = {v | c v = j} := by
        ext v
        exact ⟨fun h => Fin.castLE_injective _ h, congrArg (Fin.castLE hn3)⟩
      rw [he]
      exact hc j
    · left
      rw [eq_bot_iff_forall_not_adj]
      rintro ⟨a, ha⟩
      exact (hi ⟨c a, ha⟩).elim

end Erdos762Steiner

open Erdos762Steiner

theorem OMA.solution : type_of% @Erdos762.erdos_762.variants.steiner :=
  ⟨19, graph, clique_num, zeta_eq, chi_eq⟩