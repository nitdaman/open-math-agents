import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases

open RamseyNumbers SimpleGraph

namespace OMA.R_RamseyNumbers_ramsey_number_three_seven_R1

-- A clique search branches on its least vertex, retaining only larger neighbours.
lemma exclude_search {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (cert : (Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
      (fun _ rec vs => vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
      k (List.finRange n)) = false) : G.CliqueFree k := by
  let search := Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
    (fun _ rec vs => vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
  have found (j : ℕ) (vs : List (Fin n)) (s : Finset (Fin n)) (hs : G.IsNClique j s)
      (hsub : ∀ x ∈ s, x ∈ vs) : search j vs = true := by
    induction j generalizing vs s with
    | zero => rfl
    | succ j ih =>
      have hne : s.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; omega)
      let v := s.min' hne
      have hv : v ∈ s := s.min'_mem hne
      change (vs.any _) = true
      apply List.any_eq_true.mpr
      refine ⟨v, hsub v hv, ih _ (s.erase v) (hs.erase_of_mem hv) ?_⟩
      intro w hw
      obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
      exact List.mem_filter.mpr ⟨hsub w hw, decide_eq_true
        ⟨lt_of_le_of_ne (s.min'_le _ hw) hne.symm, hs.isClique hv hw hne.symm⟩⟩
  intro s hs
  have yes := found k (List.finRange n) s hs (by simp)
  change search k (List.finRange n) = false at cert
  simp_all

-- First 22-vertex graph in Brendan McKay's collection of Ramsey(3,7) graphs.
-- The table lists each vertex's larger neighbours.
set_option maxRecDepth 50000 in
set_option maxHeartbeats 16000000 in
lemma twentytwo_fails : ¬ IsGraphRamsey 22 3 7 := by
  let edge (i j : ℕ) : Bool :=
    match i with
    | 0 => j == 11 || j == 12 || j == 15 || j == 17 || j == 21
    | 1 => j == 10 || j == 13 || j == 14 || j == 20 || j == 21
    | 2 => j == 9 || j == 16 || j == 17 || j == 18 || j == 19
    | 3 => j == 8 || j == 16 || j == 18 || j == 19 || j == 20
    | 4 => j == 7 || j == 11 || j == 13 || j == 17 || j == 19 || j == 21
    | 5 => j == 6 || j == 10 || j == 12 || j == 18 || j == 19 || j == 21
    | 6 => j == 13 || j == 14 || j == 15 || j == 16 || j == 20
    | 7 => j == 12 || j == 14 || j == 15 || j == 18 || j == 20
    | 8 => j == 9 || j == 13 || j == 14 || j == 17 || j == 21
    | 9 => j == 11 || j == 12 || j == 15 || j == 20
    | 10 => j == 11 || j == 15 || j == 16 || j == 17
    | 11 => j == 14 || j == 18
    | 12 => j == 13 || j == 16
    | 13 => j == 18
    | 14 => j == 19
    | 15 => j == 19
    | 16 => j == 21
    | 17 => j == 20
    | _ => false
  let G : SimpleGraph (Fin 22) :=
    { Adj := fun u v => u ≠ v ∧ edge (min u.val v.val) (max u.val v.val) = true
      symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val, max_comm v.val u.val] using h.2⟩⟩
      loopless := ⟨fun u h => h.1 rfl⟩ }
  let : DecidableRel G.Adj := fun u v =>
    inferInstanceAs (Decidable (u ≠ v ∧ edge (min u.val v.val) (max u.val v.val) = true))
  intro h
  apply h G
  constructor
  · exact exclude_search G 3 (by rfl)
  · exact exclude_search Gᶜ 7 (by rfl)

-- With no triangle and no independent k-set, each vertex has fewer than k neighbours.
lemma degree_lt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  apply hc.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree hG v

-- An independent k-set among non-neighbours extends to an independent (k+1)-set.
lemma nonneighbors_lt {n k m : ℕ} (hr : IsGraphRamsey m 3 k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree (k + 1)) (v : Fin n) : Gᶜ.degree v < m := by
  classical
  by_contra! h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin m) (s := Gᶜ.neighborFinset v) (by simpa using h)
  have hv (i : Fin m) : Gᶜ.Adj v (f i) :=
    (Gᶜ.mem_neighborFinset v (f i)).mp (hf ⟨i, rfl⟩)
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  apply hr H
  refine ⟨CliqueFree.comap e.isContained hG, ?_⟩
  intro t ht
  have hs : Gᶜ.IsNClique k (t.map f) := by
    refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => hxy (congrArg f he)))
  apply hc _ (hs.insert (a := v) ?_)
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
  exact hv i

-- The smaller Ramsey upper bound controls the number of non-neighbours.
def H1 : Prop := IsGraphRamsey 18 3 6

-- Only triangle-free graphs of degrees five and six with a degree-six vertex remain.
def H2 : Prop :=
  ∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ v, G.degree v = 5 ∨ G.degree v = 6) → (∃ v, G.degree v = 6) → ¬ Gᶜ.CliqueFree 7

theorem main : H1 → H2 → type_of% @RamseyNumbers.ramsey_number_three_seven := by
  classical
  intro smaller restricted
  have upper : IsGraphRamsey 23 3 7 := by
    rintro G ⟨ht, hc⟩
    have degrees (v : Fin 23) : G.degree v = 5 ∨ G.degree v = 6 := by
      have hd := degree_lt G ht hc v
      have hdc := nonneighbors_lt smaller G ht hc v
      rw [G.degree_compl, Fintype.card_fin] at hdc
      omega
    apply restricted G ht degrees _ hc
    by_contra! h
    have regular (v : Fin 23) : G.degree v = 5 := (degrees v).resolve_right (h v)
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp [regular] at hsum
    omega
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨upper, ?_⟩
  intro n hn
  by_contra! hlt
  have hmono : Monotone (fun m => IsGraphRamsey m 3 7) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 3 7
  exact twentytwo_fails (hmono (show n ≤ 22 by omega) hn)

end OMA.R_RamseyNumbers_ramsey_number_three_seven_R1
