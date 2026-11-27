import FormalConjectures.ErdosProblems.«934»
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! We use the last-layer weight argument of Cambie, Cames van Batenburg,
de Joannis de Verclos and Kang, Maximising line subgraphs of diameter at most t,
Theorem 6 and Proposition 13, https://arxiv.org/abs/2103.11898. -/

open Finset Filter SimpleGraph

namespace OMA

private lemma edist_step {V : Type} {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) : G.edist x z ≤ 1 + G.edist y z := by
  simpa only [edist_eq_one_iff_adj.mpr hxy] using
    (G.edist_triangle (u := x) (v := y) (w := z))

private lemma edist_step_right {V : Type} {G : SimpleGraph V} {r x y : V}
    (hxy : G.Adj x y) : G.edist r x ≤ G.edist r y + 1 := by
  simpa only [edist_eq_one_iff_adj.mpr hxy.symm] using
    (G.edist_triangle (u := r) (v := y) (w := x))

private lemma geodesic_step {V : Type} {G : SimpleGraph V} {x z : V} {k : ℕ}
    (h : G.edist x z = ((k + 1 : ℕ) : ℕ∞)) :
    ∃ y, G.Adj x y ∧ G.edist y z = (k : ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe h
  cases p with
  | nil => simp at hp
  | @cons x y z hxy p =>
    refine ⟨y, hxy, le_antisymm ?_ ?_⟩
    · rw [Walk.length_cons] at hp
      have hlen : p.length = k := by omega
      exact hlen ▸ p.edist_le
    · have he := edist_step (z := z) hxy
      rw [h, Nat.cast_add, Nat.cast_one, add_comm (k : ℕ∞)] at he
      exact (ENat.add_le_add_iff_left (by simp : (1 : ℕ∞) ≠ ⊤)).mp he

private lemma edist_eq_of_le_step {a : ℕ∞} {i : ℕ}
    (ha : a ≤ (i : ℕ∞)) (hb : ((i + 1 : ℕ) : ℕ∞) ≤ a + 1) : a = i := by
  apply le_antisymm ha
  exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
    (by simpa only [Nat.cast_add, Nat.cast_one] using hb)

private lemma edist_eq_previous {a : ℕ∞} {i : ℕ}
    (ha : a < ((i + 1 : ℕ) : ℕ∞)) (hb : ((i + 1 : ℕ) : ℕ∞) ≤ a + 1) : a = i := by
  apply edist_eq_of_le_step _ hb
  exact (ENat.lt_add_one_iff (ENat.natCast_ne_top i)).mp
    (by simpa only [Nat.cast_add, Nat.cast_one] using ha)

section Paths

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private noncomputable def layer (i : ℕ) : Finset V := by
  classical
  exact univ.filter fun x => G.edist r x = (i : ℕ∞)

omit [DecidableRel G.Adj] in
private lemma mem_layer {i : ℕ} {x : V} :
    x ∈ layer G r i ↔ G.edist r x = (i : ℕ∞) := by
  simp [layer]

private noncomputable def neighborsAt (x : V) (i : ℕ) : Finset V := by
  classical
  exact (G.neighborFinset x).filter fun y => G.edist r y = (i : ℕ∞)

private lemma mem_neighborsAt {x y : V} {i : ℕ} :
    y ∈ neighborsAt G r x i ↔ G.Adj x y ∧ G.edist r y = (i : ℕ∞) := by
  simp [neighborsAt]

/-- Count walks that advance one layer at every step from the root. -/
private noncomputable def paths (i : ℕ) (x : V) : ℕ := by
  classical
  exact match i with
    | 0 => if x = r then 1 else 0
    | k + 1 => ∑ y ∈ neighborsAt G r x k, paths k y

private lemma paths_succ (i : ℕ) (x : V) :
    paths G r (i + 1) x = ∑ y ∈ neighborsAt G r x i, paths G r i y := by
  rw [paths]

private lemma paths_zero (x : V) (h : G.edist r x = 0) : paths G r 0 x = 1 := by
  have hr := edist_eq_zero_iff.mp h
  subst x
  simp [paths]

private lemma paths_pos (i : ℕ) {x : V} (hx : G.edist r x = (i : ℕ∞)) :
    0 < paths G r i x := by
  induction i generalizing x with
  | zero => simpa only [paths_zero G r x hx] using Nat.one_pos
  | succ i ih =>
    obtain ⟨y, hxy, hy⟩ := geodesic_step ((edist_comm (G := G) (u := x) (v := r)).trans hx)
    have hyr : G.edist r y = i := (edist_comm (G := G) (u := r) (v := y)).trans hy
    have hyMem := (mem_neighborsAt G r).mpr ⟨hxy, hyr⟩
    rw [paths_succ]
    exact (ih hyr).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyMem)

private lemma predecessors_le_paths (i : ℕ) (x : V) :
    (neighborsAt G r x i).card ≤ paths G r (i + 1) x := by
  rw [paths_succ]
  calc
    _ = ∑ y ∈ neighborsAt G r x i, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun _ hy =>
      paths_pos G r i ((mem_neighborsAt G r).mp hy).2

private noncomputable def firstNeighbors (i : ℕ) (x : V) : Finset V := by
  classical
  exact (G.neighborFinset r).filter fun u => G.edist u x = (i : ℕ∞)

private lemma mem_firstNeighbors {i : ℕ} {x u : V} :
    u ∈ firstNeighbors G r i x ↔ G.Adj r u ∧ G.edist u x = (i : ℕ∞) := by
  simp [firstNeighbors]

private lemma firstNeighbors_le_paths (i : ℕ) {x : V} (hx : G.edist r x = ((i + 1 : ℕ) : ℕ∞)) :
    (firstNeighbors G r i x).card ≤ paths G r (i + 1) x := by
  classical
  induction i generalizing x with
  | zero =>
    have hsub : firstNeighbors G r 0 x ⊆ {x} := by
      intro u hu
      exact Finset.mem_singleton.mpr (edist_eq_zero_iff.mp ((mem_firstNeighbors G r).mp hu).2)
    exact (Finset.card_le_card hsub).trans (by simpa only [Finset.card_singleton] using Nat.succ_le_of_lt (paths_pos G r 1 hx))
  | succ i ih =>
    have hsub : firstNeighbors G r (i + 1) x ⊆
        (neighborsAt G r x (i + 1)).biUnion (firstNeighbors G r i) := by
      intro u hu
      obtain ⟨hru, hux⟩ := (mem_firstNeighbors G r).mp hu
      obtain ⟨y, hxy, hyu⟩ := geodesic_step ((edist_comm (G := G) (u := x) (v := u)).trans hux)
      have hry : G.edist r y ≤ ((i + 1 : ℕ) : ℕ∞) := by
        simpa only [edist_eq_one_iff_adj.mpr hru, (edist_comm (G := G) (u := u) (v := y)).trans hyu,
          Nat.cast_add, Nat.cast_one, add_comm (1 : ℕ∞)] using
          (G.edist_triangle (u := r) (v := u) (w := y))
      have hyr : G.edist r y = ((i + 1 : ℕ) : ℕ∞) :=
        edist_eq_of_le_step hry (hx ▸ edist_step_right (r := r) hxy)
      exact Finset.mem_biUnion.mpr ⟨y, (mem_neighborsAt G r).mpr ⟨hxy, hyr⟩,
        (mem_firstNeighbors G r).mpr ⟨hru, (edist_comm (G := G) (u := u) (v := y)).trans hyu⟩⟩
    rw [paths_succ]
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun _ hy => ih ((mem_neighborsAt G r).mp hy).2))

end Paths

section Boundary

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

omit [Fintype V] [DecidableRel G.Adj] in
private lemma first_neighbor_close {k : ℕ} {u x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hru : G.Adj r u) (hxy : G.Adj x y)
    (hx : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r x) (hy : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r y) :
    G.edist u x < ((k + 1 : ℕ) : ℕ∞) ∨ G.edist u y < ((k + 1 : ℕ) : ℕ∞) := by
  by_contra! hh
  apply h
  refine ⟨r, u, x, y, hru, hxy, ?_⟩
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hx
  · exact hy
  · exact hh.1
  · exact hh.2

omit [Fintype V] [DecidableRel G.Adj] in
private lemma root_close_of_first_close {k : ℕ} {u x : V} (hru : G.Adj r u)
    (hux : G.edist u x < ((k + 1 : ℕ) : ℕ∞)) :
    G.edist r x ≤ ((k + 1 : ℕ) : ℕ∞) := by
  have hu : G.edist u x ≤ (k : ℕ∞) := ENat.lt_natCast_add_one_iff.mp
    (by simpa only [Nat.cast_add, Nat.cast_one] using hux)
  calc
    _ ≤ 1 + G.edist u x := edist_step hru
    _ ≤ 1 + (k : ℕ∞) := by gcongr
    _ = _ := by simp only [Nat.cast_add, Nat.cast_one, add_comm]

omit [Fintype V] [DecidableRel G.Adj] in
private lemma every_edge_near_root {k : ℕ} {x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hr : ∃ u, G.Adj r u) (hxy : G.Adj x y) :
    G.edist r x ≤ ((k + 1 : ℕ) : ℕ∞) ∨ G.edist r y ≤ ((k + 1 : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := hr
  by_contra! hh
  rcases first_neighbor_close G r h hu hxy hh.1.le hh.2.le with hc | hc
  · exact hh.1.not_ge (root_close_of_first_close G r hu hc)
  · exact hh.2.not_ge (root_close_of_first_close G r hu hc)

private lemma root_neighbors_covered [DecidableEq V] {k : ℕ} {x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hxy : G.Adj x y)
    (hx : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r x) (hy : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r y) :
    G.neighborFinset r ⊆ firstNeighbors G r k x ∪ firstNeighbors G r k y := by
  intro u hu
  have hru := (G.mem_neighborFinset r u).mp hu
  have eqdist {v : V} (hv : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r v)
      (huv : G.edist u v < ((k + 1 : ℕ) : ℕ∞)) : G.edist u v = (k : ℕ∞) :=
    edist_eq_previous huv (by simpa only [add_comm] using hv.trans (edist_step hru))
  rcases first_neighbor_close G r h hru hxy hx hy with hc | hc
  · exact Finset.mem_union_left _ ((mem_firstNeighbors G r).mpr ⟨hru, eqdist hx hc⟩)
  · exact Finset.mem_union_right _ ((mem_firstNeighbors G r).mpr ⟨hru, eqdist hy hc⟩)

private lemma boundary_cover [DecidableEq V] {k : ℕ} {x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hxy : G.Adj x y)
    (hx : G.edist r x = ((k + 1 : ℕ) : ℕ∞)) (hy : G.edist r y = ((k + 1 : ℕ) : ℕ∞)) :
    G.degree r ≤ paths G r (k + 1) x + paths G r (k + 1) y := by
  rw [← G.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card (root_neighbors_covered G r h hxy hx.ge hy.ge)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add
      (firstNeighbors_le_paths G r k hx) (firstNeighbors_le_paths G r k hy)))

private lemma boundary_to_outside [DecidableEq V] {k : ℕ} {x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hxy : G.Adj x y)
    (hx : G.edist r x = ((k + 1 : ℕ) : ℕ∞)) (hy : ((k + 1 : ℕ) : ℕ∞) < G.edist r y) :
    G.degree r ≤ paths G r (k + 1) x := by
  have hempty : firstNeighbors G r k y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨hru,huy⟩ := (mem_firstNeighbors G r).mp hu
    have hnear : G.edist u y < ((k + 1 : ℕ) : ℕ∞) := by
      rw [huy]
      exact ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self k)
    exact hy.not_ge (root_close_of_first_close G r hru hnear)
  have hs := root_neighbors_covered G r h hxy hx.ge hy.le
  rw [hempty, Finset.union_empty] at hs
  rw [← G.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card hs).trans (firstNeighbors_le_paths G r k hx)

end Boundary

private def chargeSize (j w : ℝ) : ℝ :=
  max 0 (min (2 * j) (4 * w - j))

private lemma chargeSize_nonneg (j w : ℝ) : 0 ≤ chargeSize j w := le_max_left _ _

private lemma chargeSize_le {j : ℝ} (hj : 0 ≤ j) (w : ℝ) : chargeSize j w ≤ 2 * j :=
  max_le (by positivity) (min_le_left _ _)

private lemma chargeSize_cover {j x y : ℝ} (hj : 0 ≤ j) (hxy : j ≤ x + y) :
    2 * j ≤ chargeSize j x + chargeSize j y := by
  by_cases hx : 2 * j ≤ 4 * x - j
  · have hxe : chargeSize j x = 2 * j := by
      unfold chargeSize
      rw [min_eq_left hx, max_eq_right (by positivity)]
    linarith only [hxe, chargeSize_nonneg j y]
  by_cases hy : 2 * j ≤ 4 * y - j
  · have hye : chargeSize j y = 2 * j := by
      unfold chargeSize
      rw [min_eq_left hy, max_eq_right (by positivity)]
    linarith only [hye, chargeSize_nonneg j x]
  have hxa : 4 * x - j ≤ chargeSize j x := by
    unfold chargeSize
    rw [min_eq_right (le_of_not_ge hx)]
    exact le_max_right _ _
  have hya : 4 * y - j ≤ chargeSize j y := by
    unfold chargeSize
    rw [min_eq_right (le_of_not_ge hy)]
    exact le_max_right _ _
  linarith only [hxy, hxa, hya]

private lemma chargeSize_budget {j w m : ℝ} (hj : 0 ≤ j) (hm₀ : 0 ≤ m) (hmw : m ≤ w) :
    2 * j * m + chargeSize j w * (j - m) ≤ 3 * j * w := by
  by_cases hw : 4 * w - j ≤ 0
  · have he : chargeSize j w = 0 := by
      unfold chargeSize
      rw [max_eq_left ((min_le_right _ _).trans hw)]
    rw [he, zero_mul, add_zero]
    have hw₀ : 0 ≤ w := hm₀.trans hmw
    nlinarith only [mul_nonneg hj (sub_nonneg.mpr hmw), mul_nonneg hj hw₀]
  by_cases hw' : 2 * j ≤ 4 * w - j
  · have he : chargeSize j w = 2 * j := by
      unfold chargeSize
      rw [min_eq_left hw', max_eq_right (by positivity)]
    rw [he]
    have hh : 0 ≤ j * (3 * w - 2 * j) := mul_nonneg hj (by linarith)
    nlinarith only [hh]
  · have hlow : 0 ≤ 4 * w - j := le_of_not_ge hw
    have hupp : 4 * w - j ≤ 2 * j := le_of_not_ge hw'
    have he : chargeSize j w = 4 * w - j := by
      unfold chargeSize
      rw [min_eq_right hupp, max_eq_right hlow]
    rw [he]
    have hh := mul_nonneg (sub_nonneg.mpr hmw) (sub_nonneg.mpr hupp)
    nlinarith only [hh, sq_nonneg (j - 2 * w)]

section Branching

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private noncomputable def forwardNeighbors (x : V) (i : ℕ) : Finset V := by
  classical
  exact (G.neighborFinset x).filter fun y => (i : ℕ∞) ≤ G.edist r y

private lemma mem_forwardNeighbors {i : ℕ} {x y : V} :
    y ∈ forwardNeighbors G r x i ↔ G.Adj x y ∧ (i : ℕ∞) ≤ G.edist r y := by
  simp [forwardNeighbors]

private def branching (j i : ℕ) : ℕ := if i = 0 then j else j - 1

private lemma forwardNeighbors_le {j i : ℕ} (hj : ∀ x, G.degree x ≤ j)
    {x : V} (hx : x ∈ layer G r i) : (forwardNeighbors G r x i).card ≤ branching j i := by
  classical
  have hsub : forwardNeighbors G r x i ⊆ G.neighborFinset x :=
    fun y hy => (G.mem_neighborFinset x y).mpr ((mem_forwardNeighbors G r).mp hy).1
  cases i with
  | zero =>
    simp only [branching]
    exact (Finset.card_le_card hsub).trans ((G.card_neighborFinset_eq_degree x).le.trans (hj x))
  | succ i =>
    have hxr : G.edist x r = ((i + 1 : ℕ) : ℕ∞) :=
      (edist_comm (G := G)).trans ((mem_layer G r).mp hx)
    obtain ⟨y, hxy, hyr⟩ := geodesic_step hxr
    have hy : y ∉ forwardNeighbors G r x (i + 1) := by
      intro hy
      have hh := ((mem_forwardNeighbors G r).mp hy).2
      rw [edist_comm (G := G) (u := r) (v := y), hyr] at hh
      have := ENat.natCast_le_natCast.mp hh
      omega
    have hins : insert y (forwardNeighbors G r x (i + 1)) ⊆ G.neighborFinset x :=
      Finset.insert_subset_iff.mpr ⟨(G.mem_neighborFinset x y).mpr hxy, hsub⟩
    have hh := Finset.card_le_card hins
    rw [G.card_neighborFinset_eq_degree, Finset.card_insert_of_notMem hy] at hh
    simp only [branching, Nat.succ_ne_zero, if_false]
    have := hj x
    omega

private lemma same_next_le (x : V) (i : ℕ) :
    (neighborsAt G r x i).card + (neighborsAt G r x (i + 1)).card ≤
      (forwardNeighbors G r x i).card := by
  classical
  have hd : Disjoint (neighborsAt G r x i) (neighborsAt G r x (i + 1)) := by
    refine Finset.disjoint_left.mpr fun y hy hy' => ?_
    have hh := ((mem_neighborsAt G r).mp hy).2.symm.trans ((mem_neighborsAt G r).mp hy').2
    have := Nat.cast_injective hh
    omega
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  intro y hy
  apply (mem_forwardNeighbors G r).mpr
  rcases Finset.mem_union.mp hy with hy | hy
  · obtain ⟨ha, he⟩ := (mem_neighborsAt G r).mp hy
    exact ⟨ha, he.ge⟩
  · obtain ⟨ha, he⟩ := (mem_neighborsAt G r).mp hy
    exact ⟨ha, he ▸ ENat.natCast_le_natCast.mpr (Nat.le_succ i)⟩

private lemma neighborsAt_eq_filter (x : V) (i : ℕ) :
    neighborsAt G r x i = (layer G r i).filter (fun y => G.Adj x y) := by
  ext y
  simp only [Finset.mem_filter, mem_neighborsAt, mem_layer, and_comm]

private noncomputable def mass (i : ℕ) : ℕ := ∑ x ∈ layer G r i, paths G r i x

private lemma mass_zero : mass G r 0 = 1 := by
  classical
  have he : layer G r 0 = {r} := by
    ext x
    simp only [mem_layer, Nat.cast_zero, edist_eq_zero_iff, Finset.mem_singleton]
    exact eq_comm
  rw [mass, he, Finset.sum_singleton]
  exact paths_zero G r r (SimpleGraph.edist_self (G := G) (v := r))

private lemma mass_succ (i : ℕ) :
    mass G r (i + 1) =
      ∑ x ∈ layer G r i, paths G r i x * (neighborsAt G r x (i + 1)).card := by
  calc
    _ = ∑ y ∈ layer G r (i + 1), ∑ x ∈ layer G r i,
        if G.Adj y x then paths G r i x else 0 := by
      simp only [mass, paths_succ, neighborsAt_eq_filter, Finset.sum_filter]
    _ = ∑ x ∈ layer G r i, ∑ y ∈ layer G r (i + 1),
        if G.Adj x y then paths G r i x else 0 := by
      rw [Finset.sum_comm]
      simp only [adj_comm (G := G)]
    _ = _ := by
      simp only [← Finset.sum_filter, ← neighborsAt_eq_filter, Finset.sum_const, Nat.nsmul_eq_mul]
      simp only [Nat.mul_comm]

private lemma mass_bound {j : ℕ} (hj : ∀ x, G.degree x ≤ j) (i : ℕ) :
    branching j i * mass G r i ≤ j * (j - 1) ^ i := by
  have hs (i : ℕ) : mass G r (i + 1) ≤ branching j i * mass G r i := by
    rw [mass_succ, mass, Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [Nat.mul_comm (branching j i)]
    exact Nat.mul_le_mul_left _ ((Nat.le_add_left _ _).trans
      ((same_next_le G r x i).trans (forwardNeighbors_le G r hj hx)))
  induction i with
  | zero => simp [mass_zero, branching]
  | succ i ih =>
    simp only [branching, Nat.succ_ne_zero, if_false, pow_succ]
    calc
      _ ≤ (j - 1) * (j * (j - 1) ^ i) := Nat.mul_le_mul_left _ ((hs i).trans ih)
      _ = _ := by ring

end Branching

section Charges

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (r : V) (k : ℕ)

/-- Charge a directed edge from its starting vertex. One full edge costs twice the root degree. -/
private noncomputable def weight (x y : V) : ℝ := by
  classical
  let j : ℝ := G.degree r
  let t : ℕ∞ := ((k + 1 : ℕ) : ℕ∞)
  exact if G.edist r x = t then
    if G.edist r y = t then chargeSize j (paths G r (k + 1) x) else 2 * j
  else if G.edist r x ≤ G.edist r y ∧ G.edist r y < t then 2 * j else 0

private lemma weight_nonneg (x y : V) : 0 ≤ weight G r k x y := by
  dsimp only [weight]
  split_ifs <;> first | exact chargeSize_nonneg _ _ | positivity

private lemma weight_le (x y : V) : weight G r k x y ≤ 2 * (G.degree r : ℝ) := by
  dsimp only [weight]
  split_ifs <;> first | exact chargeSize_le (by positivity) _ | positivity | rfl

private lemma weight_cover (h : ¬ Erdos934.HasFarEdges G (k + 1))
    (hr : ∃ u, G.Adj r u) {x y : V} (hxy : G.Adj x y) :
    2 * (G.degree r : ℝ) ≤ weight G r k x y + weight G r k y x := by
  classical
  by_cases hx : G.edist r x = ((k + 1 : ℕ) : ℕ∞)
  · by_cases hy : G.edist r y = ((k + 1 : ℕ) : ℕ∞)
    · have hw := boundary_cover G r h hxy hx hy
      have hw' : (G.degree r : ℝ) ≤ (paths G r (k + 1) x : ℝ) + paths G r (k + 1) y := by
        exact_mod_cast hw
      simpa only [weight, hx, hy, if_true] using chargeSize_cover (by positivity) hw'
    · have hW : weight G r k x y = 2 * (G.degree r : ℝ) := by
        simp only [weight, if_pos hx, if_neg hy]
      linarith only [hW, weight_nonneg G r k y x]
  by_cases hy : G.edist r y = ((k + 1 : ℕ) : ℕ∞)
  · have hW : weight G r k y x = 2 * (G.degree r : ℝ) := by
      simp only [weight, if_pos hy, if_neg hx]
    linarith only [hW, weight_nonneg G r k x y]
  have close_next {a b : V} (hadj : G.Adj a b) (ha : G.edist r a < ((k + 1 : ℕ) : ℕ∞)) :
      G.edist r b ≤ ((k + 1 : ℕ) : ℕ∞) := by
    have hle : G.edist r a ≤ (k : ℕ∞) := ENat.lt_natCast_add_one_iff.mp
      (by simpa only [Nat.cast_add, Nat.cast_one] using ha)
    calc
      _ ≤ G.edist r a + 1 := edist_step_right hadj.symm
      _ ≤ (k : ℕ∞) + 1 := by gcongr
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]
  obtain hnear | hnear := every_edge_near_root G r h hr hxy
  · have hxl : G.edist r x < ((k + 1 : ℕ) : ℕ∞) := lt_of_le_of_ne hnear hx
    have hyl : G.edist r y < ((k + 1 : ℕ) : ℕ∞) := lt_of_le_of_ne (close_next hxy hxl) hy
    rcases le_total (G.edist r x) (G.edist r y) with hl | hl
    · have he : weight G r k x y = 2 * (G.degree r : ℝ) := by
        simp only [weight, if_neg hx, if_pos (And.intro hl hyl)]
      linarith only [he, weight_nonneg G r k y x]
    · have he : weight G r k y x = 2 * (G.degree r : ℝ) := by
        simp only [weight, if_neg hy, if_pos (And.intro hl hxl)]
      linarith only [he, weight_nonneg G r k x y]
  · have hyl : G.edist r y < ((k + 1 : ℕ) : ℕ∞) := lt_of_le_of_ne hnear hy
    have hxl : G.edist r x < ((k + 1 : ℕ) : ℕ∞) := lt_of_le_of_ne (close_next hxy.symm hyl) hx
    rcases le_total (G.edist r x) (G.edist r y) with hl | hl
    · have he : weight G r k x y = 2 * (G.degree r : ℝ) := by
        simp only [weight, if_neg hx, if_pos (And.intro hl hyl)]
      linarith only [he, weight_nonneg G r k y x]
    · have he : weight G r k y x = 2 * (G.degree r : ℝ) := by
        simp only [weight, if_neg hy, if_pos (And.intro hl hxl)]
      linarith only [he, weight_nonneg G r k x y]

private noncomputable def load (x : V) : ℝ := ∑ y ∈ G.neighborFinset x, weight G r k x y

private lemma load_indicator [DecidableEq V] (x : V) (S : Finset V) (hS : S ⊆ G.neighborFinset x)
    (a b : ℝ) (hf : ∀ y ∈ G.neighborFinset x, weight G r k x y ≤
      if y ∈ S then a else b) :
    load G r k x ≤ a * S.card + b * ((G.degree x : ℝ) - S.card) := by
  classical
  let N := G.neighborFinset x
  have hp : N.filter (fun y => y ∈ S) = S := by
    ext y
    exact Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hc := Finset.card_filter_add_card_filter_not (s := N) (p := fun y => y ∈ S)
  rw [hp] at hc
  have hN : N.card = G.degree x := G.card_neighborFinset_eq_degree x
  rw [hN] at hc
  have hc' : ((N.filter fun y => y ∉ S).card : ℝ) = (G.degree x : ℝ) - S.card := by
    have hh : (S.card : ℝ) + ((N.filter fun y => y ∉ S).card : ℝ) = G.degree x := by
      exact_mod_cast hc
    linarith
  calc
    _ ≤ ∑ y ∈ N, if y ∈ S then a else b := Finset.sum_le_sum hf
    _ = _ := by
      rw [Finset.sum_ite, hp]
      simp only [Finset.sum_const, nsmul_eq_mul, hc']
      ring

private lemma load_inner (i : ℕ) (hi : i < k + 1) {x : V} (hx : x ∈ layer G r i) :
    load G r k x ≤ 2 * (G.degree r : ℝ) * (forwardNeighbors G r x i).card := by
  classical
  have hx' := (mem_layer G r).mp hx
  have hn : G.edist r x ≠ ((k + 1 : ℕ) : ℕ∞) :=
    ne_of_lt (hx'.trans_lt (ENat.natCast_lt_natCast.mpr hi))
  have hs : forwardNeighbors G r x i ⊆ G.neighborFinset x :=
    fun y hy => (G.mem_neighborFinset x y).mpr ((mem_forwardNeighbors G r).mp hy).1
  apply (load_indicator G r k x _ hs (2 * (G.degree r : ℝ)) 0 ?_).trans_eq
    (by simp only [zero_mul, add_zero])
  intro y hy
  by_cases hyy : y ∈ forwardNeighbors G r x i
  · rw [if_pos hyy]
    exact weight_le G r k x y
  · have hny : ¬ G.edist r x ≤ G.edist r y := by
      intro hh
      exact hyy ((mem_forwardNeighbors G r).mpr ⟨(G.mem_neighborFinset x y).mp hy, hx' ▸ hh⟩)
    have h' : ¬ (G.edist r x ≤ G.edist r y ∧ G.edist r y < ((k + 1 : ℕ) : ℕ∞)) :=
      fun h => hny h.1
    simp only [weight, if_neg hn, if_neg h', if_neg hyy, le_rfl]

private lemma load_last_inner {x : V} (hx : x ∈ layer G r k) :
    load G r k x ≤ 2 * (G.degree r : ℝ) * (neighborsAt G r x k).card := by
  classical
  have hx' := (mem_layer G r).mp hx
  have hn : G.edist r x ≠ ((k + 1 : ℕ) : ℕ∞) :=
    ne_of_lt (hx'.trans_lt (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self k)))
  have hs : neighborsAt G r x k ⊆ G.neighborFinset x :=
    fun y hy => (G.mem_neighborFinset x y).mpr ((mem_neighborsAt G r).mp hy).1
  apply (load_indicator G r k x _ hs (2 * (G.degree r : ℝ)) 0 ?_).trans_eq
    (by simp only [zero_mul, add_zero])
  intro y hy
  by_cases hyy : y ∈ neighborsAt G r x k
  · rw [if_pos hyy]
    exact weight_le G r k x y
  · have hny : ¬ (G.edist r x ≤ G.edist r y ∧ G.edist r y < ((k + 1 : ℕ) : ℕ∞)) := by
      rintro ⟨h₁, h₂⟩
      have h₃ : G.edist r y ≤ (k : ℕ∞) := ENat.lt_natCast_add_one_iff.mp
        (by simpa only [Nat.cast_add, Nat.cast_one] using h₂)
      exact hyy ((mem_neighborsAt G r).mpr
        ⟨(G.mem_neighborFinset x y).mp hy, le_antisymm h₃ (hx' ▸ h₁)⟩)
    simp only [weight, if_neg hn, if_neg hny, if_neg hyy, le_rfl]

private lemma load_boundary (h : ¬ Erdos934.HasFarEdges G (k + 1))
    (hmax : ∀ x, G.degree x ≤ G.degree r) {x : V} (hx : x ∈ layer G r (k + 1)) :
    load G r k x ≤ 3 * (G.degree r : ℝ) * paths G r (k + 1) x := by
  classical
  let j : ℝ := G.degree r
  let w : ℝ := paths G r (k + 1) x
  have hx' := (mem_layer G r).mp hx
  have hdeg : (G.degree x : ℝ) ≤ j := by dsimp [j]; exact_mod_cast hmax x
  have hj : 0 ≤ j := by dsimp [j]; positivity
  by_cases hwj : j ≤ w
  · have hload : load G r k x ≤ (G.degree x : ℝ) * (2 * j) := by
      calc
        _ ≤ ∑ y ∈ G.neighborFinset x, 2 * j := Finset.sum_le_sum fun y _ => weight_le G r k x y
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree]
    change load G r k x ≤ 3 * j * w
    nlinarith only [hload, mul_nonneg hj (sub_nonneg.mpr hdeg),
      mul_nonneg hj (sub_nonneg.mpr hwj), sq_nonneg j]
  have hsub : neighborsAt G r x k ⊆ G.neighborFinset x :=
    fun y hy => (G.mem_neighborFinset x y).mpr ((mem_neighborsAt G r).mp hy).1
  have hload := load_indicator G r k x _ hsub (2 * j) (chargeSize j w) (by
    intro y hy
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
    have hyl : G.edist r y ≤ ((k + 1 : ℕ) : ℕ∞) := by
      by_contra! hfar
      have hh := boundary_to_outside G r h hxy hx' hfar
      exact hwj (by dsimp [j, w]; exact_mod_cast hh)
    by_cases he : G.edist r y = ((k + 1 : ℕ) : ℕ∞)
    · have hnot : y ∉ neighborsAt G r x k := by
        intro hy'
        have hh := he.symm.trans ((mem_neighborsAt G r).mp hy').2
        have := Nat.cast_injective hh
        omega
      simp only [weight, if_pos hx', if_pos he, if_neg hnot, j, w, le_rfl]
    · have hep : G.edist r y = (k : ℕ∞) :=
        edist_eq_previous (lt_of_le_of_ne hyl he) (hx' ▸ edist_step_right (r := r) hxy)
      have hyn : y ∈ neighborsAt G r x k := (mem_neighborsAt G r).mpr ⟨hxy, hep⟩
      simp only [weight, if_pos hx', if_neg he, if_pos hyn, j, le_rfl])
  change load G r k x ≤ 3 * j * w
  let m : ℝ := (neighborsAt G r x k).card
  have hw : m ≤ w := by dsimp [m, w]; exact_mod_cast predecessors_le_paths G r k x
  have hcmp : chargeSize j w * ((G.degree x : ℝ) - m) ≤ chargeSize j w * (j - m) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hdeg m) (chargeSize_nonneg j w)
  exact hload.trans ((add_le_add (le_refl (2 * j * m)) hcmp).trans
    (chargeSize_budget hj (by dsimp [m]; positivity) hw))

private lemma load_outside {x : V} (hx : ((k + 1 : ℕ) : ℕ∞) < G.edist r x) :
    load G r k x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro y _
  have hn : ¬ (G.edist r x ≤ G.edist r y ∧ G.edist r y < ((k + 1 : ℕ) : ℕ∞)) :=
    fun h => hx.not_ge (h.1.trans h.2.le)
  simp only [weight, if_neg hx.ne', if_neg hn]

end Charges

private lemma geom_bound {j : ℕ} (hj : 0 < j) (i : ℕ) :
    (∑ a ∈ Finset.range i, j * (j - 1) ^ a) ≤ j ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rcases i with _ | i
    · simp
    rw [Finset.sum_range_succ]
    have hpow : j * (j - 1) ^ (i + 1) ≤ (j - 1) * j ^ (i + 1) := by
      rw [pow_succ (j - 1), pow_succ j]
      calc
        _ = ((j - 1) * j) * (j - 1) ^ i := by ring
        _ ≤ ((j - 1) * j) * j ^ i := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
        _ = _ := by ring
    calc
      _ ≤ j ^ (i + 1) + (j - 1) * j ^ (i + 1) := Nat.add_le_add ih hpow
      _ = (1 + (j - 1)) * j ^ (i + 1) := by ring
      _ = j * j ^ (i + 1) := by rw [show 1 + (j - 1) = j by omega]
      _ = _ := (Nat.mul_comm _ _).trans (pow_succ j (i + 1)).symm

section Sum

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (r : V) (k : ℕ)

private lemma sum_of_loads_lower (h : ¬ Erdos934.HasFarEdges G (k + 1))
    (hr : ∃ u, G.Adj r u) :
    2 * (G.degree r : ℝ) * G.edgeFinset.card ≤ ∑ x : V, load G r k x := by
  classical
  let E : (Σ x : V, ↥(G.neighborSet x)) ≃ G.Dart :=
    ⟨fun p => ⟨(p.1, p.2.val), p.2.property⟩, fun d => ⟨d.fst, d.snd, d.adj⟩,
      by rintro ⟨v, w, _⟩; rfl, by rintro ⟨⟨u, v⟩, _⟩; rfl⟩
  let F : G.Dart ≃ G.Dart := ⟨Dart.symm, Dart.symm, Dart.symm_symm, Dart.symm_symm⟩
  let c (d : G.Dart) : ℝ := weight G r k d.fst d.snd
  have hswap : (∑ d : G.Dart, weight G r k d.snd d.fst) = ∑ d : G.Dart, c d := F.sum_comp c
  have hsum : (∑ d : G.Dart, c d) = ∑ x : V, load G r k x := by
    rw [← E.sum_comp c, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (Finset.sum_subtype (G.neighborFinset x) (fun _ => G.mem_neighborFinset x _)
      (weight G r k x)).symm
  have hcard : (Fintype.card G.Dart : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.dart_card_eq_twice_card_edges
  have hle : (∑ _d : G.Dart, 2 * (G.degree r : ℝ)) ≤
      ∑ d : G.Dart, (weight G r k d.fst d.snd + weight G r k d.snd d.fst) :=
    Finset.sum_le_sum fun d _ => weight_cover G r k h hr d.adj
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, Finset.sum_add_distrib, hswap] at hle
  change 2 * (G.edgeFinset.card : ℝ) * (2 * (G.degree r : ℝ)) ≤
    (∑ d : G.Dart, c d) + ∑ d : G.Dart, c d at hle
  rw [hsum] at hle
  nlinarith only [hle]

private lemma sum_of_loads_layers :
    (∑ x : V, load G r k x) =
      ∑ i ∈ Finset.range (k + 2), ∑ x ∈ layer G r i, load G r k x := by
  classical
  symm
  simp only [layer, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : G.edist r x ≤ ((k + 1 : ℕ) : ℕ∞)
  · obtain ⟨i, hi, hik⟩ := ENat.le_natCast_iff.mp hx
    have him : i ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single i]
    · simp only [hi, if_true]
    · intro j _ hj
      exact if_neg (fun he => hj (Nat.cast_injective (he.symm.trans hi)))
    · exact fun h => (h him).elim
  · simp only [load_outside G r k (lt_of_not_ge hx), ite_self, Finset.sum_const_zero]

private lemma sum_of_loads_upper (h : ¬ Erdos934.HasFarEdges G (k + 1))
    (hj : 0 < G.degree r) (hmax : ∀ x, G.degree x ≤ G.degree r) :
    (∑ x : V, load G r k x) ≤ 3 * (G.degree r : ℝ) * (G.degree r : ℝ) ^ (k + 1) := by
  let j := G.degree r
  let cost (i : ℕ) : ℝ := ∑ x ∈ layer G r i, load G r k x
  have hcap (i : ℕ) {x : V} (hx : x ∈ layer G r i) :
      ((forwardNeighbors G r x i).card : ℝ) ≤ branching j i := by
    exact_mod_cast forwardNeighbors_le G r hmax hx
  have weight_one (i : ℕ) {x : V} (hx : x ∈ layer G r i) :
      (1 : ℝ) ≤ paths G r i x := by
    exact_mod_cast Nat.succ_le_of_lt (paths_pos G r i ((mem_layer G r).mp hx))
  have hcost (i : ℕ) (hi : i < k) :
      cost i ≤ 3 * (j : ℝ) * ((branching j i : ℝ) * mass G r i) := by
    calc
      _ ≤ ∑ x ∈ layer G r i, 3 * (j : ℝ) * (branching j i : ℝ) * paths G r i x := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hli : load G r k x ≤ 2 * (j : ℝ) * (branching j i : ℝ) :=
          (load_inner G r k i (by omega) hx).trans
            (mul_le_mul_of_nonneg_left (hcap i hx) (by positivity))
        have h₀ : 0 ≤ (j : ℝ) * (branching j i : ℝ) := by positivity
        nlinarith only [hli, h₀, mul_nonneg h₀ (sub_nonneg.mpr (weight_one i hx))]
      _ = _ := by rw [mass, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]; simp only [mul_assoc]
  -- Same-layer edges at depth k use the slots that do not send paths into the final layer.
  have hlast : cost k + cost (k + 1) ≤ 3 * (j : ℝ) * ((branching j k : ℝ) * mass G r k) := by
    have hs : (∑ y ∈ layer G r (k + 1), (paths G r (k + 1) y : ℝ)) =
        ∑ x ∈ layer G r k, (paths G r k x : ℝ) * (neighborsAt G r x (k + 1)).card := by
      exact_mod_cast mass_succ G r k
    have hh : (∑ y ∈ layer G r (k + 1), 3 * (j : ℝ) * paths G r (k + 1) y) =
        ∑ x ∈ layer G r k, 3 * (j : ℝ) * (paths G r k x : ℝ) *
          (neighborsAt G r x (k + 1)).card := by
      simp only [mul_assoc, ← Finset.mul_sum, hs]
    calc
      _ ≤ (∑ x ∈ layer G r k, 2 * (j : ℝ) * (neighborsAt G r x k).card) +
          ∑ y ∈ layer G r (k + 1), 3 * (j : ℝ) * paths G r (k + 1) y :=
        add_le_add (Finset.sum_le_sum fun _ hx => load_last_inner G r k hx)
          (Finset.sum_le_sum fun _ hx => load_boundary G r k h hmax hx)
      _ = ∑ x ∈ layer G r k, (2 * (j : ℝ) * (neighborsAt G r x k).card +
          3 * (j : ℝ) * (paths G r k x : ℝ) * (neighborsAt G r x (k + 1)).card) := by
        rw [hh, Finset.sum_add_distrib]
      _ ≤ ∑ x ∈ layer G r k, 3 * (j : ℝ) * (branching j k : ℝ) * paths G r k x := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hcnt : ((neighborsAt G r x k).card : ℝ) +
            (neighborsAt G r x (k + 1)).card ≤ branching j k := by
          exact_mod_cast (same_next_le G r x k).trans (forwardNeighbors_le G r hmax hx)
        have hj₀ : 0 ≤ (j : ℝ) := by positivity
        have hfactor : 2 * (j : ℝ) ≤ 3 * (j : ℝ) * paths G r k x := by
          nlinarith only [hj₀, mul_nonneg hj₀ (sub_nonneg.mpr (weight_one k hx))]
        have h₁ := mul_le_mul_of_nonneg_right hfactor
          (show 0 ≤ ((neighborsAt G r x k).card : ℝ) by positivity)
        have h₂ := mul_le_mul_of_nonneg_left hcnt
          (show 0 ≤ 3 * (j : ℝ) * (paths G r k x : ℝ) by positivity)
        nlinarith only [h₁, h₂]
      _ = _ := by rw [mass, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]; simp only [mul_assoc]
  have hbound (i : ℕ) :
      (branching j i : ℝ) * (mass G r i : ℝ) ≤ (j : ℝ) * ((j - 1 : ℕ) : ℝ) ^ i := by
    exact_mod_cast mass_bound G r hmax i
  have hgeom : (∑ a ∈ Finset.range (k + 1), (j : ℝ) * ((j - 1 : ℕ) : ℝ) ^ a) ≤
      (j : ℝ) ^ (k + 1) := by
    exact_mod_cast geom_bound hj (k + 1)
  rw [sum_of_loads_layers G r k]
  change (∑ i ∈ Finset.range (k + 2), cost i) ≤ 3 * (j : ℝ) * (j : ℝ) ^ (k + 1)
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  calc
    _ ≤ (∑ i ∈ Finset.range k, 3 * (j : ℝ) * ((j : ℝ) * ((j - 1 : ℕ) : ℝ) ^ i)) +
        3 * (j : ℝ) * ((j : ℝ) * ((j - 1 : ℕ) : ℝ) ^ k) := by
      rw [add_assoc]
      exact add_le_add (Finset.sum_le_sum fun i hi => (hcost i (Finset.mem_range.mp hi)).trans
        (mul_le_mul_of_nonneg_left (hbound i) (by positivity)))
        (hlast.trans (mul_le_mul_of_nonneg_left (hbound k) (by positivity)))
    _ = (3 * (j : ℝ)) * ∑ i ∈ Finset.range (k + 1), (j : ℝ) * ((j - 1 : ℕ) : ℝ) ^ i := by
      rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hgeom (by positivity)

end Sum

private lemma card_bound {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k d : ℕ} (hdegrees : ∀ x, G.degree x ≤ d)
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) :
    2 * G.edgeFinset.card ≤ 3 * d ^ (k + 1) := by
  classical
  by_cases hempty : G.edgeFinset.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
  obtain ⟨e, he⟩ := hempty
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
    obtain ⟨r, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset V) (fun v => G.degree v)
      ⟨x, Finset.mem_univ _⟩
    have hdmax (v : V) : G.degree v ≤ G.degree r := hmax v (Finset.mem_univ _)
    have hjₓ : 0 < G.degree x := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨y, (G.mem_neighborFinset x y).mpr hxy⟩
    have hj : 0 < G.degree r := hjₓ.trans_le (hdmax x)
    have hr : ∃ u, G.Adj r u := by
      rw [← G.card_neighborFinset_eq_degree] at hj
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hj
      exact ⟨u, (G.mem_neighborFinset r u).mp hu⟩
    have hsum := (sum_of_loads_lower G r k h hr).trans
      (sum_of_loads_upper G r k h hj hdmax)
    have hh : 2 * (G.edgeFinset.card : ℝ) ≤ 3 * (G.degree r : ℝ) ^ (k + 1) := by
      by_contra hn
      have hp : 0 < (G.degree r : ℝ) := Nat.cast_pos.mpr hj
      have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hp
      nlinarith only [hh, hsum]
    have hcard : 2 * G.edgeFinset.card ≤ 3 * G.degree r ^ (k + 1) := by exact_mod_cast hh
    exact hcard.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hdegrees r) _))

end OMA

theorem OMA.solution : type_of% @Erdos934.erdos_934.variants.upper := by
  intro t d ht
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hthreshold : Erdos934.h (k + 1) d ≤ 3 * d ^ (k + 1) / 2 + 1 := by
    apply Erdos934.h_le
    intro n G hD hE
    classical
    have hdeg (v : Fin n) : G.degree v ≤ d := by
      have hh := hD v
      rw [← G.coe_neighborFinset, Set.ncard_coe_finset, G.card_neighborFinset_eq_degree] at hh
      exact hh
    have hcard : G.edgeFinset.card = G.edgeSet.ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    by_contra hn
    have hg := OMA.card_bound G hdeg hn
    rw [hcard] at hg
    omega
  omega