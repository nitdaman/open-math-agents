import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise

-- Credit: @avivorly
/-! Encode each exterior line by its index in the fixed list of sixty lines. -/



namespace FiniteSupportRelabeling

theorem relabel_finset {α : Type} [Fintype α] [DecidableEq α] (s t : Finset α)
    (same_size : s.card = t.card) :
    ∃ perm : Equiv.Perm α, s.map perm.toEmbedding = t := by
  classical
  let inside : s ≃ t := Fintype.equivOfCardEq (by simpa using same_size)
  let outside : {x // x ∉ s} ≃ {x // x ∉ t} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    simpa using congrArg (fun n => Fintype.card α - n) same_size)
  let perm := (Equiv.sumCompl (fun x => x ∈ s)).symm.trans
    ((Equiv.sumCongr inside outside).trans (Equiv.sumCompl (fun x => x ∈ t)))
  refine ⟨perm, ?_⟩
  have map_in (x : s) : perm x.val = (inside x).val := by
    simp [perm, Equiv.sumCompl_symm_apply_of_pos x.property]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, xy⟩ := Finset.mem_map.mp hy
    let p : s := ⟨x,hx⟩
    change perm x = y at xy
    rw [map_in p] at xy
    exact xy ▸ (inside p).property
  · intro hy
    let z : t := ⟨y,hy⟩
    let x : s := inside.symm z
    apply Finset.mem_map.mpr
    refine ⟨x.val, x.property, ?_⟩
    change perm x.val = y
    rw [map_in x]
    exact congrArg Subtype.val (inside.apply_symm_apply z)

end FiniteSupportRelabeling

namespace StarLabelTransport

open Finset

variable {α β : Type} [DecidableEq α] [DecidableEq β]

abbrev Edge (α : Type) := Finset α
abbrev Matching (α : Type) := Finset (Edge α)
abbrev Exterior (α : Type) := Finset (Matching α)

def isMatching (L : Finset α) (M : Matching α) : Prop :=
  M.card = 3 ∧ (∀ e ∈ M, e ⊆ L ∧ e.card = 2) ∧ ∀ p ∈ L, ∃! e, e ∈ M ∧ p ∈ e

def isExterior (L : Finset α) (C : Exterior α) : Prop :=
  C.card = 2 ∧ (∀ M ∈ C, isMatching L M) ∧
    ∀ M ∈ C, ∀ N ∈ C, M ≠ N → Disjoint M N

omit [DecidableEq α] [DecidableEq β] in
lemma map_mem (e : α ≃ β) (x : α) (s : Finset α) :
    e x ∈ e.finsetCongr s ↔ x ∈ s :=
  Finset.mem_map' e.toEmbedding

omit [DecidableEq α] [DecidableEq β] in
lemma matching_forward (e : α ≃ β) (L : Finset α) (M : Matching α)
    (valid : isMatching L M) :
    isMatching (e.finsetCongr L) (e.finsetCongr.finsetCongr M) := by
  refine ⟨by simpa [Equiv.finsetCongr_apply] using valid.1, ?_, ?_⟩
  · intro F memF
    obtain ⟨f, mf, rfl⟩ := Finset.mem_map.mp memF
    exact ⟨Finset.map_subset_map.mpr (valid.2.1 f mf).1,
      by simpa [Equiv.finsetCongr_apply] using (valid.2.1 f mf).2⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    exact (e.finsetCongr.existsUnique_congr (fun f =>
      and_congr (map_mem e.finsetCongr f M).symm (map_mem e q f).symm)).mp
      (valid.2.2 q hq)

theorem matching_relabel (e : α ≃ β) (L : Finset α) (M : Matching α) :
    isMatching (e.finsetCongr L) (e.finsetCongr.finsetCongr M) ↔ isMatching L M := by
  refine ⟨fun h => ?_, matching_forward e L M⟩
  have back := matching_forward e.symm _ _ h
  simpa only [← Equiv.finsetCongr_symm, Equiv.symm_apply_apply] using back

lemma exterior_forward (e : α ≃ β) (L : Finset α) (C : Exterior α)
    (valid : isExterior L C) :
    isExterior (e.finsetCongr L) (e.finsetCongr.finsetCongr.finsetCongr C) := by
  let E := e.finsetCongr
  let M := E.finsetCongr
  refine ⟨by simpa [Equiv.finsetCongr_apply] using valid.1, ?_, ?_⟩
  · intro F hF
    obtain ⟨f, fC, rfl⟩ := Finset.mem_map.mp hF
    exact matching_forward e L f (valid.2.1 f fC)
  · intro F hF G hG unequal
    obtain ⟨f, fC, rfl⟩ := Finset.mem_map.mp hF
    obtain ⟨g, gC, rfl⟩ := Finset.mem_map.mp hG
    have ne : f ≠ g := fun h => unequal (congrArg M h)
    exact (Finset.disjoint_map E.toEmbedding).mpr (valid.2.2 f fC g gC ne)

theorem exterior_relabel (e : α ≃ β) (L : Finset α) (C : Exterior α) :
    isExterior (e.finsetCongr L) (e.finsetCongr.finsetCongr.finsetCongr C) ↔ isExterior L C := by
  refine ⟨fun h => ?_, exterior_forward e L C⟩
  have back := exterior_forward e.symm _ _ h
  simpa only [← Equiv.finsetCongr_symm, Equiv.symm_apply_apply] using back

abbrev Star (α : Type) := Finset (Exterior α)

def StarCover (L : Finset α) (stars : ↥(L.powersetCard 2) → Fin 6 → Star α) : Prop :=
  (∀ e i C, C ∈ stars e i → isExterior L C ∧ ∀ M ∈ C, e.val ∉ M) ∧
  (∀ e i M, isMatching L M → e.val ∉ M → ∃! C, C ∈ stars e i ∧ M ∈ C) ∧
  (∀ e C, isExterior L C → (∀ M ∈ C, e.val ∉ M) → ∃! i, C ∈ stars e i) ∧
  ∀ e f, e ≠ f → ∀ i j, (stars e i ∩ stars f j).card ≤ 1

theorem starCover_relabel (g : α ≃ β) (L : Finset α)
    (stars : ↥(L.powersetCard 2) → Fin 6 → Star α) (valid : StarCover L stars) :
    ∃ stars' : ↥((g.finsetCongr L).powersetCard 2) → Fin 6 → Star β,
      StarCover (g.finsetCongr L) stars' := by
  let E := g.finsetCongr
  let M := E.finsetCongr
  let C := M.finsetCongr
  let S := C.finsetCongr
  let E' : ↥(L.powersetCard 2) ≃ ↥((E L).powersetCard 2) :=
    E.subtypeEquiv (fun e => by
      rw [Finset.mem_powersetCard, Finset.mem_powersetCard]
      simp [E, Equiv.finsetCongr_apply, Finset.map_subset_map])
  let stars' := fun (e : ↥((E L).powersetCard 2)) (i : Fin 6) => S (stars (E'.symm e) i)
  have edge (e : ↥(L.powersetCard 2)) : (E' e).val = E e.val := rfl
  have mem (e : ↥(L.powersetCard 2)) (i : Fin 6) (c : Exterior α) :
      C c ∈ stars' (E' e) i ↔ c ∈ stars e i := by
    dsimp only [stars']
    rw [E'.symm_apply_apply]
    exact map_mem C c (stars e i)
  refine ⟨stars', ?_, ?_, ?_, ?_⟩
  · intro e' i c' h
    obtain ⟨e, rfl⟩ := E'.surjective e'
    obtain ⟨c, rfl⟩ := C.surjective c'
    obtain ⟨legal, avoid⟩ := valid.1 e i c ((mem e i c).mp h)
    refine ⟨exterior_forward g L c legal, ?_⟩
    intro m' at_m'
    obtain ⟨m, rfl⟩ := M.surjective m'
    rw [edge]
    exact mt (map_mem E e.val m).mp (avoid m ((map_mem M m c).mp at_m'))
  · intro e' i m' valid_m' avoid'
    obtain ⟨e, rfl⟩ := E'.surjective e'
    obtain ⟨m, rfl⟩ := M.surjective m'
    have legal := (matching_relabel g L m).mp valid_m'
    have avoid : e.val ∉ m := fun h => avoid' (edge e ▸ (map_mem E e.val m).mpr h)
    apply (C.existsUnique_congr (fun c => and_congr (mem e i c).symm (map_mem M m c).symm)).mp
    exact valid.2.1 e i m legal avoid
  · intro e' c' valid_c' avoid'
    obtain ⟨e, rfl⟩ := E'.surjective e'
    obtain ⟨c, rfl⟩ := C.surjective c'
    have legal := (exterior_relabel g L c).mp valid_c'
    have avoid (m : Matching α) (hm : m ∈ c) : e.val ∉ m :=
      fun h => avoid' (M m) ((map_mem M m c).mpr hm) (edge e ▸ (map_mem E e.val m).mpr h)
    exact (Equiv.refl (Fin 6)).existsUnique_congr (fun i => (mem e i c).symm) |>.mp
      (valid.2.2.1 e c legal avoid)
  · intro e' f' different i j
    obtain ⟨e, rfl⟩ := E'.surjective e'
    obtain ⟨f, rfl⟩ := E'.surjective f'
    have ne : e ≠ f := fun eq => different (congrArg E' eq)
    dsimp only [stars']
    rw [E'.symm_apply_apply, E'.symm_apply_apply]
    change ((stars e i).map C.toEmbedding ∩ (stars f j).map C.toEmbedding).card ≤ 1
    rw [← Finset.map_inter, Finset.card_map]
    exact valid.2.2.2 e f ne i j

end StarLabelTransport

namespace StarLabelTransport

open Finset

def sixLabels : Finset (Fin 111) := {0, 1, 2, 3, 4, 5}

lemma sixLabels_card : sixLabels.card = 6 := by decide +kernel

theorem standard_star_cover (L : Finset (Fin 111)) (six : L.card = 6)
    (stars : ↥(L.powersetCard 2) → Fin 6 → Star (Fin 111)) (valid : StarCover L stars) :
    ∃ stars' : ↥(sixLabels.powersetCard 2) → Fin 6 → Star (Fin 111), StarCover sixLabels stars' := by
  obtain ⟨g, hg⟩ := FiniteSupportRelabeling.relabel_finset L sixLabels
    (six.trans sixLabels_card.symm)
  have same : g.finsetCongr L = sixLabels := hg
  have eq := congrArg (fun t : Finset (Fin 111) =>
    ∃ f : ↥(t.powersetCard 2) → Fin 6 → Star (Fin 111), StarCover t f) same
  exact eq.mp (starCover_relabel g L stars valid)

end StarLabelTransport

namespace FinitePairingEnumeration

variable {α : Type} [DecidableEq α]

def pairing (allowed : Finset α → Bool) (vertices : Finset α)
    (pairs : Finset (Finset α)) : Prop :=
  (∀ e ∈ pairs, e.card = 2 ∧ e ⊆ vertices ∧ allowed e = true) ∧
    ∀ x ∈ vertices, ∃! e, e ∈ pairs ∧ x ∈ e

def enumerate (allowed : Finset α → Bool) : Nat → List α → List (Finset (Finset α))
  | _, [] => [∅]
  | 0, _ :: _ => []
  | fuel + 1, a :: tail =>
      tail.flatMap fun b =>
        if allowed {a, b} then
          (enumerate allowed fuel (tail.erase b)).map (insert {a, b})
        else []

theorem enumerate_complete (allowed : Finset α → Bool) (fuel : Nat)
    (vertices : List α) (nodup : vertices.Nodup) (length : vertices.length ≤ fuel)
    (pairs : Finset (Finset α)) (valid : pairing allowed vertices.toFinset pairs) :
    pairs ∈ enumerate allowed fuel vertices := by
  induction fuel generalizing vertices pairs with
  | zero =>
      have empty : vertices = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero length)
      subst vertices
      have none : pairs = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain ⟨card, contained, _⟩ := valid.1 e he
        have zero : e.card ≤ 0 := by simpa using Finset.card_le_card contained
        omega
      simp [enumerate, none]
  | succ fuel ih =>
      cases vertices with
      | nil =>
          have empty : pairs = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro e he
            obtain ⟨card, contained, _⟩ := valid.1 e he
            have zero : e.card ≤ 0 := by simpa using Finset.card_le_card contained
            omega
          simp [enumerate, empty]
      | cons a tail =>
          have on_a : a ∈ (a :: tail).toFinset := by simp
          obtain ⟨e, ⟨he, ha⟩, unique_a⟩ := valid.2 a on_a
          obtain ⟨e_card, e_inside, e_allowed⟩ := valid.1 e he
          have one : (e.erase a).card = 1 := by rw [Finset.card_erase_of_mem ha, e_card]
          obtain ⟨b, b_eq⟩ := Finset.card_eq_one.mp one
          have b_mem : b ∈ e.erase a := by simp [b_eq]
          obtain ⟨ba, hb⟩ := Finset.mem_erase.mp b_mem
          have e_eq : e = {a, b} := by
            rw [← b_eq, Finset.insert_erase ha]
          have bt : b ∈ tail := by
            have on := e_inside hb
            simpa [ba] using on
          have no_a := (List.nodup_cons.mp nodup).1
          have tail_nodup := (List.nodup_cons.mp nodup).2
          let next := tail.erase b
          have next_nodup : next.Nodup := tail_nodup.erase b
          have next_len : next.length ≤ fuel := by
            have le : next.length ≤ tail.length := List.length_erase_le
            simp only [List.length_cons] at length
            omega
          have in_b := e_inside hb
          obtain ⟨f, _, unique_b⟩ := valid.2 b in_b
          have other (g : Finset α) (hg : g ∈ pairs.erase e) : a ∉ g ∧ b ∉ g := by
            obtain ⟨different, in_pairs⟩ := Finset.mem_erase.mp hg
            refine ⟨fun on => different (unique_a g ⟨in_pairs, on⟩), ?_⟩
            intro on
            exact different ((unique_b g ⟨in_pairs, on⟩).trans (unique_b e ⟨he, hb⟩).symm)
          have remaining : pairing allowed next.toFinset (pairs.erase e) := by
            constructor
            · intro g hg
              obtain ⟨card, contained, permit⟩ := valid.1 g (Finset.mem_of_mem_erase hg)
              refine ⟨card, ?_, permit⟩
              intro x hx
              obtain ⟨no_a, no_b⟩ := other g hg
              have xa : x ≠ a := fun eq => no_a (eq ▸ hx)
              have xb : x ≠ b := fun eq => no_b (eq ▸ hx)
              have in_tail : x ∈ tail := by simpa [xa] using contained hx
              exact List.mem_toFinset.mpr ((List.mem_erase_of_ne xb).mpr in_tail)
            · intro x hx
              have ht : x ∈ tail := List.mem_of_mem_erase (List.mem_toFinset.mp hx)
              have xa : x ≠ a := fun eq => no_a (eq ▸ ht)
              have xb : x ≠ b := by
                intro eq
                have h := List.mem_toFinset.mp hx
                change x ∈ tail.erase b at h
                exact List.Nodup.not_mem_erase tail_nodup (eq ▸ h)
              have old : x ∈ (a :: tail).toFinset := by simp [ht]
              obtain ⟨g, ⟨hg, at_x⟩, unique⟩ := valid.2 x old
              have ge : g ≠ e := by
                intro eq
                rw [eq, e_eq, Finset.mem_insert, Finset.mem_singleton] at at_x
                exact at_x.elim xa xb
              exact ⟨g, ⟨Finset.mem_erase.mpr ⟨ge,hg⟩, at_x⟩,
                fun f hf => unique f ⟨Finset.mem_of_mem_erase hf.1, hf.2⟩⟩
          have member := ih next next_nodup next_len (pairs.erase e) remaining
          simp only [enumerate, List.mem_flatMap]
          refine ⟨b, bt, ?_⟩
          rw [← e_eq, e_allowed, if_pos rfl, List.mem_map]
          exact ⟨pairs.erase e, member, Finset.insert_erase he⟩

end FinitePairingEnumeration

namespace WeightFifteenLargeCatalog

def labels : List (Fin 111) := [0, 1, 2, 3, 4, 5]

abbrev Edge := Finset (Fin 111)
abbrev Medium := Finset Edge
abbrev Exterior := Finset Medium
abbrev Star := Finset Exterior

def medium : List Medium :=
  [{{0,1}, {2,3}, {4,5}},
    {{0,1}, {2,4}, {3,5}},
    {{0,1}, {2,5}, {3,4}},
    {{0,2}, {1,3}, {4,5}},
    {{0,2}, {1,4}, {3,5}},
    {{0,2}, {1,5}, {3,4}},
    {{0,3}, {1,2}, {4,5}},
    {{0,3}, {1,4}, {2,5}},
    {{0,3}, {1,5}, {2,4}},
    {{0,4}, {1,2}, {3,5}},
    {{0,4}, {1,3}, {2,5}},
    {{0,4}, {1,5}, {2,3}},
    {{0,5}, {1,2}, {3,4}},
    {{0,5}, {1,3}, {2,4}},
    {{0,5}, {1,4}, {2,3}}]

set_option maxRecDepth 30000 in
lemma medium_enum :
    FinitePairingEnumeration.enumerate (fun _ => true) 6 labels = medium := by decide +kernel

def generatedExterior : List Exterior :=
  medium.zipIdx.flatMap fun (a, i) =>
    medium.zipIdx.filterMap fun (b, j) => if i < j ∧ Disjoint a b then some {a,b} else none

def exteriorPairs : List (Fin 15 × Fin 15) :=
  [(0, 4), (0, 5), (0, 7), (0, 8), (0, 9), (0, 10), (0, 12), (0, 13),
    (1, 3), (1, 5), (1, 6), (1, 7), (1, 10), (1, 11), (1, 12), (1, 14),
    (2, 3), (2, 4), (2, 6), (2, 8), (2, 9), (2, 11), (2, 13), (2, 14),
    (3, 7), (3, 8), (3, 9), (3, 11), (3, 12), (3, 14), (4, 6), (4, 8),
    (4, 10), (4, 11), (4, 12), (4, 13), (5, 6), (5, 7), (5, 9), (5, 10),
    (5, 13), (5, 14), (6, 10), (6, 11), (6, 13), (6, 14), (7, 9), (7, 11),
    (7, 12), (7, 13), (8, 9), (8, 10), (8, 12), (8, 14), (9, 13), (9, 14),
    (10, 12), (10, 14), (11, 12), (11, 13)]

def exteriorPair (p : Fin 60) : Fin 15 × Fin 15 := exteriorPairs[p.val]'p.isLt

def mediumAt (m : Fin 15) : Medium := medium[m.val]'m.isLt

def exterior : List Exterior := exteriorPairs.map fun pair => {mediumAt pair.1, mediumAt pair.2}

set_option maxRecDepth 30000 in
lemma generatedExterior_eq : generatedExterior = exterior := by decide +kernel

end WeightFifteenLargeCatalog

open Finset

namespace WeightFifteenLargeCatalog

def isMedium (M : Medium) : Prop :=
  M.card = 3 ∧ (∀ e ∈ M, e.card = 2 ∧ e ⊆ labels.toFinset) ∧
    ∀ p ∈ labels.toFinset, (M.filter fun e => p ∈ e).card = 1

instance (M : Medium) : Decidable (isMedium M) := by
  unfold isMedium
  let edges : Decidable (∀ e ∈ M, e.card = 2 ∧ e ⊆ labels.toFinset) :=
    Finset.decidableDforallFinset
  let labelsCovered : Decidable (∀ p ∈ labels.toFinset, (M.filter fun e => p ∈ e).card = 1) :=
    Finset.decidableDforallFinset
  exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ edges labelsCovered)

set_option maxRecDepth 30000 in
theorem medium_correct (M : Medium) : M ∈ medium ↔ isMedium M := by
  constructor
  · intro member
    have all_valid : medium.all (fun m => decide (isMedium m)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp all_valid M member)
  · intro valid
    rw [← medium_enum]
    apply FinitePairingEnumeration.enumerate_complete _ 6 labels
      (by decide +kernel) (by decide +kernel)
    refine ⟨?_, ?_⟩
    · intro e he
      exact ⟨(valid.2.1 e he).1, (valid.2.1 e he).2, rfl⟩
    · intro p hp
      obtain ⟨e, sole⟩ := Finset.card_eq_one.mp (valid.2.2 p hp)
      have mem : e ∈ M.filter (fun E => p ∈ E) := by rw [sole]; simp
      refine ⟨e, Finset.mem_filter.mp mem, ?_⟩
      intro E hE
      have mem : E ∈ M.filter (fun e => p ∈ e) := Finset.mem_filter.mpr hE
      rwa [sole, Finset.mem_singleton] at mem

def isExterior (C : Exterior) : Prop :=
  C.card = 2 ∧ (∀ M ∈ C, isMedium M) ∧
    ∀ M ∈ C, ∀ N ∈ C, M ≠ N → Disjoint M N

theorem exterior_complete (C : Exterior) (valid : isExterior C) : C ∈ exterior := by
  obtain ⟨a, b, different, label⟩ := Finset.card_eq_two.mp valid.1
  have ha : a ∈ medium := (medium_correct a).mpr (valid.2.1 a (by simp [label]))
  have hb : b ∈ medium := (medium_correct b).mpr (valid.2.1 b (by simp [label]))
  obtain ⟨i, i_eq⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨j, j_eq⟩ := List.mem_iff_getElem?.mp hb
  have i_ne_j : i ≠ j := by
    intro eq
    rw [eq, j_eq] at i_eq
    exact different (Option.some.inj i_eq.symm)
  have pair_one : (a, i) ∈ medium.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr i_eq
  have pair_two : (b, j) ∈ medium.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr j_eq
  have disj := valid.2.2 a (by simp [label]) b (by simp [label]) different
  rw [← generatedExterior_eq, generatedExterior, List.mem_flatMap]
  rcases lt_or_gt_of_ne i_ne_j with less | greater
  · refine ⟨(a,i), pair_one, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨(b,j), pair_two, by simp [less, disj, label]⟩
  · refine ⟨(b,j), pair_two, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨(a,i), pair_one, by simp [greater, disj.symm, label, Finset.pair_comm]⟩

end WeightFifteenLargeCatalog

namespace FiniteSearchMasks

variable {α : Type}

def bitMask (xs : List α) (chosen : α → Bool) : Nat :=
  (xs.zipIdx.map fun (x, i) => if chosen x then 2^i else 0).foldr Nat.lor 0

lemma foldr_or_testBit (words : List Nat) (i : Nat) :
    (words.foldr Nat.lor 0).testBit i = true ↔ ∃ n ∈ words, n.testBit i = true := by
  induction words with
  | nil => simp
  | cons word words ih =>
      change (word ||| words.foldr Nat.lor 0).testBit i = true ↔ _
      simp only [Nat.testBit_lor, Bool.or_eq_true, ih, List.mem_cons]
      constructor
      · intro h
        rcases h with bit | ⟨n, hn, bit⟩
        · exact ⟨word, Or.inl rfl, bit⟩
        · exact ⟨n, Or.inr hn, bit⟩
      · rintro ⟨n, h, bit⟩
        rcases h with rfl | mem
        · exact Or.inl bit
        · exact Or.inr ⟨n, mem, bit⟩

theorem bitMask_testBit (xs : List α) (chosen : α → Bool) (i : Nat) :
    (bitMask xs chosen).testBit i = true ↔ ∃ x, xs[i]? = some x ∧ chosen x = true := by
  rw [bitMask, foldr_or_testBit]
  constructor
  · rintro ⟨n, member, set⟩
    obtain ⟨⟨x,j⟩, hxj, rfl⟩ := List.mem_map.mp member
    cases hx : chosen x with
    | false => simp [hx] at set
    | true =>
      have ji : j = i := by simpa [hx, Nat.testBit_two_pow] using set
      subst j
      exact ⟨x, List.mk_mem_zipIdx_iff_getElem?.mp hxj, hx⟩
  · rintro ⟨x, hx, chosen_x⟩
    refine ⟨2^i, ?_, Nat.testBit_two_pow_self⟩
    apply List.mem_map.mpr
    exact ⟨(x,i), List.mk_mem_zipIdx_iff_getElem?.mpr hx, by simp [chosen_x]⟩

lemma bitMask_getElem_testBit (xs : List α) (chosen : α → Bool) (i : ℕ) (in_list : i < xs.length) :
    (bitMask xs chosen).testBit i = chosen xs[i] := by
  apply Bool.eq_iff_iff.mpr
  rw [bitMask_testBit]
  simp [List.getElem?_eq_getElem in_list]

end FiniteSearchMasks
namespace WeightFifteenLargeCatalog

open Finset FiniteSearchMasks

def base : Finset (Fin 111) := labels.toFinset

lemma base_eq : base = StarLabelTransport.sixLabels := by decide +kernel

def groupEdges : List Edge :=
  [{0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {1,2}, {1,3}, {1,4}, {1,5},
    {2,3}, {2,4}, {2,5}, {3,4}, {3,5}, {4,5}]

def groupEdge (g : Fin 15) : Edge := groupEdges[g.val]'g.isLt

lemma groupEdge_valid : ∀ g : Fin 15, groupEdge g ∈ base.powersetCard 2 := by decide +kernel

lemma groupEdge_injective : Function.Injective groupEdge := by
  have distinct : groupEdges.Nodup := by decide +kernel
  intro a b eq
  exact Fin.ext (distinct.getElem_inj_iff.mp eq)

def group (g : Fin 15) : (base.powersetCard 2 : Finset Edge) := ⟨groupEdge g, groupEdge_valid g⟩

lemma matching_agrees (m : Medium) : StarLabelTransport.isMatching base m ↔ isMedium m := by
  constructor
  · rintro ⟨size, inside, cov⟩
    refine ⟨size, fun e he => ⟨(inside e he).2, (inside e he).1⟩, ?_⟩
    intro p hp
    obtain ⟨a, ha, unique⟩ := cov p hp
    apply card_eq_one.mpr
    refine ⟨a, ?_⟩
    ext b
    simp only [mem_filter, mem_singleton]
    exact ⟨unique b, fun r => r.symm ▸ ha⟩
  · rintro ⟨size, inside, cov⟩
    refine ⟨size, fun e he => ⟨(inside e he).2, (inside e he).1⟩, ?_⟩
    intro p hp
    obtain ⟨a, unique⟩ := card_eq_one.mp (cov p hp)
    have h : ∀ b, (b ∈ m ∧ p ∈ b) ↔ b = a := by
      intro b
      have filt : b ∈ m.filter (fun e => p ∈ e) ↔ b ∈ m ∧ p ∈ b := mem_filter
      rw [← filt, unique, mem_singleton]
    exact ⟨a, (h a).mpr rfl, fun b hb => (h b).mp hb⟩

lemma exterior_agrees (c : Exterior) : StarLabelTransport.isExterior base c ↔ isExterior c := by
  constructor
  · rintro ⟨size, legal, disj⟩
    exact ⟨size, fun m h => (matching_agrees m).mp (legal m h), disj⟩
  · rintro ⟨size, legal, disj⟩
    exact ⟨size, fun m h => (matching_agrees m).mpr (legal m h), disj⟩

lemma exterior_sound (c : Exterior) (listed : c ∈ exterior) : isExterior c := by
  rw [← generatedExterior_eq] at listed
  obtain ⟨⟨a,i⟩, a_zip, rest⟩ := List.mem_flatMap.mp listed
  obtain ⟨⟨b,j⟩, b_zip, value⟩ := List.mem_filterMap.mp rest
  have ma : isMedium a := (medium_correct a).mp
    (List.mem_iff_getElem?.mpr ⟨i, List.mk_mem_zipIdx_iff_getElem?.mp a_zip⟩)
  have mb : isMedium b := (medium_correct b).mp
    (List.mem_iff_getElem?.mpr ⟨j, List.mk_mem_zipIdx_iff_getElem?.mp b_zip⟩)
  change (if i < j ∧ Disjoint a b then some {a,b} else none) = some c at value
  by_cases good : i < j ∧ Disjoint a b
  · have h : {a,b} = c := by simpa [good] using value
    subst c
    have ne : a ≠ b := by
      intro equal
      have self : Disjoint a a := equal.symm ▸ good.2
      obtain ⟨e, he⟩ := Finset.card_pos.mp (by rw [ma.1]; decide)
      exact Finset.disjoint_left.mp self he he
    refine ⟨by simp [ne], ?_, ?_⟩
    · intro m mem
      simp only [mem_insert, mem_singleton] at mem
      rcases mem with rfl | rfl <;> assumption
    · intro m hm n hn different
      simp only [mem_insert, mem_singleton] at hm hn
      rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
      · exact (different rfl).elim
      · exact good.2
      · exact good.2.symm
      · exact (different rfl).elim
  · simp [good] at value

end WeightFifteenLargeCatalog

namespace WeightFifteenLargeCatalog

open Finset FiniteSearchMasks

def vertexMask (g : Fin 15) : Nat :=
  ([32760, 32711, 32319, 29183, 4095, 28095, 23543, 16239,
      30431, 14334, 24317, 31611, 28635, 32237, 32694] : List Nat)[g.val]'g.isLt

def endpointMask (g : Fin 60) : Nat :=
  ([17, 33, 129, 257, 513, 1025, 4097, 8193,
      10, 34, 66, 130, 1026, 2050, 4098, 16386,
      12, 20, 68, 260, 516, 2052, 8196, 16388,
      136, 264, 520, 2056, 4104, 16392, 80, 272,
      1040, 2064, 4112, 8208, 96, 160, 544, 1056,
      8224, 16416, 1088, 2112, 8256, 16448, 640, 2176,
      4224, 8320, 768, 1280, 4352, 16640, 8704, 16896,
      5120, 17408, 6144, 10240] : List Nat)[g.val]'g.isLt

def eligibleMask (g : Fin 15) : Nat :=
  ([1152921504590069760, 1152917106576915708, 1134911294713099251, 14411560693780431, 3603047246675775, 732542662748126127, 339435142697119327, 962677200052385786,
      271188003732839925, 98892265553878784, 540976176994648183, 933436301946972123, 787844113021058493, 1097681697835385070, 1152855463058668032] : List Nat)[g.val]'g.isLt


def IndexedCover : Prop :=
  ∃ s : Fin 15 → Fin 6 → Finset (Fin 60),
    (∀ g i p, p ∈ s g i → (eligibleMask g).testBit p.val = true) ∧
    (∀ g i (m : Fin 15), (vertexMask g).testBit m.val = true →
      ∃! p : Fin 60, p ∈ s g i ∧ (endpointMask p).testBit m.val = true) ∧
    (∀ g p, (eligibleMask g).testBit p.val = true → ∃! i, p ∈ s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1

lemma medium_length : medium.length = 15 := by decide +kernel
lemma exterior_length : exterior.length = 60 := by decide +kernel

def exteriorAt (p : Fin 60) : Exterior := exterior[p.val]'p.isLt

lemma exteriorAt_pair (p : Fin 60) :
    exteriorAt p = {mediumAt (exteriorPair p).1, mediumAt (exteriorPair p).2} := by
  exact List.getElem_map (fun pair => ({mediumAt pair.1, mediumAt pair.2} : Exterior))
    (l := exteriorPairs) (i := p.val)

lemma mediumAt_injective : Function.Injective mediumAt := by
  have nodup : medium.Nodup := by decide +kernel
  intro a b eq
  exact Fin.ext (nodup.getElem_inj_iff.mp eq)

lemma exteriorAt_injective : Function.Injective exteriorAt := by
  have ordered : ∀ p, (exteriorPair p).1 < (exteriorPair p).2 := by decide +kernel
  have nodup : exteriorPairs.Nodup := by decide +kernel
  intro p q equal
  rw [exteriorAt_pair, exteriorAt_pair] at equal
  have mem_p_left : mediumAt (exteriorPair p).1 ∈
      ({mediumAt (exteriorPair q).1, mediumAt (exteriorPair q).2} : Exterior) := by rw [← equal]; simp
  have mem_p_right : mediumAt (exteriorPair p).2 ∈
      ({mediumAt (exteriorPair q).1, mediumAt (exteriorPair q).2} : Exterior) := by rw [← equal]; simp
  have mem_q_left : mediumAt (exteriorPair q).1 ∈
      ({mediumAt (exteriorPair p).1, mediumAt (exteriorPair p).2} : Exterior) := by rw [equal]; simp
  simp only [mem_insert, mem_singleton, mediumAt_injective.eq_iff] at mem_p_left mem_p_right mem_q_left
  have left : (exteriorPair p).1 = (exteriorPair q).1 := by
    rcases mem_p_left with h | h
    · exact h
    · have hp := ordered p
      have hq := ordered q
      rcases mem_q_left with h' | h' <;> omega
  have right : (exteriorPair p).2 = (exteriorPair q).2 := by
    rcases mem_p_right with h | h
    · have hp := ordered p
      omega
    · exact h
  exact Fin.ext (nodup.getElem_inj_iff.mp (Prod.ext left right))

lemma exteriorAt_complete (c : Exterior) (ok : isExterior c) :
    ∃ p : Fin 60, exteriorAt p = c := by
  obtain ⟨i, less, eq⟩ := List.mem_iff_getElem.mp (exterior_complete c ok)
  exact ⟨⟨i, by simpa only [exterior_length] using less⟩, eq⟩

lemma mediumAt_legal (m : Fin 15) : isMedium (mediumAt m) :=
  (medium_correct _).mp (List.getElem_mem _)

lemma exteriorAt_legal (p : Fin 60) : isExterior (exteriorAt p) :=
  exterior_sound _ (List.getElem_mem _)

set_option maxHeartbeats 250000000 in
set_option maxRecDepth 30000 in
lemma vertices_agree : ∀ g : Fin 15, vertexMask g = bitMask medium (fun m => decide (groupEdge g ∉ m)) :=
  by decide +kernel

set_option maxRecDepth 30000 in
lemma endpoints_agree : ∀ p : Fin 60,
    endpointMask p = 2^(exteriorPair p).1.val ||| 2^(exteriorPair p).2.val := by decide +kernel

set_option maxHeartbeats 250000000 in
set_option maxRecDepth 30000 in
lemma eligibility_agrees : ∀ g : Fin 15,
    eligibleMask g = bitMask exteriorPairs (fun (a,b) =>
      (vertexMask g).testBit a.val && (vertexMask g).testBit b.val) := by decide +kernel

lemma vertex_iff (g m : Fin 15) :
    (vertexMask g).testBit m.val = true ↔ groupEdge g ∉ mediumAt m := by
  rw [vertices_agree, bitMask_getElem_testBit medium _ m.val m.isLt]
  change decide (groupEdge g ∉ mediumAt m) = true ↔ _
  exact decide_eq_true_iff

lemma endpoint_iff (p : Fin 60) (m : Fin 15) :
    (endpointMask p).testBit m.val = true ↔ mediumAt m ∈ exteriorAt p := by
  rw [endpoints_agree, exteriorAt_pair]
  simp only [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
    mem_insert, mem_singleton, mediumAt_injective.eq_iff, Fin.val_inj]
  tauto

lemma eligible_iff (g : Fin 15) (p : Fin 60) :
    (eligibleMask g).testBit p.val = true ↔ ∀ m ∈ exteriorAt p, groupEdge g ∉ m := by
  rw [eligibility_agrees, bitMask_getElem_testBit exteriorPairs _ p.val p.isLt, exteriorAt_pair]
  change ((vertexMask g).testBit (exteriorPair p).1.val &&
    (vertexMask g).testBit (exteriorPair p).2.val) = true ↔ _
  simp only [Bool.and_eq_true, vertex_iff, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]

theorem exists_cover_to_indexed :
    (∃ L : Finset (Fin 111), L.card = 6 ∧
      ∃ stars, StarLabelTransport.StarCover L stars) → IndexedCover := by
  rintro ⟨L, six, stars, valid⟩
  have standardized := StarLabelTransport.standard_star_cover L six stars valid
  rw [← base_eq] at standardized
  obtain ⟨stars', cover⟩ := standardized
  classical
  let indexed := fun (g : Fin 15) (i : Fin 6) =>
    univ.filter fun p : Fin 60 => exteriorAt p ∈ stars' (group g) i
  have at_star (g : Fin 15) (i : Fin 6) (p : Fin 60) :
      p ∈ indexed g i ↔ exteriorAt p ∈ stars' (group g) i := by simp [indexed]
  refine ⟨indexed, ?_, ?_, ?_, ?_⟩
  · intro g i p within
    exact (eligible_iff g p).mpr (cover.1 (group g) i _ ((at_star g i p).mp within)).2
  · intro g index m required
    obtain ⟨c, both, unique⟩ :=
      cover.2.1 (group g) index (mediumAt m) ((matching_agrees _).mpr (mediumAt_legal m))
        ((vertex_iff g m).mp required)
    have c_legal := (exterior_agrees _).mp (cover.1 (group g) index c both.1).1
    obtain ⟨p, rfl⟩ := exteriorAt_complete c c_legal
    exact ⟨p, ⟨(at_star g index p).mpr both.1, (endpoint_iff p m).mpr both.2⟩,
      fun q h => exteriorAt_injective (unique _ ⟨(at_star g index q).mp h.1, (endpoint_iff q m).mp h.2⟩)⟩
  · intro g p required
    obtain ⟨i, hit, unique⟩ := cover.2.2.1 (group g) (exteriorAt p)
      ((exterior_agrees _).mpr (exteriorAt_legal p)) ((eligible_iff g p).mp required)
    exact ⟨i, (at_star g i p).mpr hit, fun j h => unique j ((at_star g j p).mp h)⟩
  · intro g h i j different
    have ne : group g ≠ group h := fun eq => different (groupEdge_injective (congrArg Subtype.val eq))
    have smaller : (indexed g i ∩ indexed h j).card ≤
        (stars' (group g) i ∩ stars' (group h) j).card := by
      refine Finset.card_le_card_of_injOn exteriorAt ?_ exteriorAt_injective.injOn
      intro p hp
      have both := mem_inter.mp hp
      exact mem_inter.mpr ⟨(at_star g i p).mp both.1, (at_star h j p).mp both.2⟩
    exact smaller.trans (cover.2.2.2 (group g) (group h) ne i j)

end WeightFifteenLargeCatalog

namespace WeightFifteenLargeCatalog


lemma row_testBit (packed width base index : Nat) (within : index < width) :
    (((packed >>> (width * base)) &&& (2^width-1)).testBit index) =
      packed.testBit (width * base + index) := by
  simp only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true within, Bool.and_true, Nat.add_comm]


set_option maxRecDepth 10000 in
lemma row_eligible : ∀ g : Fin 15,
    ((0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000 : Nat) >>> (60 * g.val)) &&& (2^60-1) = eligibleMask g := by decide +kernel

lemma packed_eligible (g : Fin 15) (p : Fin 60) :
    (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000 : Nat).testBit (60*g.val+p.val) = (eligibleMask g).testBit p.val := by
  rw [← row_testBit _ _ _ _ p.isLt, row_eligible]

set_option maxRecDepth 10000 in
lemma row_vertex : ∀ g : Fin 15,
    ((0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8 : Nat) >>> (15 * g.val)) &&& (2^15-1) = vertexMask g := by decide +kernel

lemma packed_vertex (g : Fin 15) (m : Fin 15) :
    (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8 : Nat).testBit (15*g.val+m.val) = (vertexMask g).testBit m.val := by
  rw [← row_testBit _ _ _ _ m.isLt, row_vertex]

set_option maxRecDepth 10000 in
lemma row_endpoint : ∀ p : Fin 60,
    ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011 : Nat) >>> (15 * p.val)) &&& (2^15-1) = endpointMask p := by decide +kernel

lemma packed_endpoint (p : Fin 60) (m : Fin 15) :
    (0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011 : Nat).testBit (15*p.val+m.val) = (endpointMask p).testBit m.val := by
  rw [← row_testBit _ _ _ _ m.isLt, row_endpoint]

end WeightFifteenLargeCatalog

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1.H1 := by
  intro cover
  have indexed := WeightFifteenLargeCatalog.exists_cover_to_indexed cover
  simpa only [WeightFifteenLargeCatalog.IndexedCover,
    WeightFifteenLargeCatalog.packed_eligible, WeightFifteenLargeCatalog.packed_vertex,
    WeightFifteenLargeCatalog.packed_endpoint] using indexed
