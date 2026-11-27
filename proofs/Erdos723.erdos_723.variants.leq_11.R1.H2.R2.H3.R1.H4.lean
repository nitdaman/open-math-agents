import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1
import Mathlib.Data.Finset.SymmDiff

/-! Two six-secants would produce a twelve-point even set meeting one line four times. -/
-- Credit: @avivorly

open Finset
open scoped symmDiff

namespace OrderTen

def pointsOnLine (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (l : Fin 111) :
    Finset (Fin 111) :=
  S.filter fun p => incidence l p = true

end OrderTen

namespace OrderTenCaseShapes

def atPoint (incidence : Fin 111 → Fin 111 → Bool) (p : Fin 111) : Finset (Fin 111) :=
  Finset.univ.filter fun l => incidence l p = true

lemma sum_pencil_avoiding_center (incidence : Fin 111 → Fin 111 → Bool)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (p : Fin 111) (not_center : p ∉ S) :
    (∑ l ∈ atPoint incidence p, (OrderTen.pointsOnLine incidence S l).card) = S.card := by
  classical
  calc
    _ = ∑ l ∈ atPoint incidence p, ∑ q ∈ S, if incidence l q = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      simp [OrderTen.pointsOnLine]
    _ = ∑ q ∈ S, (1 : ℕ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      have distinct : p ≠ q := fun equal => not_center (equal.symm ▸ hq)
      obtain ⟨l, on_both, unique⟩ := columnPairs p q distinct
      have one_line : (atPoint incidence p).filter (fun k => incidence k q = true) = {l} := by
        ext k
        simp only [atPoint, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨unique k, fun eq => eq.symm ▸ on_both⟩
      rw [← Finset.sum_filter, one_line]
      simp
    _ = _ := by simp

end OrderTenCaseShapes

open Matrix Finset

namespace OrderTenCaseShapes

lemma even_set_line_bound (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111))
    (even_lines : ∀ l, 2 ∣ (OrderTen.pointsOnLine incidence S l).card) (l : Fin 111) :
    (OrderTen.pointsOnLine incidence S l).card ≤ S.card - 10 := by
  classical
  by_cases empty : (OrderTen.pointsOnLine incidence S l).card = 0
  · simp [empty]
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero empty)
  obtain ⟨in_S, on_l⟩ := Finset.mem_filter.mp hp
  let L := atPoint incidence p
  have l_mem : l ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, on_l⟩
  have L_size : L.card = 11 := columnSize p
  let k := fun m => (OrderTen.pointsOnLine incidence (S.erase p) m).card
  have total : (∑ m ∈ L, k m) = S.card - 1 := by
    dsimp only [L, k]
    rw [sum_pencil_avoiding_center incidence columnPairs _ p (by simp),
      Finset.card_erase_of_mem in_S]
  have on_pencil (m : Fin 111) (hm : m ∈ L) :
      (OrderTen.pointsOnLine incidence S m).card = k m + 1 := by
    have p_mem : p ∈ OrderTen.pointsOnLine incidence S m :=
      Finset.mem_filter.mpr ⟨in_S, (Finset.mem_filter.mp hm).2⟩
    have erase_commutes : OrderTen.pointsOnLine incidence (S.erase p) m =
        (OrderTen.pointsOnLine incidence S m).erase p := by
      ext q
      simp [OrderTen.pointsOnLine, and_assoc]
    dsimp only [k]
    rw [erase_commutes, Finset.card_erase_of_mem p_mem]
    have := Finset.card_pos.mpr ⟨p, p_mem⟩
    omega
  have one_le (m : Fin 111) (hm : m ∈ L) : 1 ≤ k m := by
    have even := even_lines m
    rw [on_pencil m hm] at even
    omega
  have other_lines := Finset.sum_le_sum (s := L.erase l)
    (f := fun _ => (1 : ℕ)) (g := k) (fun m hm => one_le m (Finset.mem_of_mem_erase hm))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem l_mem,
    L_size] at other_lines
  have separated := Finset.sum_erase_add L k l_mem
  rw [total] at separated
  have lower := one_le l l_mem
  rw [on_pencil l l_mem]
  omega


def line (incidence : Fin 111 → Fin 111 → Bool) (l : Fin 111) : Finset (Fin 111) :=
  Finset.univ.filter fun p => incidence l p = true

lemma card_toggle {α : Type} [DecidableEq α] (S T : Finset α) :
    (S ∆ T).card + 2 * (S ∩ T).card = S.card + T.card := by
  have separate : Disjoint (S \ T) (T \ S) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint separate]
  have sum := Finset.card_sdiff_add_card_inter S T
  have other := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at other
  omega

lemma points_toggle (incidence : Fin 111 → Fin 111 → Bool) (S T : Finset (Fin 111)) (l : Fin 111) :
    OrderTen.pointsOnLine incidence (S ∆ T) l =
      OrderTen.pointsOnLine incidence S l ∆ OrderTen.pointsOnLine incidence T l := by
  ext p
  simp only [OrderTen.pointsOnLine, Finset.mem_filter, Finset.mem_symmDiff]
  tauto

lemma lines_share_point (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (l m : Fin 111) (distinct : l ≠ m) :
    ∃ p, incidence l p = true ∧ incidence m p = true ∧
      OrderTen.pointsOnLine incidence (line incidence l) m = {p} := by
  obtain ⟨p, both, only⟩ := rowPairs l m distinct
  refine ⟨p, both.1, both.2, ?_⟩
  ext q
  simp only [OrderTen.pointsOnLine, line, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨only q, fun same => same.symm ▸ both⟩

lemma line_intersection_odd (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (line incidence l).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (l m : Fin 111) : (OrderTen.pointsOnLine incidence (line incidence l) m).card % 2 = 1 := by
  by_cases eq : l = m
  · subst m
    have same : OrderTen.pointsOnLine incidence (line incidence l) l = line incidence l := by
      ext p
      simp [OrderTen.pointsOnLine, line]
    rw [same, rowSize]
  · obtain ⟨p, _, _, intersect⟩ := lines_share_point incidence rowPairs l m eq
    simp [intersect]

lemma no_two_six_secants (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (line incidence l).card = 11)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 16)
    (even : ∀ l, 2 ∣ (OrderTen.pointsOnLine incidence S l).card)
    (bounded : ∀ p ∈ S, ((Finset.univ : Finset (Fin 111)).filter fun l =>
      (OrderTen.pointsOnLine incidence S l).card = 6 ∧ incidence l p = true).card ≤ 1)
    (l m : Fin 111) (different : l ≠ m)
    (l_six : (OrderTen.pointsOnLine incidence S l).card = 6)
    (m_six : (OrderTen.pointsOnLine incidence S m).card = 6) : False := by
  obtain ⟨p, pl, pm, share⟩ := lines_share_point incidence rowPairs l m different
  have outside : p ∉ S := by
    intro inside
    have small := bounded p inside
    let D := (Finset.univ : Finset (Fin 111)).filter fun a =>
      (OrderTen.pointsOnLine incidence S a).card = 6 ∧ incidence a p = true
    have D_l : l ∈ D := by simp [D, l_six, pl]
    have D_m : m ∈ D := by simp [D, m_six, pm]
    have two := Finset.card_le_card (show ({l,m} : Finset (Fin 111)) ⊆ D by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption)
    simp [different] at two
    exact (Nat.not_succ_le_self 1) (two.trans small)
  let L := line incidence l
  let M := line incidence m
  let T := S ∆ L
  let U := T ∆ M
  have intersect (A : Finset (Fin 111)) (r : Fin 111) :
      A ∩ line incidence r = OrderTen.pointsOnLine incidence A r := by
    ext q
    simp [line, OrderTen.pointsOnLine]
  have T_size : T.card = 15 := by
    have count := card_toggle S L
    rw [intersect, l_six, rowSize l, size] at count
    change T.card + 12 = 27 at count
    omega
  have T_m : (OrderTen.pointsOnLine incidence T m).card = 7 := by
    have count := card_toggle (OrderTen.pointsOnLine incidence S m) (OrderTen.pointsOnLine incidence L m)
    rw [← points_toggle, show OrderTen.pointsOnLine incidence L m = {p} from share, m_six] at count
    have empty : OrderTen.pointsOnLine incidence S m ∩ {p} = ∅ := by
      ext q
      simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨hq, rfl⟩
      exact outside (Finset.mem_filter.mp hq).1
    rw [empty, Finset.card_empty, Finset.card_singleton] at count
    omega
  have U_size : U.card = 12 := by
    have count := card_toggle T M
    rw [intersect, rowSize m, T_m, T_size] at count
    change U.card + 14 = 26 at count
    omega
  have row_self : OrderTen.pointsOnLine incidence M m = M := by
    ext q
    simp [OrderTen.pointsOnLine, M, line]
  have T_m_inside : OrderTen.pointsOnLine incidence T m ⊆ M :=
    fun q hq => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
  have U_m : (OrderTen.pointsOnLine incidence U m).card = 4 := by
    have count := card_toggle (OrderTen.pointsOnLine incidence T m) (OrderTen.pointsOnLine incidence M m)
    rw [← points_toggle, row_self, Finset.inter_eq_left.mpr T_m_inside, rowSize m, T_m] at count
    change (OrderTen.pointsOnLine incidence U m).card + 14 = 18 at count
    omega
  have U_even (r : Fin 111) : 2 ∣ (OrderTen.pointsOnLine incidence U r).card := by
    have a := card_toggle (OrderTen.pointsOnLine incidence S r) (OrderTen.pointsOnLine incidence L r)
    have b := card_toggle (OrderTen.pointsOnLine incidence T r) (OrderTen.pointsOnLine incidence M r)
    rw [← points_toggle] at a b
    change (OrderTen.pointsOnLine incidence T r).card + _ = _ at a
    change (OrderTen.pointsOnLine incidence U r).card + _ = _ at b
    have pL := line_intersection_odd incidence rowSize rowPairs l r
    have pM := line_intersection_odd incidence rowSize rowPairs m r
    change (OrderTen.pointsOnLine incidence L r).card % 2 = 1 at pL
    change (OrderTen.pointsOnLine incidence M r).card % 2 = 1 at pM
    have pS := even r
    omega
  have bound := even_set_line_bound incidence columnSize columnPairs U U_even m
  rw [U_size, U_m] at bound
  omega

end OrderTenCaseShapes

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1.H4 := by
  intro incidence rowSize columnSize rowPairs columnPairs
  dsimp only
  rintro ⟨S, ⟨size, shape, counts, degrees⟩, two⟩
  let P := (Finset.univ : Finset (Fin 111)).filter fun l =>
    (OrderTen.pointsOnLine incidence S l).card = 6
  have two_secants : P.card = 2 := two
  obtain ⟨l, m, distinct, same⟩ := Finset.card_eq_two.mp two_secants
  have hit_a : l ∈ P := by simp [same]
  have hit_b : m ∈ P := by simp [same]
  refine OrderTenCaseShapes.no_two_six_secants incidence rowSize columnSize rowPairs columnPairs
    S size (fun r => (shape r).1) ?_ l m distinct (Finset.mem_filter.mp hit_a).2 (Finset.mem_filter.mp hit_b).2
  intro p hp
  have d := degrees p hp
  unfold OrderTen.pointsOnLine
  omega
