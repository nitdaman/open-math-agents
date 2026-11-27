import OMAReductions.R_Erdos128_erdos_128_R1

-- Reduction Erdos128.erdos_128.R1.H1.R1 of step Erdos128.erdos_128.R1.H1
-- Credit: @ashnewmanjones
--
-- Step H1 is the dense case of Erdős 128 (triangle-free, e ≥ n^2 / 5), proved by Keevash and
-- Sudakov, Sparse halves in triangle-free graphs, JCTB 96 (2006), Theorem 1.1. Their proof first
-- reduces to n divisible by 10 with the blow-up G(10); this file PROVES that reduction:
--   * G(10) = G.comap Prod.fst on V × Fin 10 is triangle-free with exactly 100 e edges;
--   * a sparse half S of G(10) gives, through its blob profile a_u = |S ∩ ({u} × Fin 10)| and a
--     pipage (shifting) argument (the edge form is concave along any shift between two partially
--     used blobs, so an endpoint is no worse), a profile with at most one partial blob, whose
--     full blobs form a set of ⌊n/2⌋ vertices of G spanning at most n^2 / 50 edges.
-- What remains are the two cases of their proof for n divisible by 10, split at maximum degree
-- (2/5 + 1/135) n = 11 n / 27:
--   H1: some vertex has degree ≥ 11 n / 27 (their Case 1),
--   H2: every degree is < 11 n / 27 (their Case 2; uses the Andrásfai–Erdős–Sós theorem).

namespace OMA.R_Erdos128_erdos_128_R1_H1_R1

open Finset
-- Keevash–Sudakov Case 1 (t ≥ 1/135, i.e. maximum degree ≥ 11n/27), for n divisible by 10.
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 → 10 ∣ Fintype.card V →
    Fintype.card V ^ 2 ≤ 5 * G.edgeSet.ncard →
    (∃ v, 11 * Fintype.card V ≤ 27 * (G.neighborSet v).ncard) →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

-- Keevash–Sudakov Case 2 (t < 1/135, i.e. maximum degree < 11n/27), for n divisible by 10.
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 → 10 ∣ Fintype.card V →
    Fintype.card V ^ 2 ≤ 5 * G.edgeSet.ncard →
    (∀ v, 27 * (G.neighborSet v).ncard < 11 * Fintype.card V) →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

variable {V : Type} [Fintype V] [DecidableEq V]

-- Shifting δ units from coordinate w to coordinate u changes the quadratic form by
-- 2 δ ((A a)_u - (A a)_w) - 2 A_uw δ².
lemma shift_quad (A : V → V → ℤ) (hsym : ∀ x y, A x y = A y x) (hdiag : ∀ x, A x x = 0)
    (a : V → ℤ) (u w : V) (huw : u ≠ w) (δ : ℤ) :
    ∑ x, ∑ y, A x y * (a x + (if x = u then δ else 0) - (if x = w then δ else 0)) *
        (a y + (if y = u then δ else 0) - (if y = w then δ else 0)) =
      ∑ x, ∑ y, A x y * a x * a y + 2 * δ * (∑ y, A u y * a y - ∑ y, A w y * a y) -
        2 * A u w * δ ^ 2 := by
  have e1 : ∀ x y, A x y * (a x + (if x = u then δ else 0) - (if x = w then δ else 0)) *
      (a y + (if y = u then δ else 0) - (if y = w then δ else 0)) =
      A x y * a x * a y + A x y * a x * ((if y = u then δ else 0) - (if y = w then δ else 0)) +
      A x y * a y * ((if x = u then δ else 0) - (if x = w then δ else 0)) +
      A x y * ((if x = u then δ else 0) - (if x = w then δ else 0)) *
        ((if y = u then δ else 0) - (if y = w then δ else 0)) := by intro x y; ring
  simp only [e1, Finset.sum_add_distrib]
  have t1 : ∑ x, ∑ y, A x y * a x * ((if y = u then δ else 0) - (if y = w then δ else 0)) =
      δ * (∑ y, A u y * a y - ∑ y, A w y * a y) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> rw [hsym] <;> ring
  have t2 : ∑ x, ∑ y, A x y * a y * ((if x = u then δ else 0) - (if x = w then δ else 0)) =
      δ * (∑ y, A u y * a y - ∑ y, A w y * a y) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
    rw [Finset.sum_comm (f := fun x y => if x = u then A x y * a y * δ else 0),
      Finset.sum_comm (f := fun x y => if x = w then A x y * a y * δ else 0)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> ring
  have t3 : ∑ x, ∑ y, A x y * ((if x = u then δ else 0) - (if x = w then δ else 0)) *
      ((if y = u then δ else 0) - (if y = w then δ else 0)) = -2 * A u w * δ ^ 2 := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hdiag u, hdiag w, hsym w u]
    ring
  rw [t1, t2, t3]
  ring

-- One pipage step: two partially used coordinates u ≠ w; shifting toward an endpoint does not
-- increase the (concave in the shift) quadratic form and removes u or w from the partial set.
lemma shift_once (A : V → V → ℤ) (hsym : ∀ x y, A x y = A y x) (hdiag : ∀ x, A x x = 0)
    (hnn : ∀ x y, 0 ≤ A x y) (a : V → ℤ) (hb : ∀ x, 0 ≤ a x ∧ a x ≤ 10) (u w : V) (huw : u ≠ w)
    (hu : 0 < a u ∧ a u < 10) (hw : 0 < a w ∧ a w < 10) :
    ∃ b : V → ℤ, (∀ x, 0 ≤ b x ∧ b x ≤ 10) ∧ ∑ x, b x = ∑ x, a x ∧
      ∑ x, ∑ y, A x y * b x * b y ≤ ∑ x, ∑ y, A x y * a x * a y ∧
      univ.filter (fun x => 0 < b x ∧ b x < 10) ⊂ univ.filter (fun x => 0 < a x ∧ a x < 10) := by
  have key : ∀ δ : ℤ, 0 ≤ a u + δ → a u + δ ≤ 10 → 0 ≤ a w - δ → a w - δ ≤ 10 →
      δ * (∑ y, A u y * a y - ∑ y, A w y * a y) ≤ 0 →
      (a u + δ = 0 ∨ a u + δ = 10 ∨ a w - δ = 0 ∨ a w - δ = 10) →
      ∃ b : V → ℤ, (∀ x, 0 ≤ b x ∧ b x ≤ 10) ∧ ∑ x, b x = ∑ x, a x ∧
        ∑ x, ∑ y, A x y * b x * b y ≤ ∑ x, ∑ y, A x y * a x * a y ∧
        univ.filter (fun x => 0 < b x ∧ b x < 10) ⊂ univ.filter (fun x => 0 < a x ∧ a x < 10) := by
    intro δ h1 h2 h3 h4 h5 h6
    have bu : a u + (if u = u then δ else 0) - (if u = w then δ else 0) = a u + δ := by
      simp [huw]
    have bw : a w + (if w = u then δ else 0) - (if w = w then δ else 0) = a w - δ := by
      simp [Ne.symm huw]
    have bx : ∀ x, x ≠ u → x ≠ w →
        a x + (if x = u then δ else 0) - (if x = w then δ else 0) = a x := by
      intro x hxu hxw; simp [hxu, hxw]
    refine ⟨fun x => a x + (if x = u then δ else 0) - (if x = w then δ else 0), ?_, ?_, ?_, ?_⟩
    · intro x
      by_cases hxu : x = u
      · subst hxu; dsimp only; rw [bu]; exact ⟨h1, h2⟩
      by_cases hxw : x = w
      · subst hxw; dsimp only; rw [bw]; exact ⟨h3, h4⟩
      dsimp only; rw [bx x hxu hxw]; exact hb x
    · simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    · rw [shift_quad A hsym hdiag a u w huw δ]
      nlinarith [hnn u w, sq_nonneg δ, mul_nonneg (hnn u w) (sq_nonneg δ)]
    · rw [Finset.ssubset_iff_of_subset]
      · rcases h6 with h | h | h | h
        · exact ⟨u, by simp [hu], by simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_true, huw, if_false, sub_zero]; omega⟩
        · exact ⟨u, by simp [hu], by simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_true, huw, if_false, sub_zero]; omega⟩
        · exact ⟨w, by simp [hw], by simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_true, Ne.symm huw, if_false, add_zero]; omega⟩
        · exact ⟨w, by simp [hw], by simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_true, Ne.symm huw, if_false, add_zero]; omega⟩
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        by_cases hxu : x = u
        · subst hxu; exact hu
        by_cases hxw : x = w
        · subst hxw; exact hw
        rw [bx x hxu hxw] at hx; exact hx
  by_cases hα : ∑ y, A u y * a y - ∑ y, A w y * a y ≤ 0
  · refine key (min (10 - a u) (a w)) (by omega) (by omega) (by omega) (by omega) ?_ (by omega)
    exact mul_nonpos_of_nonneg_of_nonpos (by omega) hα
  · push Not at hα
    refine key (-(min (a u) (10 - a w))) (by omega) (by omega) (by omega) (by omega) ?_ (by omega)
    exact mul_nonpos_of_nonpos_of_nonneg (by omega) hα.le

-- Iterating: some profile with the same total, no larger form, and at most one partial coordinate.
lemma shift_all (A : V → V → ℤ) (hsym : ∀ x y, A x y = A y x) (hdiag : ∀ x, A x x = 0)
    (hnn : ∀ x y, 0 ≤ A x y) : ∀ (n : ℕ) (a : V → ℤ),
    (univ.filter (fun x => 0 < a x ∧ a x < 10)).card = n → (∀ x, 0 ≤ a x ∧ a x ≤ 10) →
    ∃ b : V → ℤ, (∀ x, 0 ≤ b x ∧ b x ≤ 10) ∧ ∑ x, b x = ∑ x, a x ∧
      ∑ x, ∑ y, A x y * b x * b y ≤ ∑ x, ∑ y, A x y * a x * a y ∧
      ∀ u w, (0 < b u ∧ b u < 10) → (0 < b w ∧ b w < 10) → u = w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hn hb
    by_cases h : ∃ u w, u ≠ w ∧ (0 < a u ∧ a u < 10) ∧ (0 < a w ∧ a w < 10)
    · obtain ⟨u, w, huw, hu, hw⟩ := h
      obtain ⟨b, hbb, hbs, hbF, hss⟩ := shift_once A hsym hdiag hnn a hb u w huw hu hw
      obtain ⟨c, hcb, hcs, hcF, hc1⟩ :=
        ih _ (hn ▸ Finset.card_lt_card hss) b rfl hbb
      exact ⟨c, hcb, hcs.trans hbs, hcF.trans hbF, hc1⟩
    · refine ⟨a, hb, rfl, le_rfl, fun u w hu hw => ?_⟩
      by_contra huw
      exact h ⟨u, w, huw, hu, hw⟩

/-! ## The blow-up G(10) -/

open OMA.R_Erdos128_erdos_128_R1

lemma blow_cliqueFree (G : SimpleGraph V) (hcf : G.CliqueFree 3) :
    (G.comap (Prod.fst : V × Fin 10 → V)).CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  exact hcf {a.1, b.1, c.1} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

lemma blow_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.comap (Prod.fst : V × Fin 10 → V)).edgeSet.ncard = 100 * G.edgeSet.ncard := by
  classical
  set H := G.comap (Prod.fst : V × Fin 10 → V)
  have hH := deg_sum_univ H
  have hG := deg_sum_univ G
  have hdeg : ∀ p : V × Fin 10, ((univ : Finset (V × Fin 10)).filter (H.Adj p)).card =
      10 * ((univ : Finset V).filter (G.Adj p.1)).card := by
    intro p
    have : (univ : Finset (V × Fin 10)).filter (H.Adj p) =
        ((univ : Finset V).filter (G.Adj p.1)) ×ˢ (univ : Finset (Fin 10)) := by
      ext q; simp [H]
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
  simp_rw [hdeg] at hH
  rw [← Finset.mul_sum, Fintype.sum_prod_type] at hH
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hH
  rw [← Finset.mul_sum, hG] at hH
  omega

-- The degree sum of S in the blow-up is the quadratic form of its blob profile.
lemma blow_profile (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (V × Fin 10)) :
    (∑ p ∈ S, (S.filter ((G.comap (Prod.fst : V × Fin 10 → V)).Adj p)).card : ℤ) =
      ∑ u, ∑ w, (if G.Adj u w then (1 : ℤ) else 0) * ((S.filter (fun p => p.1 = u)).card : ℤ) *
        ((S.filter (fun p => p.1 = w)).card : ℤ) := by
  classical
  have hcard : ∀ p : V × Fin 10, ((S.filter ((G.comap (Prod.fst : V × Fin 10 → V)).Adj p)).card : ℤ) =
      ∑ w, (if G.Adj p.1 w then (1 : ℤ) else 0) * ((S.filter (fun q => q.1 = w)).card : ℤ) := by
    intro p
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => Finset.mem_univ _)]
    push_cast
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.filter_filter]
    split_ifs with h
    · simp only [one_mul]
      congr 2
      ext q
      simp only [Finset.mem_filter, SimpleGraph.comap_adj]
      constructor
      · rintro ⟨hq, -, hqw⟩; exact ⟨hq, hqw⟩
      · rintro ⟨hq, hqw⟩; exact ⟨hq, hqw ▸ h, hqw⟩
    · simp only [zero_mul, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro q - ⟨hadj, hqw⟩
      exact h (hqw ▸ hadj)
  simp_rw [hcard]
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := univ) (g := Prod.fst)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have : ∀ p ∈ S.filter (fun p => p.1 = u),
      ∑ w, (if G.Adj p.1 w then (1 : ℤ) else 0) * ((S.filter (fun q => q.1 = w)).card : ℤ) =
      ∑ w, (if G.Adj u w then (1 : ℤ) else 0) * ((S.filter (fun q => q.1 = w)).card : ℤ) := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R1.H1 := by
  intro h1 h2 V _ G hcf hdense
  classical
  set n := Fintype.card V with hn
  set H := G.comap (Prod.fst : V × Fin 10 → V) with hHdef
  have hHn : Fintype.card (V × Fin 10) = 10 * n := by
    rw [Fintype.card_prod, Fintype.card_fin, hn, mul_comm]
  have hHcf := blow_cliqueFree G hcf
  have hHe := blow_edges G
  -- a sparse half of the blow-up
  obtain ⟨W, hW1, hW2⟩ : ∃ W : Set (V × Fin 10), 2 * W.ncard + 1 ≥ 10 * n ∧
      50 * (H.induce W).edgeSet.ncard ≤ (10 * n) ^ 2 := by
    have hdiv : 10 ∣ Fintype.card (V × Fin 10) := by rw [hHn]; exact dvd_mul_right 10 n
    have hdH : Fintype.card (V × Fin 10) ^ 2 ≤ 5 * H.edgeSet.ncard := by
      rw [hHn, hHe]; nlinarith
    by_cases hc : ∃ v, 11 * Fintype.card (V × Fin 10) ≤ 27 * (H.neighborSet v).ncard
    · obtain ⟨W, a, b⟩ := h1 (V × Fin 10) H hHcf hdiv hdH hc
      rw [hHn] at a b; exact ⟨W, a, b⟩
    · push Not at hc
      obtain ⟨W, a, b⟩ := h2 (V × Fin 10) H hHcf hdiv hdH hc
      rw [hHn] at a b; exact ⟨W, a, b⟩
  -- as a finset, cut down to exactly 5n vertices
  set S := W.toFinset with hS
  have hSc : S.card = W.ncard := (Set.ncard_eq_toFinset_card' W).symm
  have hSD : ∑ p ∈ S, (S.filter (H.Adj p)).card ≤ 4 * n ^ 2 := by
    have := two_mul_induce H S
    rw [hS, Set.coe_toFinset] at this
    rw [hS]; nlinarith
  obtain ⟨S0, hS0S, hS0⟩ := Finset.exists_subset_card_eq (show 5 * n ≤ S.card by omega)
  have hS0D : ∑ p ∈ S0, (S0.filter (H.Adj p)).card ≤ 4 * n ^ 2 := by
    refine le_trans ?_ hSD
    calc ∑ p ∈ S0, (S0.filter (H.Adj p)).card ≤ ∑ p ∈ S0, (S.filter (H.Adj p)).card :=
          Finset.sum_le_sum fun p _ => Finset.card_le_card (Finset.filter_subset_filter _ hS0S)
      _ ≤ ∑ p ∈ S, (S.filter (H.Adj p)).card := Finset.sum_le_sum_of_subset hS0S
  -- the blob profile of S0
  set a : V → ℤ := fun u => ((S0.filter (fun p => p.1 = u)).card : ℤ) with ha
  have hab : ∀ u, 0 ≤ a u ∧ a u ≤ 10 := by
    intro u
    refine ⟨by positivity, ?_⟩
    have : (S0.filter (fun p => p.1 = u)).card ≤ 10 := by
      calc (S0.filter (fun p => p.1 = u)).card ≤ (({u} : Finset V) ×ˢ (univ : Finset (Fin 10))).card := by
            apply Finset.card_le_card
            intro p hp
            exact Finset.mem_product.mpr
              ⟨Finset.mem_singleton.mpr (Finset.mem_filter.mp hp).2, Finset.mem_univ _⟩
        _ = 10 := by simp
    simp only [ha]; exact_mod_cast this
  have hasum : ∑ u, a u = 5 * n := by
    have := Finset.card_eq_sum_card_fiberwise (s := S0) (t := univ) (f := Prod.fst)
      (fun _ _ => Finset.mem_univ _)
    simp only [ha]
    rw [hS0] at this
    exact_mod_cast this.symm
  set A : V → V → ℤ := fun u w => if G.Adj u w then 1 else 0 with hA
  have hAsym : ∀ x y, A x y = A y x := fun x y => by simp only [hA, G.adj_comm]
  have hAdiag : ∀ x, A x x = 0 := fun x => by simp [hA]
  have hAnn : ∀ x y, 0 ≤ A x y := fun x y => by simp only [hA]; split_ifs <;> norm_num
  have hFa : ∑ x, ∑ y, A x y * a x * a y ≤ 4 * (n : ℤ) ^ 2 := by
    have := blow_profile G S0
    simp only [hA, ha]
    rw [← this]
    exact_mod_cast hS0D
  obtain ⟨b, hbb, hbs, hbF, hb1⟩ := shift_all A hAsym hAdiag hAnn _ a rfl hab
  -- the full blobs of b
  set T := (univ : Finset V).filter (fun u => b u = 10) with hT
  have hpart : (univ.filter (fun u => 0 < b u ∧ b u < 10)).card ≤ 1 :=
    Finset.card_le_one.mpr fun u hu w hw => hb1 u w (Finset.mem_filter.mp hu).2
      (Finset.mem_filter.mp hw).2
  have hsplit : ∑ u, b u = 10 * T.card + ∑ u ∈ univ.filter (fun u => 0 < b u ∧ b u < 10), b u := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun u => b u = 10)]
    have e1 : ∑ u ∈ univ.filter (fun u => b u = 10), b u = 10 * T.card := by
      rw [Finset.sum_congr rfl fun u hu => (Finset.mem_filter.mp hu).2, Finset.sum_const,
        nsmul_eq_mul, mul_comm]
    have e2 : ∑ u ∈ univ.filter (fun u => ¬ b u = 10), b u =
        ∑ u ∈ univ.filter (fun u => 0 < b u ∧ b u < 10), b u := by
      rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun u => ¬ b u = 10))
        (fun u => 0 < b u)]
      have z : ∑ u ∈ (univ.filter (fun u => ¬ b u = 10)).filter (fun u => ¬ 0 < b u), b u = 0 :=
        Finset.sum_eq_zero fun u hu => by
          simp only [Finset.mem_filter] at hu
          have := hbb u; omega
      rw [z, add_zero, Finset.filter_filter]
      congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hbb u; omega
    rw [e1, e2]
  have hrest : ∑ u ∈ univ.filter (fun u => 0 < b u ∧ b u < 10), b u ≤ 9 := by
    calc ∑ u ∈ univ.filter (fun u => 0 < b u ∧ b u < 10), b u
        ≤ ∑ _u ∈ univ.filter (fun u => 0 < b u ∧ b u < 10), (9 : ℤ) :=
          Finset.sum_le_sum fun u hu => by have := (Finset.mem_filter.mp hu).2; omega
      _ = 9 * (univ.filter (fun u => 0 < b u ∧ b u < 10)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ 9 := by
          have : ((univ.filter (fun u => 0 < b u ∧ b u < 10)).card : ℤ) ≤ 1 := by exact_mod_cast hpart
          linarith
  have hrest0 : 0 ≤ ∑ u ∈ univ.filter (fun u => 0 < b u ∧ b u < 10), b u :=
    Finset.sum_nonneg fun u _ => (hbb u).1
  have hTcard : 2 * T.card + 1 ≥ n := by
    have h5 : (5 * n : ℤ) = 10 * T.card + ∑ u ∈ univ.filter (fun u => 0 < b u ∧ b u < 10), b u := by
      rw [← hasum, hbs.symm.trans hsplit]
    have : (n : ℤ) ≤ 2 * T.card + 1 := by linarith
    exact_mod_cast this
  -- the full blobs give a sparse half of G
  have hFb : 100 * (∑ u ∈ T, (T.filter (G.Adj u)).card : ℤ) ≤ ∑ x, ∑ y, A x y * b x * b y := by
    have hT10 : ∀ u ∈ T, b u = 10 := fun u hu => (Finset.mem_filter.mp hu).2
    calc 100 * (∑ u ∈ T, (T.filter (G.Adj u)).card : ℤ)
        = ∑ x ∈ T, ∑ y ∈ T, A x y * b x * b y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Finset.card_filter]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y hy => ?_
          rw [hT10 x hx, hT10 y hy]
          simp only [hA]; split_ifs <;> ring
      _ ≤ ∑ x ∈ T, ∑ y, A x y * b x * b y :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun y _ _ => mul_nonneg (mul_nonneg (hAnn x y) (hbb x).1) (hbb y).1
      _ ≤ ∑ x, ∑ y, A x y * b x * b y :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ =>
            Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (hAnn x y) (hbb x).1) (hbb y).1
  have hDT : 25 * ∑ u ∈ T, (T.filter (G.Adj u)).card ≤ n ^ 2 := by
    have : (100 * ∑ u ∈ T, (T.filter (G.Adj u)).card : ℤ) ≤ 4 * (n : ℤ) ^ 2 := by
      push_cast at hFb ⊢; linarith
    have h' : 100 * ∑ u ∈ T, (T.filter (G.Adj u)).card ≤ 4 * n ^ 2 := by exact_mod_cast this
    omega
  refine ⟨(T : Set V), by rw [Set.ncard_coe_finset]; exact hTcard, ?_⟩
  have := two_mul_induce G T
  omega

end OMA.R_Erdos128_erdos_128_R1_H1_R1
