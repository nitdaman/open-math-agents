import FormalConjectures.ErdosProblems.«1033»

/-! The graph construction for the Erdős–Laskar upper bound. -/

open SimpleGraph Finset Filter
open scoped Classical

namespace Erdos1033Upper

private abbrev Vert (a m : ℕ) := Fin a ⊕ (Fin m ⊕ Fin m)

private def adjacency {a m : ℕ} (r : ℕ) : Vert a m → Vert a m → Prop
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr (.inl x), .inr (.inr y) => (y - x).val < r
  | .inr (.inr y), .inr (.inl x) => (y - x).val < r
  | _, _ => False

private def tripartite (a m r : ℕ) : SimpleGraph (Vert a m) where
  Adj := adjacency r
  symm := ⟨by
    intro u v huv
    rcases u with u | (u | u) <;> rcases v with v | (v | v) <;> exact huv⟩
  loopless := ⟨by
    rintro (u | (u | u)) h <;> exact h⟩

private lemma split_card {A B : Type*} [Fintype A] [Fintype B] (p : A ⊕ B → Prop) :
    Nat.card {v // p v} =
      Nat.card {v : A // p (.inl v)} + Nat.card {v : B // p (.inr v)} := by
  rw [Nat.card_congr (Equiv.subtypeSum (p := p)), Nat.card_sum]

private lemma card_initial {m r : ℕ} (hr : r ≤ m) :
    Nat.card {v : Fin m // v.val < r} = r := by
  let e : {v : Fin m // v.val < r} ≃ Fin r :=
    { toFun := fun v => ⟨v.val.val, v.property⟩
      invFun := fun v => ⟨Fin.castLE hr v, v.isLt⟩
      left_inv := fun v => by rfl
      right_inv := fun v => by rfl }
  rw [Nat.card_congr e, Nat.card_fin]

private lemma card_shift_right {m r : ℕ} [NeZero m] (hr : r ≤ m) (x : Fin m) :
    Nat.card {v : Fin m // (v - x).val < r} = r := by
  have e : {v : Fin m // (v - x).val < r} ≃ {v : Fin m // v.val < r} :=
    Equiv.subtypeEquiv (Equiv.subRight x) (fun _ => Iff.rfl)
  rw [Nat.card_congr e, card_initial hr]

private lemma card_shift_left {m r : ℕ} [NeZero m] (hr : r ≤ m) (y : Fin m) :
    Nat.card {v : Fin m // (y - v).val < r} = r := by
  have e : {v : Fin m // (y - v).val < r} ≃ {v : Fin m // v.val < r} :=
    Equiv.subtypeEquiv (Equiv.subLeft y) (fun _ => Iff.rfl)
  rw [Nat.card_congr e, card_initial hr]

private def prescribedDegree (a m r : ℕ) : Vert a m → ℕ
  | .inl _ => 2 * m
  | .inr _ => a + r

private lemma degree_eq_prescribed {a m r : ℕ} [NeZero m] (hr : r ≤ m) (u : Vert a m) :
    (tripartite a m r).degree u = prescribedDegree a m r u := by
  rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  change Nat.card {v // (tripartite a m r).Adj u v} = _
  rw [split_card, split_card]
  rcases u with u | (u | u)
  · change Nat.card {_v : Fin a // False} +
      (Nat.card {_v : Fin m // True} + Nat.card {_v : Fin m // True}) = 2 * m
    simp [two_mul]
  · change Nat.card {_v : Fin a // True} +
      (Nat.card {_v : Fin m // False} + Nat.card {v : Fin m // (v - u).val < r}) = a + r
    rw [card_shift_right hr]
    simp
  · change Nat.card {_v : Fin a // True} +
      (Nat.card {v : Fin m // (u - v).val < r} + Nat.card {_v : Fin m // False}) = a + r
    rw [card_shift_left hr]
    simp

private lemma triangle_degrees {a m r : ℕ} [NeZero m] (hr : r ≤ m)
    (t : Finset (Vert a m)) (ht : (tripartite a m r).IsNClique 3 t) :
    (∑ v ∈ t, (tripartite a m r).degree v) = 2 * m + 2 * (a + r) := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp ht
  rw [Finset.sum_insert (by simp [hxy.ne, hxz.ne]), Finset.sum_pair hyz.ne]
  simp only [degree_eq_prescribed hr]
  rcases x with x | (x | x) <;> rcases y with y | (y | y) <;> rcases z with z | (z | z) <;>
    simp_all [tripartite, adjacency, prescribedDegree] <;> omega

private lemma construct (n a m r : ℕ) (hm : 0 < m) (hr : r ≤ m) (hn : n = a + 2 * m) :
    ∃ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * m * a + m * r ∧
      ∀ t, G.IsNClique 3 t → (∑ v ∈ t, G.degree v) = 2 * m + 2 * (a + r) := by
  have _ : NeZero m := ⟨hm.ne'⟩
  let H := tripartite a m r
  have hcard : Fintype.card (Vert a m) = n := by simp [hn, two_mul]
  let e : Vert a m ≃ Fin n := (Fintype.equivFin _).trans (finCongr hcard)
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph (Fin n), H.comap e.symm = G := ⟨_, rfl⟩
  have iso : G ≃g H := hG ▸ Iso.comap e.symm H
  refine ⟨G, ?_, fun t ht => ?_⟩
  · have heq : G.edgeFinset.card = H.edgeFinset.card := iso.card_edgeFinset_eq
    refine heq.trans ?_
    have hsum := H.sum_degrees_eq_twice_card_edges
    change (∑ v, (tripartite a m r).degree v) = 2 * H.edgeFinset.card at hsum
    simp only [degree_eq_prescribed hr, Fintype.sum_sum_type, prescribedDegree,
      Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, smul_eq_mul] at hsum
    nlinarith
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp ht
    have hxy' := iso.map_adj_iff.mpr hxy
    have hxz' := iso.map_adj_iff.mpr hxz
    have hyz' := iso.map_adj_iff.mpr hyz
    have ht' : H.IsNClique 3 {iso x, iso y, iso z} :=
      is3Clique_triple_iff.mpr ⟨hxy', hxz', hyz'⟩
    have hsum := triangle_degrees hr _ ht'
    rw [Finset.sum_insert (by simp [hxy'.ne, hxz'.ne]), Finset.sum_pair hyz'.ne] at hsum
    rw [Finset.sum_insert (by simp [hxy.ne, hxz.ne]), Finset.sum_pair hyz.ne]
    have hd (v : Fin n) : (tripartite a m r).degree (iso v) = G.degree v := iso.degree_eq v
    simpa only [hd] using hsum

private theorem laskarParameters : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    ∃ a m r : ℕ, 0 < m ∧ r ≤ m ∧ n = a + 2 * m ∧
      n ^ 2 < 4 * (2 * m * a + m * r) ∧
      ((2 * m + 2 * (a + r) : ℕ) : ℝ) ≤ 2 * (Real.sqrt 3 - 1) * n + C := by
  refine ⟨6, eventually_atTop.mpr ⟨100, ?_⟩⟩
  intro n hn
  let s := Real.sqrt 3
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsL : 17 / 10 < s := by nlinarith
  have hsU : s < 7 / 4 := by nlinarith
  have hpos : 0 < 2 * s := by linarith
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  let m : ℕ := ⌊(n : ℝ) / (2 * s)⌋₊
  have hmlo : (m : ℝ) * (2 * s) ≤ n :=
    (le_div_iff₀ hpos).mp (Nat.floor_le (by positivity))
  have hmhi : (n : ℝ) < ((m : ℝ) + 1) * (2 * s) :=
    (div_lt_iff₀ hpos).mp (Nat.lt_floor_add_one _)
  have hm8 : 8 ≤ m := by
    apply Nat.le_floor
    apply (le_div_iff₀ hpos).mpr
    push_cast
    linarith
  have hm8' : (8 : ℝ) ≤ m := by exact_mod_cast hm8
  have h2m : 2 * m ≤ n := by
    have : (2 : ℝ) * m ≤ n := by
      nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) by positivity) (show 0 ≤ s - 1 by linarith)]
    exact_mod_cast this
  have h4m : (n : ℝ) ≤ 4 * m := by
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) + 1 by positivity) (show 0 ≤ 7 / 4 - s by linarith)]
  let a := n - 2 * m
  have ha : n = a + 2 * m := by dsimp [a]; omega
  have ha' : (n : ℝ) = a + 2 * m := by exact_mod_cast ha
  let r : ℕ := ⌊(7 - 4 * s) * (m : ℝ)⌋₊ + 1
  have hrpos : 0 ≤ (7 - 4 * s) * (m : ℝ) :=
    mul_nonneg (by linarith) (by positivity)
  have hrl : (7 - 4 * s) * (m : ℝ) < r := by
    simpa [r] using Nat.lt_floor_add_one ((7 - 4 * s) * (m : ℝ))
  have hru : (r : ℝ) ≤ (7 - 4 * s) * (m : ℝ) + 1 := by
    simpa [r] using add_le_add_right (Nat.floor_le hrpos) 1
  have hrm : r ≤ m := by
    have h : (r : ℝ) ≤ m := by
      nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) by positivity) (show 0 ≤ s - 17 / 10 by linarith)]
    exact_mod_cast h
  refine ⟨a, m, r, by omega, hrm, ha, ?_, ?_⟩
  · have hsq : (4 * (m : ℝ) - n) ^ 2 ≤ ((4 - 2 * s) * m) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith : 0 ≤ 4 * (m : ℝ) - n)
      linarith
    have hid : ((4 - 2 * s) * (m : ℝ)) ^ 2 = 4 * m * ((7 - 4 * s) * m) := by
      linear_combination 4 * (m : ℝ) ^ 2 * hs
    have hedge : (4 * (m : ℝ) - n)^2 < 4 * m * r :=
      (hsq.trans_eq hid).trans_lt (mul_lt_mul_of_pos_left hrl (by positivity))
    have : (n : ℝ) ^ 2 < 4 * (2 * m * a + m * r) := by
      rw [ha'] at hedge ⊢
      nlinarith
    exact_mod_cast this
  · push_cast
    change 2 * (m : ℝ) + 2 * (a + (r : ℝ)) ≤ 2 * (s - 1) * n + 6
    have hgap : (4 - 2 * s) * ((n : ℝ) - 2 * s * m) ≤ 4 := by
      have hn0 : 0 ≤ (n : ℝ) - 2 * s * m := by linarith
      have hδ : (n : ℝ) - 2 * s * m ≤ 4 := by linarith
      nlinarith [mul_nonneg hn0 (show 0 ≤ 2 * s - 3 by linarith)]
    nlinarith only [ha', hru, hgap, show s ^ 2 * (m : ℝ) = 3 * m from congrArg (fun x : ℝ => x * m) hs]

end Erdos1033Upper

open Erdos1033Upper

theorem OMA.solution : type_of% @Erdos1033.erdos_1033.variants.erdos_laskar := by
  obtain ⟨C, hparams⟩ := laskarParameters
  refine ⟨C, ?_⟩
  filter_upwards [hparams] with n hn
  obtain ⟨a, m, r, hm, hr, hsum, hlt, hle⟩ := hn
  obtain ⟨G, hedge, htriangle⟩ := construct n a m r hm hr hsum
  refine ⟨G, by rwa [hedge], fun t ht => ?_⟩
  rw [← Nat.cast_sum, htriangle t ht]
  exact hle