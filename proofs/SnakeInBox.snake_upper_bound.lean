/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot
-/
import FormalConjectures.Wikipedia.SnakeInTheBox
import Mathlib

/-!
# The snake-in-the-box upper bound

In dimensions at least five, Huang's degree theorem forces a vertex of degree
at least three in any induced subgraph containing more than half the cube.
The low-dimensional cases use a kernel-checked search over induced paths.

The degree theorem and its supporting linear algebra are adapted from Mathlib's
`Archive/Sensitivity.lean`. See Huang, https://arxiv.org/abs/1907.00847.
-/
namespace OMA.SnakeSensitivity

noncomputable section

open Bool Finset Fintype Function LinearMap Module Module.DualBases

/-
### The hypercube

Notations:
- `ℕ` denotes natural numbers (including zero).
- `Fin n` = {0, ⋯ , n - 1}.
- `Bool` = {`true`, `false`}.
-/


/-- The hypercube in dimension `n`. -/
abbrev Q (n : ℕ) :=
  Fin n → Bool

/-- The projection from `Q n.succ` to `Q n` forgetting the first value
(i.e. the image of zero). -/
def π {n : ℕ} : Q n.succ → Q n := fun p => p ∘ Fin.succ

namespace Q

theorem ext {n} {f g : Q n} (h : ∀ x, f x = g x) : f = g := funext h

/- `n` will always denote a natural number. -/

variable (n : ℕ)

/-- `Q 0` has a unique element. -/
instance : Unique (Q 0) :=
  ⟨⟨fun _ => true⟩, by intro; apply Q.ext; intro x; fin_cases x⟩

/-- `Q n` has 2^n elements. -/
theorem card : card (Q n) = 2 ^ n := by simp

/- Until the end of this namespace, `n` will be an implicit argument (still
a natural number). -/

variable {n}

theorem succ_n_eq (p q : Q n.succ) : p = q ↔ p 0 = q 0 ∧ π p = π q := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h₀, h⟩
    apply Q.ext
    intro x
    by_cases hx : x = 0
    · rwa [hx]
    · rw [← Fin.succ_pred x hx]
      convert! congr_fun h (Fin.pred x hx)

/-- The adjacency relation defining the graph structure on `Q n`:
`p.adjacent q` if there is an edge from `p` to `q` in `Q n`. -/
def adjacent {n : ℕ} (p : Q n) : Set (Q n) := { q | ∃! i, p i ≠ q i }

/-- In `Q 0`, no two vertices are adjacent. -/
theorem not_adjacent_zero (p q : Q 0) : q ∉ p.adjacent := by rintro ⟨v, _⟩; apply finZeroElim v

/-- If `p` and `q` in `Q n.succ` have different values at zero then they are adjacent
iff their projections to `Q n` are equal. -/
theorem adj_iff_proj_eq {p q : Q n.succ} (h₀ : p 0 ≠ q 0) : q ∈ p.adjacent ↔ π p = π q := by
  constructor
  · rintro ⟨i, _, h_uni⟩
    apply Q.ext
    intro x
    by_contra hx
    apply Fin.succ_ne_zero x
    rw [h_uni _ hx, h_uni _ h₀]
  · intro heq
    use 0, h₀
    intro y hy
    contrapose! hy
    rw [← Fin.succ_pred _ hy]
    apply congr_fun heq

/-- If `p` and `q` in `Q n.succ` have the same value at zero then they are adjacent
iff their projections to `Q n` are adjacent. -/
theorem adj_iff_proj_adj {p q : Q n.succ} (h₀ : p 0 = q 0) :
    q ∈ p.adjacent ↔ π q ∈ (π p).adjacent := by
  constructor
  · rintro ⟨i, h_eq, h_uni⟩
    have h_i : i ≠ 0 := fun h_i => absurd h₀ (by rwa [h_i] at h_eq)
    use i.pred h_i,
      show p (Fin.succ (Fin.pred i _)) ≠ q (Fin.succ (Fin.pred i _)) by rwa [Fin.succ_pred]
    intro y hy
    simp [Eq.symm (h_uni _ hy)]
  · rintro ⟨i, h_eq, h_uni⟩
    use i.succ, h_eq
    intro y hy
    rw [← Fin.pred_inj (ha := (?ha : y ≠ 0)) (hb := (?hb : i.succ ≠ 0)),
      Fin.pred_succ]
    case ha =>
      contrapose hy
      rw [hy, h₀]
    case hb =>
      apply Fin.succ_ne_zero
    apply h_uni
    simp [π, hy]

end Q

/- ### The vector space -/


/-- The free vector space on vertices of a hypercube, defined inductively. -/
abbrev V : ℕ → Type
  | 0 => ℝ
  | n + 1 => V n × V n

@[simp]
theorem V_zero : V 0 = ℝ := rfl

@[simp]
theorem V_succ {n : ℕ} : V (n + 1) = (V n × V n) := rfl

namespace V

theorem ext {n : ℕ} {p q : V n.succ} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q := Prod.ext h₁ h₂

variable (n : ℕ)

instance : DecidableEq (V n) := by induction n <;> · dsimp only [V]; infer_instance

instance : AddCommGroup (V n) := by induction n <;> · dsimp only [V]; infer_instance

instance : Module ℝ (V n) := by
  induction n with
  | zero => exact inferInstanceAs (Module ℝ ℝ)
  | succ n ih => exact inferInstanceAs (Module ℝ (V n × V n))

end V

/-- The basis of `V` indexed by the hypercube, defined inductively. -/
noncomputable def e : ∀ {n}, Q n → V n
  | 0 => fun _ => (1 : ℝ)
  | Nat.succ _ => fun x => cond (x 0) (e (π x), 0) (0, e (π x))

@[simp]
theorem e_zero_apply (x : Q 0) : e x = (1 : ℝ) :=
  rfl

/-- The dual basis to `e`, defined inductively. -/
noncomputable def ε : ∀ {n : ℕ}, Q n → V n →ₗ[ℝ] ℝ
  | 0, _ => LinearMap.id
  | Nat.succ _, p =>
    cond (p 0) ((ε <| π p).comp <| LinearMap.fst _ _ _) ((ε <| π p).comp <| LinearMap.snd _ _ _)

variable {n : ℕ}

theorem duality (p q : Q n) : ε p (e q) = if p = q then 1 else 0 := by
  induction n with
  | zero => simp [Subsingleton.elim (α := Q 0) p q, ε, e]
  | succ n IH =>
    dsimp [ε, e]
    cases hp : p 0 <;> cases hq : q 0
    all_goals
      simp only [Bool.cond_true, Bool.cond_false, LinearMap.fst_apply, LinearMap.snd_apply,
        LinearMap.comp_apply, IH]
      congr 1; simp [Q.succ_n_eq, hp, hq]

/-- Any vector in `V n` annihilated by all `ε p`'s is zero. -/
theorem epsilon_total {v : V n} (h : ∀ p : Q n, (ε p) v = 0) : v = 0 := by
  induction n with
  | zero => dsimp [ε] at h; exact h fun _ => true
  | succ n ih =>
    obtain ⟨v₁, v₂⟩ := v
    apply V.ext <;> change _ = (0 : V n) <;> simp only <;> apply ih <;> intro p <;>
      [let q : Q n.succ := fun i => if h : i = 0 then true else p (i.pred h);
      let q : Q n.succ := fun i => if h : i = 0 then false else p (i.pred h)]
    all_goals
      specialize h q
      first
      | rw [ε, show q 0 = true from rfl, Bool.cond_true] at h
      | rw [ε, show q 0 = false from rfl, Bool.cond_false] at h
      rwa [show p = π q by apply Q.ext; intro x; simp [q, Fin.succ_ne_zero, π]]

open Module

/-- `e` and `ε` are dual families of vectors. It implies that `e` is indeed a basis
and `ε` computes coefficients of decompositions of vectors on that basis. -/
theorem dualBases_e_ε (n : ℕ) : DualBases (@e n) (@ε n) where
  eval_same := by simp [duality]
  eval_of_ne _ _ h := by simp [duality, h]
  total h := sub_eq_zero.mp <| epsilon_total fun i ↦ by
    simpa only [map_sub, sub_eq_zero] using h i

/- We will now derive the dimension of `V`, first as a cardinal in `dim_V` and,
since this cardinal is finite, as a natural number in `finrank_V` -/


theorem dim_V : Module.rank ℝ (V n) = 2 ^ n := by
  have : Module.rank ℝ (V n) = (2 ^ n : ℕ) := by
    rw [rank_eq_card_basis (dualBases_e_ε _).basis, Q.card]
  assumption_mod_cast

instance : FiniteDimensional ℝ (V n) :=
  (dualBases_e_ε _).basis.finiteDimensional_of_finite

theorem finrank_V : finrank ℝ (V n) = 2 ^ n := by
  have := @dim_V n
  rw [← finrank_eq_rank] at this; assumption_mod_cast

/- ### The linear map -/


/-- The linear operator $f_n$ corresponding to Huang's matrix $A_n$,
defined inductively as a ℝ-linear map from `V n` to `V n`. -/
noncomputable def f : ∀ n, V n →ₗ[ℝ] V n
  | 0 => 0
  | n + 1 =>
    LinearMap.prod (LinearMap.coprod (f n) LinearMap.id) (LinearMap.coprod LinearMap.id (-f n))

/- The preceding definition uses linear map constructions to automatically
get that `f` is linear, but its values are somewhat buried as a side-effect.
The next two lemmas unbury them. -/


@[simp]
theorem f_zero : f 0 = 0 :=
  rfl

theorem f_succ_apply (v : V n.succ) : f n.succ v = (f n v.1 + v.2, v.1 - f n v.2) := by
  cases v
  rw [f]
  simp only [sub_eq_add_neg]
  exact rfl

/- In the next statement, the explicit conversion `(n : ℝ)` of `n` to a real number
is necessary since otherwise `n • v` refers to the multiplication defined
using only the addition of `V`. -/


theorem f_squared (v : V n) : (f n) (f n v) = (n : ℝ) • v := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_smul, f_zero, LinearMap.zero_apply]
  | succ n IH =>
    cases v; rw [f_succ_apply, f_succ_apply]; simp [IH, add_smul (n : ℝ) 1, add_assoc]; abel

/- We now compute the matrix of `f` in the `e` basis (`p` is the line index,
`q` the column index). -/

open scoped Classical in
theorem f_matrix (p q : Q n) : |ε q (f n (e p))| = if p ∈ q.adjacent then 1 else 0 := by
  induction n with
  | zero =>
    dsimp [f]
    simp [Q.not_adjacent_zero]
  | succ n IH =>
    have ite_nonneg : ite (π q = π p) (1 : ℝ) 0 ≥ 0 := by split_ifs <;> norm_num
    dsimp only [e, ε, f, V]; rw [LinearMap.prod_apply]; dsimp; cases hp : p 0 <;> cases hq : q 0
    all_goals
      repeat rw [Bool.cond_true]
      repeat rw [Bool.cond_false]
      simp [hp, hq, IH, duality, abs_of_nonneg ite_nonneg, Q.adj_iff_proj_eq,
        Q.adj_iff_proj_adj]

/-- The linear operator $g_m$ corresponding to Knuth's matrix $B_m$. -/
noncomputable def g (m : ℕ) : V m →ₗ[ℝ] V m.succ :=
  LinearMap.prod (f m + √(m + 1) • LinearMap.id) LinearMap.id

/- In the following lemmas, `m` will denote a natural number. -/


variable {m : ℕ}

/- Again we unpack what are the values of `g`. -/


theorem g_apply : ∀ v, g m v = (f m v + √(m + 1) • v, v) := by
  delta g; intro v; simp

theorem g_injective : Injective (g m) := by
  rw [g]
  intro x₁ x₂ h
  simp only [V, LinearMap.prod_apply, LinearMap.id_apply, Prod.mk_inj, Function.prod_apply] at h
  exact h.right

theorem f_image_g (w : V m.succ) (hv : ∃ v, g m v = w) : f m.succ w = √(m + 1) • w := by
  rcases hv with ⟨v, rfl⟩
  have : √(m + 1) * √(m + 1) = m + 1 := Real.mul_self_sqrt (mod_cast zero_le)
  rw [f_succ_apply, g_apply]
  simp [this, f_squared, smul_add, add_smul, smul_smul]
  abel

/-
### The main proof

In this section, in order to enforce that `n` is positive, we write it as
`m + 1` for some natural number `m`. -/


open scoped Classical in
/-- If a subset `H` of `Q (m+1)` has cardinal at least `2^m + 1` then the
subspace of `V (m+1)` spanned by the corresponding basis vectors non-trivially
intersects the range of `g m`. -/
theorem exists_eigenvalue (H : Set (Q m.succ)) (hH : H.toFinset.card ≥ 2 ^ m + 1) :
    ∃ y ∈ Submodule.span ℝ (e '' H) ⊓ range (g m), y ≠ 0 := by
  let W := Submodule.span ℝ (e '' H)
  let img := range (g m)
  suffices 0 < Module.rank ℝ ↥(W ⊓ img) by
    exact mod_cast exists_mem_ne_zero_of_rank_pos this
  have dim_le : Module.rank ℝ ↥(W ⊔ img) ≤ (2 : Cardinal) ^ (m + 1 : Cardinal) := by
    convert! ← Submodule.rank_le (W ⊔ img)
    rw [← Nat.cast_succ]
    apply dim_V
  have dim_add : Module.rank ℝ ↥(W ⊔ img) + Module.rank ℝ ↥(W ⊓ img) = Module.rank ℝ ↥W + (2 : Cardinal) ^ m := by
    convert! ← Submodule.rank_sup_add_rank_inf_eq W img
    rw [rank_range_of_injective (g m) g_injective]
    apply dim_V
  have dimW : Module.rank ℝ ↥W = card H := by
    have li : LinearIndependent ℝ (H.domRestrict e) := by
      convert! (dualBases_e_ε m.succ).basis.linearIndependent.comp _ Subtype.val_injective
      rw [(dualBases_e_ε _).coe_basis]
      rfl
    have hdW := rank_span li
    rw [Set.range_domRestrict] at hdW
    convert! hdW
    rw [← (dualBases_e_ε _).coe_basis, Cardinal.mk_image_eq (dualBases_e_ε _).basis.injective,
      Cardinal.mk_fintype]
  rw [← finrank_eq_rank ℝ] at dim_le dim_add dimW ⊢
  rw [← finrank_eq_rank ℝ, ← finrank_eq_rank ℝ] at dim_add
  norm_cast at dim_le dim_add dimW ⊢
  rw [pow_succ'] at dim_le
  rw [Set.toFinset_card] at hH
  linarith

open scoped Classical in
/-- **Huang sensitivity theorem** also known as the **Huang degree theorem** -/
theorem huang_degree_theorem (H : Set (Q m.succ)) (hH : H.ncard ≥ 2 ^ m + 1) :
    ∃ q, q ∈ H ∧ √(m + 1) ≤ (H ∩ q.adjacent).ncard := by
  rw [Set.ncard_eq_toFinset_card'] at hH
  rcases exists_eigenvalue H hH with ⟨y, ⟨⟨y_mem_H, y_mem_g⟩, y_ne⟩⟩
  have coeffs_support : ((dualBases_e_ε m.succ).coeffs y).support ⊆ H.toFinset := by
    intro p p_in
    rw [Finsupp.mem_support_iff] at p_in
    rw [Set.mem_toFinset]
    exact (dualBases_e_ε _).mem_of_mem_span y_mem_H p p_in
  obtain ⟨q, H_max⟩ : ∃ q : Q m.succ, ∀ q' : Q m.succ, |(ε q' :) y| ≤ |ε q y| :=
    Finite.exists_max _
  have H_q_pos : 0 < |ε q y| := by
    contrapose! y_ne
    exact epsilon_total fun p => abs_nonpos_iff.mp (le_trans (H_max p) y_ne)
  refine ⟨q, (dualBases_e_ε _).mem_of_mem_span y_mem_H q (abs_pos.mp H_q_pos), ?_⟩
  rw [Set.ncard_eq_toFinset_card']
  let s := √(m + 1)
  suffices s * |ε q y| ≤ _ * |ε q y| from (mul_le_mul_iff_left₀ H_q_pos).mp ‹_›
  let coeffs := (dualBases_e_ε m.succ).coeffs
  calc
    s * |ε q y| = |ε q (s • y)| := by
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ = |ε q (f m.succ y)| := by rw [← f_image_g y (by simpa using! y_mem_g)]
    _ = |ε q (f m.succ (lc _ (coeffs y)))| := by rw [(dualBases_e_ε _).lc_coeffs y]
    _ =
        |(coeffs y).sum fun (i : Q m.succ) (a : ℝ) =>
            a • (ε q ∘ f m.succ ∘ fun i : Q m.succ => e i) i| := by
      rw [lc_def, (f m.succ).map_finsupp_linearCombination, (ε q).map_finsupp_linearCombination,
           Finsupp.linearCombination_apply]
    _ ≤ ∑ p ∈ (coeffs y).support, |coeffs y p * (ε q <| f m.succ <| e p)| :=
      (norm_sum_le _ fun p => coeffs y p * _)
    _ = ∑ p ∈ (coeffs y).support, |coeffs y p| * ite (p ∈ q.adjacent) 1 0 := by
      simp only [abs_mul]
      apply Finset.sum_congr rfl
      intro p _
      exact congrArg (fun x => |coeffs y p| * x) (f_matrix p q)
    _ = ∑ p ∈ (coeffs y).support with p ∈ q.adjacent, |coeffs y p| := by
      simp [sum_filter]
    _ ≤ ∑ p ∈ (coeffs y).support with p ∈ q.adjacent, |coeffs y q| := sum_le_sum fun p _ ↦ H_max p
    _ = #{p ∈ (coeffs y).support | p ∈ q.adjacent} * |coeffs y q| := by
      rw [sum_const, nsmul_eq_mul]
    _ = #((coeffs y).support ∩ q.adjacent.toFinset) * |coeffs y q| := by
      congr with x; simp
    _ ≤ #(H ∩ q.adjacent).toFinset * |ε q y| := by
      refine (mul_le_mul_iff_left₀ H_q_pos).2 ?_
      norm_cast
      apply card_le_card
      rw [Set.toFinset_inter]
      convert! inter_subset_inter_right coeffs_support

end

end OMA.SnakeSensitivity

namespace OMA.SnakeWalk

open SimpleGraph Finset symmDiff

variable {V : Type} {G : SimpleGraph V}

private theorem no_neighbors_of_not_mem {a b x : V} (p : G.Walk a b)
    (hx : x ∉ p.support) : p.toSubgraph.neighborSet x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hx (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hy))

private theorem start_neighbors {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.toSubgraph.neighborSet a = if p.Nil then ∅ else {p.snd} := by
  cases p with
  | nil => simp [neighborSet_singletonSubgraph]
  | cons h p =>
    rw [Walk.cons_isPath_iff] at hp
    simp [Subgraph.neighborSet_sup, no_neighbors_of_not_mem p hp.2]

private theorem card_neighbors [Fintype V] {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (x : V) : (p.toSubgraph.neighborSet x).ncard ≤ 2 := by
  classical
  induction p with
  | nil => simp [neighborSet_singletonSubgraph]
  | @cons a b c h p ih =>
    rcases (Walk.cons_isPath_iff h p).mp hp with ⟨hp, ha⟩
    rw [Walk.toSubgraph, Subgraph.neighborSet_sup]
    by_cases hxa : x = a
    · subst x
      simp [no_neighbors_of_not_mem p ha]
    by_cases hxb : x = b
    · subst x
      rw [neighborSet_snd_subgraphOfAdj, start_neighbors p hp]
      split_ifs
      · simp
      · exact (Set.ncard_union_le _ _).trans (by simp)
    simpa [neighborSet_subgraphOfAdj_of_ne_of_ne h hxa hxb] using ih hp

private theorem tail_induced {a b c : V} (h : G.Adj a b) (p : G.Walk b c)
    (hp : (Walk.cons h p).IsPath) (hi : (Walk.cons h p).toSubgraph.IsInduced) :
    p.toSubgraph.IsInduced := by
  have ha := ((Walk.cons_isPath_iff h p).mp hp).2
  intro x hx y hy hxy
  have hfull : (Walk.cons h p).toSubgraph.Adj x y :=
    hi ((Walk.cons h p).mem_verts_toSubgraph.mpr (by simp [p.mem_verts_toSubgraph.mp hx]))
      ((Walk.cons h p).mem_verts_toSubgraph.mpr (by simp [p.mem_verts_toSubgraph.mp hy])) hxy
  rw [Walk.toSubgraph, Subgraph.sup_adj] at hfull
  refine hfull.resolve_left ?_
  have hxa : x ≠ a := fun e => ha (e ▸ p.mem_verts_toSubgraph.mp hx)
  have hya : y ≠ a := fun e => ha (e ▸ p.mem_verts_toSubgraph.mp hy)
  simp [subgraphOfAdj_adj, Sym2.eq, hxa.symm, hya.symm]

/-- Search for a path prefix of the requested length, excluding previously
visited vertices and chords to earlier vertices. -/
private def search [Fintype V] [DecidableEq V] (adj : V → V → Bool) :
    ℕ → V → List V → Bool
  | 0, _, _ => true
  | k + 1, v, excluded =>
    decide (∃ w : V, adj v w = true ∧
      (excluded.any fun z => decide (z = w) || adj z w) = false ∧
      search adj k w (v :: excluded) = true)

private theorem search_complete [Fintype V] [DecidableEq V]
    (adj : V → V → Bool) (hadj : ∀ a b, adj a b = true ↔ G.Adj a b)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hi : p.toSubgraph.IsInduced)
    {k : ℕ} (hk : k ≤ p.length) (excluded : List V)
    (he : ∀ z ∈ excluded, ∀ x ∈ p.support, x ≠ a → z ≠ x ∧ ¬G.Adj z x) :
    search adj k a excluded = true := by
  induction k generalizing a b excluded with
  | zero => rfl
  | succ k ih =>
    cases p with
    | nil => simp at hk
    | @cons a b c h p =>
      simp only [search, decide_eq_true_eq]
      have hpath := (Walk.cons_isPath_iff h p).mp hp
      refine ⟨b, (hadj _ _).mpr h, ?_, ih p hpath.1 (tail_induced h p hp hi)
        (by simpa using hk) (a :: excluded) ?_⟩
      · apply List.any_eq_false.mpr
        intro z hz
        have hzb := he z hz b (by simp) h.ne.symm
        have hfalse : adj z b = false := Bool.eq_false_iff.mpr (hzb.2 ∘ (hadj _ _).mp)
        simp [hzb.1, hfalse]
      · intro z hz x hx hxb
        rcases List.mem_cons.mp hz with hz | hz
        · subst z
          have hxa : x ≠ a := fun e => hpath.2 (e ▸ hx)
          refine ⟨hxa.symm, ?_⟩
          intro hax
          have hfull := hi (Walk.start_mem_verts_toSubgraph (Walk.cons h p))
            ((Walk.cons h p).mem_verts_toSubgraph.mpr (by simp [hx])) hax
          change x ∈ (Walk.cons h p).toSubgraph.neighborSet a at hfull
          rw [start_neighbors _ hp] at hfull
          exact hxb (by simpa using hfull)
        · exact he z hz x (by simp [hx]) (fun e => hpath.2 (e ▸ hx))


private theorem cube_adj {n : ℕ} (a b : Finset (Fin n)) :
    (SnakeInBox.Hypercube n).Adj a b ↔ (a ∆ b).card = 1 := by
  rw [SnakeInBox.Hypercube, SimpleGraph.fromRel_adj, symmDiff_comm b a, or_self]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rintro rfl
  simp at h

private def cube_adj_bool {n : ℕ} (a b : Finset (Fin n)) : Bool :=
  decide ((a ∆ b).card = 1)

private theorem cube_adj_bool_iff {n : ℕ} (a b : Finset (Fin n)) :
    cube_adj_bool a b = true ↔ (SnakeInBox.Hypercube n).Adj a b := by
  simp only [cube_adj_bool, decide_eq_true_eq, cube_adj]

private theorem check_one : ∀ a : Finset (Fin 1), search cube_adj_bool 2 a [] = false := by
  decide

private theorem check_two : ∀ a : Finset (Fin 2), search cube_adj_bool 3 a [] = false := by
  decide

private theorem check_three : ∀ a : Finset (Fin 3), search cube_adj_bool 5 a [] = false := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem check_four : ∀ a : Finset (Fin 4), search cube_adj_bool 9 a [] = false := by
  decide

private theorem small {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 4)
    {a b : Finset (Fin n)} (p : (SnakeInBox.Hypercube n).Walk a b)
    (hp : p.IsPath) (hi : p.toSubgraph.IsInduced) : p.length ≤ 2 ^ (n - 1) := by
  by_contra! h
  have hsearch := search_complete cube_adj_bool cube_adj_bool_iff p hp hi (Nat.succ_le_of_lt h) []
    (by simp)
  interval_cases n
  · simp [check_one a] at hsearch
  · simp [check_two a] at hsearch
  · simp [check_three a] at hsearch
  · simp [check_four a] at hsearch

end OMA.SnakeWalk

namespace OMA.SnakeWalk

open SimpleGraph Finset symmDiff OMA.SnakeSensitivity

private def coordinates {n : ℕ} (a : Finset (Fin n)) : Q n :=
  fun i => decide (i ∈ a)

private theorem coordinates_injective {n : ℕ} : Function.Injective (@coordinates n) := by
  intro a b hab
  ext i
  have hi := congrFun hab i
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all [coordinates]

private theorem coordinates_adj {n : ℕ} (a b : Finset (Fin n)) :
    coordinates b ∈ (coordinates a).adjacent ↔ (SnakeInBox.Hypercube n).Adj a b := by
  rw [cube_adj, Finset.card_eq_one_iff_existsUnique]
  unfold Q.adjacent
  change (∃! i, coordinates a i ≠ coordinates b i) ↔ ∃! i, i ∈ a ∆ b
  refine existsUnique_congr (fun i => ?_)
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp [coordinates, Finset.mem_symmDiff, ha, hb]

private theorem large {m : ℕ} (hm : 5 ≤ m + 1)
    {a b : Finset (Fin (m + 1))} (p : (SnakeInBox.Hypercube (m + 1)).Walk a b)
    (hp : p.IsPath) (hi : p.toSubgraph.IsInduced) : p.length ≤ 2 ^ m := by
  classical
  let H : Set (Q (m + 1)) := coordinates '' p.toSubgraph.verts
  have hsize : H.ncard = p.length + 1 := by
    change (coordinates '' p.toSubgraph.verts).ncard = _
    rw [Set.ncard_image_of_injective _ coordinates_injective]
    rw [show p.toSubgraph.verts = (p.support.toFinset : Set _) by ext x; simp]
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
  by_contra! h
  have hH : H.ncard ≥ 2 ^ m + 1 := by omega
  obtain ⟨q, ⟨x, hx, rfl⟩, hq⟩ := huang_degree_theorem H hH
  have hneighbors : H ∩ (coordinates x).adjacent = coordinates '' p.toSubgraph.neighborSet x := by
    ext r
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hr⟩
      exact ⟨z, hi hx hz ((coordinates_adj x z).mp hr), rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, p.toSubgraph.neighborSet_subset_verts x hz, rfl⟩,
        (coordinates_adj x z).mpr (p.toSubgraph.adj_sub hz)⟩
  have hdegree : (H ∩ (coordinates x).adjacent).ncard ≤ 2 := by
    rw [hneighbors, Set.ncard_image_of_injective _ coordinates_injective]
    exact card_neighbors p hp x
  have hmreal : (4 : ℝ) < (m : ℝ) + 1 := by exact_mod_cast (show 4 < m + 1 by omega)
  have hsqrt : (2 : ℝ) < Real.sqrt ((m : ℝ) + 1) :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num; linarith)
  have hdegreereal : ((H ∩ (coordinates x).adjacent).ncard : ℝ) ≤ 2 := by
    exact_mod_cast hdegree
  exact hsqrt.not_ge (hq.trans hdegreereal)

end OMA.SnakeWalk

open SimpleGraph in
theorem OMA.solution : type_of% @SnakeInBox.snake_upper_bound := by
  intro n hn
  unfold SnakeInBox.LongestSnakeInTheBox SnakeInBox.LongestSnakeInGraph
  apply csSup_le
  · let p : (SnakeInBox.Hypercube n).Walk ∅ ∅ := .nil
    refine ⟨0, p.toSubgraph, ?_, ∅, ∅, p, by simp [p], rfl, rfl⟩
    intro a ha b hb hab
    have he : a = b := by simpa [p] using ha.trans hb.symm
    exact (hab.ne he).elim
  · rintro k ⟨S, hi, a, b, p, hp, rfl, rfl⟩
    by_cases hsmall : n ≤ 4
    · exact OMA.SnakeWalk.small hn hsmall p hp hi
    cases n with
    | zero => omega
    | succ m =>
      simpa using OMA.SnakeWalk.large (by omega : 5 ≤ m + 1) p hp hi
