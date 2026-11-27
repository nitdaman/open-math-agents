import OMAReductions.R_Arxiv_0805_3777_isGenericRank_cube_R1

/-! # The generic rank lower bound for cubic tensors

In each simple summand, scale the first two vectors to have first coordinate one.
This chart has `3 * n - 2` free coordinates per summand. A nonzero polynomial
annihilates the chart when the parameter count is smaller than the ambient dimension.
The resulting identity extends from nonzero factors to all factors. -/

open Set Filter
open scoped Topology

namespace TensorRankDimension

lemma interior_polynomial_zero_locus {J : Type} (P : MvPolynomial J ℂ) (hP : P ≠ 0) :
    interior {y : J → ℂ | MvPolynomial.eval y P = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hn := mem_interior_iff_mem_nhds.mp ha
  rw [nhds_pi, Filter.mem_pi] at hn
  obtain ⟨I, _, box, hin, hsub⟩ := hn
  apply hP
  apply MvPolynomial.funext_set box (fun j => infinite_of_mem_nhds (a j) (hin j))
  intro y hy
  have hyI : y ∈ I.pi box := fun j _ => hy j (Set.mem_univ _)
  have hzero : MvPolynomial.eval y P = 0 := hsub hyI
  simpa only [map_zero] using hzero

lemma eval_substitution {I J : Type} (F : J → MvPolynomial I ℂ) (x : I → ℂ)
    (P : MvPolynomial J ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval F P) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P := by
  have he : (MvPolynomial.aeval x).comp (MvPolynomial.aeval F) =
      MvPolynomial.aeval (fun j => MvPolynomial.eval x (F j)) := by
    ext j
    simp [MvPolynomial.aeval_eq_eval]
  exact DFunLike.congr_fun he P

lemma vanishing_on_polynomial_image {I J : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (F : J → MvPolynomial I ℂ) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : I → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P = 0 := by
  classical
  have hn : ¬ AlgebraicIndependent ℂ F := by
    intro h
    have hc := h.cardinalMk_le_trdeg
    rw [MvPolynomial.trdeg_of_isDomain] at hc
    have : Fintype.card J ≤ Fintype.card I := by simpa [Cardinal.mk_fintype] using hc
    omega
  rw [algebraicIndependent_iff] at hn
  push Not at hn
  obtain ⟨P, ha, hP⟩ := hn
  refine ⟨P, hP, ?_⟩
  intro x
  rw [← eval_substitution F x P, ha, map_zero]

/-- Agreement with a lower-dimensional chart on a product of infinite subsets
extends to a polynomial identity on the entire parameter space. -/
lemma generic_chart_relation {I J K : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (chart : J → MvPolynomial I ℂ)
    (full : J → MvPolynomial K ℂ)
    (hnormal : ∀ x : K → ℂ, (∀ i, x i ≠ 0) →
      ∃ y : I → ℂ, ∀ j, MvPolynomial.eval x (full j) = MvPolynomial.eval y (chart j)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : K → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (full j)) P = 0 := by
  classical
  obtain ⟨P, hP, hvanish⟩ := vanishing_on_polynomial_image hd chart
  have hpoly : MvPolynomial.aeval full P = 0 := by
    apply MvPolynomial.funext_set (fun _ : K => ({0}ᶜ : Set ℂ))
      (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl)
    intro x hx
    have hx0 (i : K) : x i ≠ 0 := hx i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := hnormal x hx0
    rw [eval_substitution full x P, funext hy, map_zero]
    exact hvanish y
  refine ⟨P, hP, fun x => ?_⟩
  rw [← eval_substitution full x P, hpoly, map_zero]

def index_cons_equiv (n : ℕ) (ds : List ℕ) : HolorIndex (n :: ds) ≃ Fin n × HolorIndex ds where
  toFun
    | ⟨i :: is, h⟩ => (⟨i, (List.forall₂_cons.mp h).1⟩, ⟨is, (List.forall₂_cons.mp h).2⟩)
    | ⟨[], h⟩ => nomatch h
  invFun q := ⟨q.1.val :: q.2.val, List.Forall₂.cons q.1.isLt q.2.property⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => cases h
    | cons i is => rfl
  right_inv := by rintro ⟨⟨i, hi⟩, ⟨is, his⟩⟩; rfl

def index_nil_equiv : HolorIndex [] ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], .nil⟩
  left_inv := by rintro ⟨l, h⟩; cases h; rfl
  right_inv := by intro x; cases x; rfl

lemma finite_index (ds : List ℕ) : Finite (HolorIndex ds) := by
  induction ds with
  | nil => exact Finite.of_equiv Unit index_nil_equiv.symm
  | cons n ds ih =>
    let _ : Finite (HolorIndex ds) := ih
    exact Finite.of_equiv (Fin n × HolorIndex ds) (index_cons_equiv n ds).symm

lemma card_index (ds : List ℕ) : Nat.card (HolorIndex ds) = ds.prod := by
  induction ds with
  | nil => simpa using Nat.card_congr index_nil_equiv
  | cons n ds ih =>
    rw [Nat.card_congr (index_cons_equiv n ds), Nat.card_prod, Nat.card_fin, ih, List.prod_cons]

def vector_index_equiv (n : ℕ) : HolorIndex [n] ≃ Fin n where
  toFun i := ((index_cons_equiv n []) i).1
  invFun i := ⟨[i.val], .cons i.isLt .nil⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases h with
    | cons _ h => cases h; rfl
  right_inv := by intro i; rfl

def cube_index_equiv (n : ℕ) : HolorIndex [n, n, n] ≃ Fin n × Fin n × Fin n :=
  (index_cons_equiv n [n, n]).trans (Equiv.prodCongr (Equiv.refl _)
    ((index_cons_equiv n [n]).trans (Equiv.prodCongr (Equiv.refl _) (vector_index_equiv n))))

lemma zero_is_simple (ds : List ℕ) : Holor.CPRankMax1 (0 : Holor ℂ ds) := by
  induction ds with
  | nil => exact .nil _
  | cons n ds ih =>
    have h := Holor.CPRankMax1.cons (0 : Holor ℂ [n]) (0 : Holor ℂ ds) ih
    have he : Holor.mul (0 : Holor ℂ [n]) (0 : Holor ℂ ds) = (0 : Holor ℂ (n :: ds)) := by
      funext i
      change (0 : ℂ) * 0 = 0
      simp
    rwa [he] at h

lemma decomposition_of_rank_bound {ds : List ℕ} (T : Holor ℂ ds) (r : ℕ) (hr : T.cprank ≤ r) :
    Holor.CPRankMax r T := by
  classical
  have hmin : Holor.CPRankMax T.cprank T :=
    Nat.find_spec (p := fun k => Holor.CPRankMax k T) ⟨ds.prod, Holor.cprankMax_upper_bound T⟩
  induction r, hr using Nat.le_induction with
  | base => exact hmin
  | succ k _ ih => simpa using Holor.CPRankMax.succ k 0 T (zero_is_simple ds) ih

lemma finite_sum_of_simple {ds : List ℕ} {r : ℕ} {T : Holor ℂ ds} (h : Holor.CPRankMax r T) :
    ∃ u : Fin r → Holor ℂ ds, (∀ i, Holor.CPRankMax1 (u i)) ∧ ∑ i, u i = T := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ k x y hx hy ih =>
    obtain ⟨u, hu, hs⟩ := ih
    refine ⟨Fin.cons x u, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using hu j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hs]

/-- Absorb the scalar at the end of a simple holor into its last vector. -/
lemma simple_cube_coordinates {n : ℕ} {T : Holor ℂ [n, n, n]} (h : Holor.CPRankMax1 T) :
    ∃ a b c : Fin n → ℂ, ∀ i j l, T ((cube_index_equiv n).symm (i, j, l)) = a i * b j * c l := by
  cases h with
  | cons a yz hyz =>
    cases hyz with
    | cons b zs hzs =>
      cases hzs with
      | cons c z hz =>
        refine ⟨fun i => a ((vector_index_equiv n).symm i),
          fun j => b ((vector_index_equiv n).symm j),
          fun l => c ((vector_index_equiv n).symm l) * z ⟨[], .nil⟩, ?_⟩
        intro i j l
        change a _ * (b _ * (c _ * z _)) = a _ * b _ * (c _ * z _)
        rw [mul_assoc]
        rfl


abbrev RawIndex (m r : ℕ) := Fin r × Fin 3 × Fin (m + 1)
abbrev ChartIndex (m r : ℕ) := Fin r × (Fin m ⊕ (Fin m ⊕ Fin (m + 1)))

noncomputable def raw_coordinate (m r : ℕ) (q : HolorIndex [m + 1, m + 1, m + 1]) :
    MvPolynomial (RawIndex m r) ℂ :=
  let v := cube_index_equiv (m + 1) q
  ∑ t : Fin r, MvPolynomial.X (t, 0, v.1) * MvPolynomial.X (t, 1, v.2.1) *
    MvPolynomial.X (t, 2, v.2.2)

noncomputable def chart_coordinate (m r : ℕ) (q : HolorIndex [m + 1, m + 1, m + 1]) :
    MvPolynomial (ChartIndex m r) ℂ :=
  let v := cube_index_equiv (m + 1) q
  ∑ t : Fin r, Fin.cases 1 (fun i => MvPolynomial.X (t, Sum.inl i)) v.1 *
    Fin.cases 1 (fun j => MvPolynomial.X (t, Sum.inr (Sum.inl j))) v.2.1 *
    MvPolynomial.X (t, Sum.inr (Sum.inr v.2.2))

/-- The two scaling constants are absorbed in the third vector. -/
lemma normalize_coordinates (m r : ℕ) (x : RawIndex m r → ℂ) (hx : ∀ i, x i ≠ 0) :
    ∃ y : ChartIndex m r → ℂ, ∀ q,
      MvPolynomial.eval x (raw_coordinate m r q) = MvPolynomial.eval y (chart_coordinate m r q) := by
  classical
  let y : ChartIndex m r → ℂ := fun (t, s) => match s with
    | .inl i => x (t, 0, i.succ) / x (t, 0, 0)
    | .inr (.inl j) => x (t, 1, j.succ) / x (t, 1, 0)
    | .inr (.inr l) => x (t, 2, l) * x (t, 0, 0) * x (t, 1, 0)
  refine ⟨y, ?_⟩
  intro q
  simp only [raw_coordinate, chart_coordinate, map_sum, map_mul, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro t _
  have ha (i : Fin (m + 1)) :
      MvPolynomial.eval y (Fin.cases 1 (fun i : Fin m => MvPolynomial.X (t, Sum.inl i)) i) =
        x (t, 0, i) / x (t, 0, 0) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hx]
    · simp [y]
  have hb (i : Fin (m + 1)) :
      MvPolynomial.eval y (Fin.cases 1 (fun j : Fin m => MvPolynomial.X (t, Sum.inr (Sum.inl j))) i) =
        x (t, 1, i) / x (t, 1, 0) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hx]
    · simp [y]
  rw [ha, hb]
  dsimp only [y]
  field_simp [hx]


lemma raw_representation (m r : ℕ) (T : Holor ℂ [m+1, m+1, m+1]) (hr : T.cprank ≤ r) :
    ∃ x : RawIndex m r → ℂ, ∀ q, MvPolynomial.eval x (raw_coordinate m r q) = T q := by
  classical
  obtain ⟨u, hu, hT⟩ := finite_sum_of_simple (decomposition_of_rank_bound T r hr)
  choose a b c habc using fun t => simple_cube_coordinates (hu t)
  let x : RawIndex m r → ℂ := fun (t, s, j) =>
    if s = 0 then a t j else if s = 1 then b t j else c t j
  refine ⟨x, ?_⟩
  intro q
  let v := cube_index_equiv (m + 1) q
  have term (t : Fin r) : u t q = a t v.1 * b t v.2.1 * c t v.2.2 := by
    have ht := habc t v.1 v.2.1 v.2.2
    change u t ((cube_index_equiv (m+1)).symm v) = _ at ht
    simpa only [v, Equiv.symm_apply_apply] using ht
  have hcoord : (∑ t : Fin r, u t q) = T q := by
    have at_q := Finset.sum_apply (M := fun _ : HolorIndex [m+1,m+1,m+1] => ℂ) q
      (Finset.univ : Finset (Fin r)) (fun t => fun v => u t v)
    exact at_q.symm.trans (congrFun hT q)
  calc
    _ = ∑ t : Fin r, a t v.1 * b t v.2.1 * c t v.2.2 := by simp [raw_coordinate, v, x]
    _ = ∑ t : Fin r, u t q := Finset.sum_congr rfl fun t _ => (term t).symm
    _ = T q := hcoord

end TensorRankDimension

open Arxiv.«0805.3777» TensorRankDimension in
theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1.H1 := by
  classical
  intro n r hn hdim
  cases n with
  | zero => omega
  | succ m =>
    let _ : Finite (HolorIndex [m+1,m+1,m+1]) := finite_index _
    let _ : Fintype (HolorIndex [m+1,m+1,m+1]) := Fintype.ofFinite _
    have hj : Fintype.card (HolorIndex [m+1,m+1,m+1]) = (m+1)^3 := by
      rw [← Nat.card_eq_fintype_card, card_index]
      simp [pow_succ, Nat.mul_assoc]
    have hi : Fintype.card (ChartIndex m r) = (3 * (m + 1) - 2) * r := by
      have hz : 3 * (m + 1) - 2 = m + (m + (m + 1)) := by omega
      rw [hz]
      simp only [ChartIndex, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
      exact Nat.mul_comm _ _
    have hsize : Fintype.card (ChartIndex m r) < Fintype.card (HolorIndex [m+1,m+1,m+1]) := by
      rwa [hi, hj]
    obtain ⟨P, hP, hzero⟩ := generic_chart_relation hsize (chart_coordinate m r)
      (raw_coordinate m r) (normalize_coordinates m r)
    let Z := {T : Holor ℂ [m+1,m+1,m+1] | MvPolynomial.eval T P = 0}
    have hclosed : IsClosed Z := isClosed_eq (MvPolynomial.continuous_eval P) continuous_const
    have hsub : {T : Holor ℂ [m+1,m+1,m+1] | T.cprank ≤ r} ⊆ Z := by
      intro T hT
      obtain ⟨x, hx⟩ := raw_representation m r T hT
      have he : (fun j => MvPolynomial.eval x (raw_coordinate m r j)) = T := funext hx
      change MvPolynomial.eval T P = 0
      simpa only [he] using hzero x
    have hempty : interior Z = ∅ := interior_polynomial_zero_locus P hP
    apply Set.subset_empty_iff.mp
    simpa only [hempty] using interior_mono (closure_minimal hsub hclosed)
