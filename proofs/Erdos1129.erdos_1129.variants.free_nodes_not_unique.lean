import FormalConjectures.ErdosProblems.«1129»

-- Problem: Erdős Problem 1129 — free nodes not unique
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1129.lean:198 (declaration Erdos1129.erdos_1129.variants.free_nodes_not_unique)
-- Credit: @koolkao (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea (Rack-Vajda 2015, Theorem 2.5): a minimiser exists, since close nodes force a large
-- Lebesgue constant and the constant is continuous on the compact set of node sets with gaps
-- at least delta. Rescaling it affinely gives a canonical minimiser x* (nodes -1 and 1). For n >= 3,
-- Lambda(x*) > 1 = L(+-1), so by continuity x*/tau is a minimiser for all tau in (1, 1 + eps).

namespace OMA.E1129F

open Erdos1129 Finset Polynomial

/-- The Lagrange basis function by its product formula. -/
noncomputable def lb {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : ℝ) : ℝ :=
  ∏ i ∈ univ.erase k, (t - x i) / (x k - x i)

lemma eval_basis_eq {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    (Lagrange.basis univ x k).eval t = lb x k t := by
  simp only [lb, Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [div_eq_inv_mul]

lemma sum_lb {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ) (hx : Function.Injective x) (t : ℝ) :
    ∑ k, lb x k t = 1 := by
  have h := congrArg (Polynomial.eval t)
    (Lagrange.sum_basis (s := (univ : Finset (Fin n))) hx.injOn ⟨⟨0, by omega⟩, mem_univ _⟩)
  rw [eval_finsetSum, eval_one] at h
  simpa only [eval_basis_eq] using h

lemma continuous_L {n : ℕ} (x : Fin n → ℝ) : Continuous (lebesgueFunction x) := by
  unfold lebesgueFunction
  exact continuous_finsetSum _ fun k _ => (Polynomial.continuous _).abs

lemma bdd_L {n : ℕ} (x : Fin n → ℝ) : BddAbove (lebesgueFunction x '' Set.Icc (-1 : ℝ) 1) :=
  (isCompact_Icc.image (continuous_L x)).bddAbove

lemma le_Lam {n : ℕ} (x : Fin n → ℝ) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    lebesgueFunction x t ≤ lebesgueConstant x :=
  le_csSup (bdd_L x) (Set.mem_image_of_mem _ ht)

lemma Lam_le {n : ℕ} (x : Fin n → ℝ) {M : ℝ}
    (h : ∀ t ∈ Set.Icc (-1 : ℝ) 1, lebesgueFunction x t ≤ M) : lebesgueConstant x ≤ M := by
  refine csSup_le ((Set.nonempty_Icc.mpr (by norm_num)).image _) ?_
  rintro _ ⟨t, ht, rfl⟩
  exact h t ht

lemma L_node {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) (j : Fin n) :
    lebesgueFunction x (x j) = 1 := by
  have e : ∀ k, (Lagrange.basis univ x k).eval (x j) = if k = j then 1 else 0 := by
    intro k
    split_ifs with h
    · subst h; exact Lagrange.eval_basis_self hx.injOn (mem_univ _)
    · exact Lagrange.eval_basis_of_ne h (mem_univ _)
  simp only [lebesgueFunction, e]
  rw [sum_eq_single j (fun b _ hb => by rw [if_neg hb]; norm_num) (by simp)]
  simp

lemma one_le_Lam {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ) (hx : IsNodeSet x) :
    1 ≤ lebesgueConstant x := by
  have := le_Lam x (hx.2 ⟨0, by omega⟩)
  rwa [L_node x hx.1.injective] at this

lemma abs_lb_le {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    |lb x k t| ≤ lebesgueFunction x t := by
  rw [lebesgueFunction_eq]
  exact single_le_sum (f := fun k => |lb x k t|) (fun _ _ => abs_nonneg _) (mem_univ k)

/-- Affine invariance of the Lebesgue function. -/
lemma L_affine {n : ℕ} (x : Fin n → ℝ) (a b : ℝ) (ha : a ≠ 0) (t : ℝ) :
    lebesgueFunction (fun i => a * x i + b) (a * t + b) = lebesgueFunction x t := by
  rw [lebesgueFunction_eq, lebesgueFunction_eq]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [show a * t + b - (a * x i + b) = a * (t - x i) by ring,
    show a * x k + b - (a * x i + b) = a * (x k - x i) by ring, mul_div_mul_left _ _ ha]

lemma L_scale {n : ℕ} (x : Fin n → ℝ) (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    lebesgueFunction (fun i => a * x i) (a * t) = lebesgueFunction x t := by
  simpa using L_affine x a 0 ha t

/-- A grid of `n` points in `[-1,1]` on which every monic polynomial of degree `n - 1` is not
uniformly small. -/
lemma grid (n : ℕ) (hn : 2 ≤ n) : ∃ (w : Fin n → ℝ) (D : ℝ), 0 < D ∧ IsNodeSet w ∧
    ∀ G : ℝ[X], G.degree < n → G.coeff (n - 1) = 1 → ∃ m, 1 ≤ D * |G.eval (w m)| := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set w : Fin n → ℝ := fun m => -1 + 2 * (m : ℝ) / ((n : ℝ) - 1) with hw
  have hmono : StrictMono w := by
    intro a b hab
    simp only [hw]
    have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left this two_pos) hn1
    linarith
  have hnode : IsNodeSet w := by
    refine ⟨hmono, fun m => ⟨?_, ?_⟩⟩
    · simp only [hw]
      have : 0 ≤ 2 * (m : ℝ) / ((n : ℝ) - 1) := div_nonneg (by positivity) hn1.le
      linarith
    · simp only [hw]
      have hm : (m : ℝ) ≤ (n : ℝ) - 1 := by
        have : (m : ℕ) + 1 ≤ n := m.2
        have : ((m : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast this
        linarith
      have : 2 * (m : ℝ) / ((n : ℝ) - 1) ≤ 2 := by
        rw [div_le_iff₀ hn1]; linarith
      linarith
  set a : Fin n → ℝ := fun m => |∏ j ∈ univ.erase m, (w m - w j)|⁻¹ with ha
  have ha0 : ∀ m, 0 ≤ a m := fun m => inv_nonneg.mpr (abs_nonneg _)
  refine ⟨w, ∑ m, a m + 1, by positivity, hnode, fun G hG hc => ?_⟩
  set D := ∑ m, a m + 1 with hD
  have hDpos : 0 < D := by positivity
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hcard : (#(univ : Finset (Fin n)) : WithBot ℕ) = n := by simp
  have key := Lagrange.coeff_eq_sum (s := (univ : Finset (Fin n))) hmono.injective.injOn
    (by rw [hcard]; exact hG)
  rw [card_univ, Fintype.card_fin, hc] at key
  have h1 : (1 : ℝ) ≤ ∑ m, |G.eval (w m)| * a m := by
    calc (1 : ℝ) = |∑ m, G.eval (w m) / ∏ j ∈ univ.erase m, (w m - w j)| := by
          rw [← key, abs_one]
      _ ≤ ∑ m, |G.eval (w m) / ∏ j ∈ univ.erase m, (w m - w j)| := abs_sum_le_sum_abs _ _
      _ = ∑ m, |G.eval (w m)| * a m := by
          refine sum_congr rfl fun m _ => ?_
          rw [abs_div, div_eq_mul_inv]
  have h2 : ∑ m, |G.eval (w m)| * a m ≤ ∑ m, (1 / D) * a m := by
    refine sum_le_sum fun m _ => mul_le_mul_of_nonneg_right ?_ (ha0 m)
    rw [le_div_iff₀ hDpos, mul_comm]
    exact (hcon m).le
  have h3 : ∑ m, (1 / D) * a m < 1 := by
    rw [← mul_sum, div_mul_eq_mul_div, one_mul, div_lt_one hDpos]
    linarith
  linarith

/-- Blow-up: close nodes force a large Lebesgue constant. -/
lemma blowup (n : ℕ) (hn : 2 ≤ n) : ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, IsNodeSet x →
    ∀ i j, i ≠ j → c ≤ |x j - x i| * lebesgueConstant x := by
  obtain ⟨w, D, hD, hw, hG⟩ := grid n hn
  refine ⟨1 / (D * 2 ^ n), by positivity, fun x hx i j hij => ?_⟩
  set G := Lagrange.nodal (univ.erase j) x with hGdef
  have hcardj : #(univ.erase j) = n - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have hGdeg : G.degree < n := by
    rw [Lagrange.degree_nodal, hcardj]
    exact_mod_cast (show n - 1 < n by omega)
  have hGc : G.coeff (n - 1) = 1 := by
    have := (Lagrange.nodal_monic (s := univ.erase j) (v := x)).coeff_natDegree
    rwa [Lagrange.natDegree_nodal, hcardj] at this
  obtain ⟨m, hm⟩ := hG G hGdeg hGc
  set P := ∏ i' ∈ univ.erase j, (x j - x i') with hP
  have hP0 : P ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun i' hi' => sub_ne_zero.mpr fun h => ?_
    exact (mem_erase.mp hi').1 (hx.1.injective h).symm
  have hlb : lb x j (w m) = G.eval (w m) / P := by
    rw [lb, prod_div_distrib, hGdef, Lagrange.eval_nodal]
  have hbound : ∀ i' ∈ (univ.erase j).erase i, |x j - x i'| ≤ 2 := by
    intro i' _
    have h1 := hx.2 j
    have h2 := hx.2 i'
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hPle : |P| ≤ |x j - x i| * 2 ^ n := by
    rw [hP, ← mul_prod_erase _ _ (mem_erase.mpr ⟨hij, mem_univ _⟩), abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_prod]
    calc ∏ i' ∈ (univ.erase j).erase i, |x j - x i'| ≤ ∏ _i' ∈ (univ.erase j).erase i, (2 : ℝ) := by
          gcongr with i' hi'
          exact hbound i' hi'
      _ = 2 ^ #((univ.erase j).erase i) := prod_const _
      _ ≤ 2 ^ n := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          exact (card_le_univ _).trans (by simp)
  have hL : |G.eval (w m)| / |P| ≤ lebesgueConstant x := by
    rw [← abs_div, ← hlb]
    exact (abs_lb_le x j (w m)).trans (le_Lam x (hw.2 m))
  have hPpos : 0 < |P| := abs_pos.mpr hP0
  have hLam0 : 0 ≤ lebesgueConstant x := le_trans zero_le_one (one_le_Lam (by omega) x hx)
  have hGle : |G.eval (w m)| ≤ lebesgueConstant x * |P| := by
    rwa [div_le_iff₀ hPpos] at hL
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℝ) ≤ D * |G.eval (w m)| := hm
    _ ≤ D * (lebesgueConstant x * (|x j - x i| * 2 ^ n)) := by
        refine mul_le_mul_of_nonneg_left (hGle.trans ?_) hD.le
        exact mul_le_mul_of_nonneg_left hPle hLam0
    _ = |x j - x i| * lebesgueConstant x * (D * 2 ^ n) := by ring


/-- Existence of a minimiser of the Lebesgue constant. -/
lemma exists_minimiser (n : ℕ) (hn : 2 ≤ n) : ∃ x : Fin n → ℝ, IsMinimiser x := by
  obtain ⟨c, hc, hblow⟩ := blowup n hn
  obtain ⟨w, D, -, hw, -⟩ := grid n hn
  set M := lebesgueConstant w with hM
  have hM1 : 1 ≤ M := one_le_Lam (by omega) w hw
  set δ := c / M with hδ
  have hδpos : 0 < δ := div_pos hc (by linarith)
  set K : Set (Fin n → ℝ) := (⋂ i, (fun y : Fin n → ℝ => y i) ⁻¹' Set.Icc (-1 : ℝ) 1) ∩
    ⋂ i, ⋂ j, ⋂ (_ : i < j), {y : Fin n → ℝ | y i + δ ≤ y j} with hK
  have memK : ∀ y, y ∈ K ↔ (∀ i, y i ∈ Set.Icc (-1 : ℝ) 1) ∧ ∀ i j, i < j → y i + δ ≤ y j := by
    intro y
    simp only [hK, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  have Knode : ∀ y ∈ K, IsNodeSet y := by
    intro y hy
    rw [memK] at hy
    exact ⟨fun i j hij => by linarith [hy.2 i j hij], hy.1⟩
  have inK : ∀ y, IsNodeSet y → lebesgueConstant y ≤ M → y ∈ K := by
    intro y hy hle
    rw [memK]
    refine ⟨hy.2, fun i j hij => ?_⟩
    have h1 := hblow y hy i j (ne_of_lt hij)
    have hpos : 0 < y j - y i := sub_pos.mpr (hy.1 hij)
    rw [abs_of_pos hpos] at h1
    have h2 : c ≤ (y j - y i) * M := h1.trans (mul_le_mul_of_nonneg_left hle hpos.le)
    have : δ ≤ y j - y i := by
      rw [hδ, div_le_iff₀ (by linarith)]; linarith
    linarith
  have hKc : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_ ?_
    · refine IsClosed.inter (isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i))
        (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
      exact isClosed_le ((continuous_apply i).add continuous_const) (continuous_apply j)
    · intro y hy
      rw [memK] at hy
      exact Set.mem_univ_pi.mpr hy.1
  have hwK : w ∈ K := inK w hw le_rfl
  -- continuity of the Lebesgue constant on `K`
  set F : K → ℝ → ℝ := fun y t => ∑ k, |∏ i ∈ univ.erase k, (t - y.1 i) / (y.1 k - y.1 i)|
    with hF
  have hFc : Continuous ↿F := by
    show Continuous fun p : K × ℝ =>
      ∑ k, |∏ i ∈ univ.erase k, (p.2 - p.1.1 i) / (p.1.1 k - p.1.1 i)|
    refine continuous_finsetSum _ fun k _ => (continuous_finsetProd _ fun i hi => ?_).abs
    have ci : ∀ l, Continuous fun p : K × ℝ => p.1.1 l :=
      fun l => (continuous_apply l).comp (continuous_subtype_val.comp continuous_fst)
    refine (continuous_snd.sub (ci i)).div ((ci k).sub (ci i)) fun p => sub_ne_zero.mpr ?_
    intro h
    exact (mem_erase.mp hi).1 ((Knode p.1.1 p.1.2).1.injective h).symm
  have hFeq : ∀ y : K, F y = lebesgueFunction y.1 :=
    fun y => funext fun t => (lebesgueFunction_eq y.1 t).symm
  have hcontK : ContinuousOn lebesgueConstant K := by
    refine continuousOn_iff_continuous_restrict.mpr (((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).continuous_sSup hFc).congr ?_)
    intro y
    show sSup (F y '' Set.Icc (-1 : ℝ) 1) = lebesgueConstant y.1
    rw [hFeq]
    rfl
  obtain ⟨x, hxK, hmin⟩ := hKc.exists_isMinOn ⟨w, hwK⟩ hcontK
  refine ⟨x, Knode x hxK, fun y hy => ?_⟩
  by_cases hle : lebesgueConstant y ≤ M
  · exact hmin (inK y hy hle)
  · exact (hmin hwK).trans (le_of_lt (not_le.mp hle))

/-- Rescaling a minimiser to a canonical one. -/
lemma exists_canonical_minimiser (n : ℕ) (hn : 2 ≤ n) : ∃ x : Fin n → ℝ, IsMinimiser x ∧
    x ⟨0, by omega⟩ = -1 ∧ x ⟨n - 1, by omega⟩ = 1 := by
  obtain ⟨y, hy, hymin⟩ := exists_minimiser n hn
  set p := y ⟨0, by omega⟩ with hp
  set q := y ⟨n - 1, by omega⟩ with hq
  have hpq : p < q := hy.1 (Fin.mk_lt_mk.mpr (by omega))
  have hpy : ∀ i, p ≤ y i := fun i => hy.1.monotone (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
  have hyq : ∀ i, y i ≤ q := fun i => hy.1.monotone (Fin.le_iff_val_le_val.mpr (by simp; omega))
  have hp1 : -1 ≤ p := (hy.2 _).1
  have hq1 : q ≤ 1 := (hy.2 _).2
  set a := 2 / (q - p) with ha
  have hqp : 0 < q - p := sub_pos.mpr hpq
  have hapos : 0 < a := div_pos two_pos hqp
  set b := -1 - a * p with hb
  have haq : a * (q - p) = 2 := by rw [ha, div_mul_cancel₀ _ hqp.ne']
  refine ⟨fun i => a * y i + b, ⟨⟨fun i j hij => ?_, fun i => ⟨?_, ?_⟩⟩, fun z hz => ?_⟩, ?_, ?_⟩
  · have := mul_lt_mul_of_pos_left (hy.1 hij) hapos
    linarith
  · have := mul_le_mul_of_nonneg_left (hpy i) hapos.le
    rw [hb]; linarith
  · have := mul_le_mul_of_nonneg_left (hyq i) hapos.le
    rw [hb]; nlinarith
  · refine le_trans (Lam_le _ fun s hs => ?_) (hymin z hz)
    set t := p + (s + 1) / a with ht
    have hst : a * t + b = s := by
      rw [ht, hb, mul_add, mul_div_cancel₀ _ hapos.ne']; ring
    rw [← hst, L_affine y a b hapos.ne']
    refine le_Lam y ⟨?_, ?_⟩
    · have : 0 ≤ (s + 1) / a := div_nonneg (by linarith [hs.1]) hapos.le
      linarith
    · have e : (s + 1) / a = (s + 1) * (q - p) / 2 := by
        rw [ha, div_div_eq_mul_div]
      have : (s + 1) * (q - p) ≤ 2 * (q - p) := mul_le_mul_of_nonneg_right (by linarith [hs.2]) hqp.le
      rw [ht, e]
      linarith
  · show a * p + b = -1
    rw [hb]; ring
  · show a * q + b = 1
    rw [hb]; linarith

/-- For `n ≥ 3` the Lebesgue constant exceeds `1`. -/
lemma one_lt_Lam (n : ℕ) (hn : 3 ≤ n) (x : Fin n → ℝ) (hx : IsNodeSet x) :
    1 < lebesgueConstant x := by
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  have h01 : x i0 < x i1 := hx.1 (Fin.mk_lt_mk.mpr (by omega))
  have h12 : x i1 < x i2 := hx.1 (Fin.mk_lt_mk.mpr (by omega))
  set t := (x i0 + x i1) / 2 with ht
  have hneg : lb x i2 t < 0 := by
    have hi1 : i1 ∈ univ.erase i2 := mem_erase.mpr ⟨fun h => by simp [i1, i2] at h, mem_univ _⟩
    rw [lb, ← mul_prod_erase _ _ hi1]
    refine mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) (by linarith))
      (prod_pos fun i hi => ?_)
    have hne1 : i ≠ i1 := (mem_erase.mp hi).1
    have hne2 : i ≠ i2 := (mem_erase.mp (mem_erase.mp hi).2).1
    have v1 : (i : ℕ) ≠ 1 := fun h => hne1 (Fin.ext h)
    have v2 : (i : ℕ) ≠ 2 := fun h => hne2 (Fin.ext h)
    rcases Nat.lt_or_ge (i : ℕ) 3 with h | h
    · have : i = i0 := Fin.ext (by simp [i0]; omega)
      subst this
      exact div_pos (by linarith) (by linarith)
    · have h2i : x i2 < x i := hx.1 (Fin.lt_iff_val_lt_val.mpr (show 2 < (i : ℕ) by omega))
      exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  have hsum := sum_lb (by omega) x hx.1.injective t
  have hlt : ∑ k, lb x k t < lebesgueFunction x t := by
    rw [lebesgueFunction_eq]
    exact sum_lt_sum (fun k _ => le_abs_self _) ⟨i2, mem_univ _, hneg.trans_le (abs_nonneg _)⟩
  have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have := (hx.2 i0).1
    have := (hx.2 i1).2
    constructor <;> linarith
  linarith [le_Lam x hmem]

theorem main (n : ℕ) (hn : 3 ≤ n) : ¬ {x : Fin n → ℝ | IsMinimiser x}.Countable := by
  obtain ⟨x, hxm, hx0, hx1⟩ := exists_canonical_minimiser n (by omega)
  set Ls := lebesgueConstant x with hLs
  have hgt : 1 < Ls := one_lt_Lam n hn x hxm.1
  have hinj := hxm.1.1.injective
  have hL1 : lebesgueFunction x 1 = 1 := by
    have := L_node x hinj ⟨n - 1, by omega⟩
    rwa [hx1] at this
  have hLm1 : lebesgueFunction x (-1) = 1 := by
    have := L_node x hinj ⟨0, by omega⟩
    rwa [hx0] at this
  have ev1 : ∀ᶠ u in nhds (1 : ℝ), lebesgueFunction x u < Ls :=
    (continuous_L x).continuousAt.eventually (gt_mem_nhds (by rw [hL1]; exact hgt))
  have ev2 : ∀ᶠ u in nhds (-1 : ℝ), lebesgueFunction x u < Ls :=
    (continuous_L x).continuousAt.eventually (gt_mem_nhds (by rw [hLm1]; exact hgt))
  obtain ⟨ε1, hε1, h1⟩ := Metric.eventually_nhds_iff.mp ev1
  obtain ⟨ε2, hε2, h2⟩ := Metric.eventually_nhds_iff.mp ev2
  set ε := min ε1 ε2 with hε
  have hεpos : 0 < ε := lt_min hε1 hε2
  set z : ℝ → Fin n → ℝ := fun τ i => τ⁻¹ * x i with hz
  have hmaps : Set.MapsTo z (Set.Ioo 1 (1 + ε)) {x : Fin n → ℝ | IsMinimiser x} := by
    intro τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have hinv0 : 0 < τ⁻¹ := inv_pos.mpr hτ0
    have hinv1 : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hτ.1
    have hnode : IsNodeSet (z τ) := by
      refine ⟨fun i j hij => mul_lt_mul_of_pos_left (hxm.1.1 hij) hinv0, fun i => ⟨?_, ?_⟩⟩
      · have := mul_le_mul_of_nonneg_left (hxm.1.2 i).1 hinv0.le
        show -1 ≤ τ⁻¹ * x i
        linarith
      · have := mul_le_mul_of_nonneg_left (hxm.1.2 i).2 hinv0.le
        show τ⁻¹ * x i ≤ 1
        linarith
    have hle : lebesgueConstant (z τ) ≤ Ls := by
      refine Lam_le _ fun s hs => ?_
      have e : s = τ⁻¹ * (τ * s) := by rw [← mul_assoc, inv_mul_cancel₀ hτ0.ne', one_mul]
      have hsc := L_scale x τ⁻¹ hinv0.ne' (τ * s)
      rw [← e] at hsc
      show lebesgueFunction (fun i => τ⁻¹ * x i) s ≤ Ls
      rw [hsc]
      have hu1 : τ * s ≤ τ := by nlinarith [hs.2]
      have hu2 : -τ ≤ τ * s := by nlinarith [hs.1]
      rcases le_or_gt (τ * s) 1 with hA | hA
      · rcases le_or_gt (-1) (τ * s) with hB | hB
        · exact le_Lam x ⟨hB, hA⟩
        · refine (h2 ?_).le
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hτ.2, min_le_right ε1 ε2]
      · refine (h1 ?_).le
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hτ.2, min_le_left ε1 ε2]
    exact ⟨hnode, fun y hy => hle.trans (hxm.2 y hy)⟩
  have hinjOn : Set.InjOn z (Set.Ioo 1 (1 + ε)) := by
    intro τ1 _ τ2 _ heq
    have := congrFun heq ⟨n - 1, by omega⟩
    simp only [hz, hx1, mul_one] at this
    exact inv_inj.mp this
  intro hc
  have := hmaps.countable_of_injOn hinjOn hc
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real (by linarith)] at this
  exact absurd this (not_le.mpr Cardinal.aleph0_lt_continuum)

end OMA.E1129F

theorem OMA.solution : type_of% @Erdos1129.erdos_1129.variants.free_nodes_not_unique := by
  intro n hn
  exact OMA.E1129F.main n hn

