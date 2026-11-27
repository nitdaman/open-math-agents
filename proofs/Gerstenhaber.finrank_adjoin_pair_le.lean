import FormalConjectures.Other.GerstenhaberThreeMatrices
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Proof of Gerstenhaber's Theorem (`dim K[A, B] ≤ n`)

We prove Gerstenhaber's theorem (`Gerstenhaber.finrank_adjoin_pair_le`) over an arbitrary field `K`
following Wadsworth's (1990) module-theoretic proof:
1. Over any nontrivial commutative ring `R`, an `R`-linear endomorphism `g` of a `k`-generated
   `R`-module satisfies a monic degree-`k` polynomial equation in `R[Y]` (by Cayley–Hamilton
   `Matrix.aeval_self_charpoly` on a representing `k × k` matrix over `R`).
2. Viewing `M` as a finitely generated torsion `K[X]`-module via `Module.AEval' a`, primary
   decomposition (`Submodule.exists_isInternal_prime_power_torsion_of_pid`) splits `M` into
   `a`- and `b`-invariant primary components `W_i = torsionBy K[X] M (p_i^{e_i})`, reducing the
   bound to a single primary component `M ≃ₗ[K[X]] ⨁_{j : Fin r} K[X] ⧸ (p^{e_j})` with
   `e_0 ≥ e_1 ≥ ⋯ ≥ e_{r-1}`.
3. On a single primary component, let `C_k = ∑_{j < k} K[a] b^j`. Applying step 1 to `b` on `M`
   gives `b^r ∈ C_r` and hence `K[a, b] ≤ C_r`; applying step 1 to `b` on the `k`-generated
   `K[X]`-submodule `p^{e_k} • M` gives `p^{e_k}(a) b^k ∈ C_k`, yielding a surjection
   `K[X] ⧸ (p^{e_k}) ↠ C_{k+1} / C_k` and hence `finrank K C_r ≤ ∑_k finrank K (K[X] ⧸ (p^{e_k})) = finrank K M`.
-/

-- Problem: Gerstenhaber's theorem
-- Upstream: formal-conjectures FormalConjectures/Other/GerstenhaberThreeMatrices.lean:51 (declaration Gerstenhaber.finrank_adjoin_pair_le)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace GerstenhaberProof

open Polynomial
open scoped Classical DirectSum

private lemma aeval_commute {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A]
    {a b : A} (hab : Commute a b) (q : K[X]) : Commute (Polynomial.aeval a q) b := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ ih₁ ih₂ =>
    rw [map_add]
    exact ih₁.add_left ih₂
  | monomial d r =>
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
    exact (hab.pow_left d).smul_left r

private lemma exists_monic_annihilating {R N : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup N] [Module R N] (g : N →ₗ[R] N) {k : ℕ} (v : Fin k → N)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    ∃ c : Fin k → R, g ^ k + ∑ m : Fin k, c m • g ^ m.1 = 0 := by
  have hrep : ∀ j : Fin k, ∃ col : Fin k → R, g (v j) = ∑ i : Fin k, col i • v i := by
    intro j
    have hmem : g (v j) ∈ Submodule.span R (Set.range v) := hv.symm ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    rcases hmem with ⟨col, hcol⟩
    exact ⟨col, hcol.symm⟩
  let T : Matrix (Fin k) (Fin k) R := fun i j => Classical.choose (hrep j) i
  have hTv : ∀ j : Fin k, g (v j) = ∑ i : Fin k, T i j • v i := fun j =>
    Classical.choose_spec (hrep j)
  have hpow : ∀ (d : ℕ) (j : Fin k), (g ^ d) (v j) = ∑ i : Fin k, (T ^ d) i j • v i := by
    intro d
    induction d with
    | zero =>
      intro j
      simp [Matrix.one_apply]
    | succ d ih =>
      intro j
      rw [pow_succ', Module.End.mul_apply, ih, map_sum]
      calc
        (∑ l : Fin k, g ((T ^ d) l j • v l))
            = ∑ l : Fin k, (T ^ d) l j • ∑ i : Fin k, T i l • v i := by
              refine Finset.sum_congr rfl fun l _ => ?_
              rw [map_smul, hTv l]
        _ = ∑ l : Fin k, ∑ i : Fin k, (T i l * (T ^ d) l j) • v i := by
              refine Finset.sum_congr rfl fun l _ => ?_
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [smul_smul, mul_comm]
        _ = ∑ i : Fin k, ∑ l : Fin k, (T i l * (T ^ d) l j) • v i := Finset.sum_comm
        _ = ∑ i : Fin k, (T ^ (d + 1)) i j • v i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.sum_smul, pow_succ', Matrix.mul_apply]
  have haeval : ∀ (Q : R[X]) (j : Fin k),
      Polynomial.aeval g Q (v j) = ∑ i : Fin k, (Polynomial.aeval T Q) i j • v i := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add Q₁ Q₂ ih₁ ih₂ =>
      intro j
      simp only [map_add, LinearMap.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib,
        ih₁, ih₂]
    | monomial d r =>
      intro j
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
      simp only [LinearMap.smul_apply, Matrix.smul_apply, hpow d j, Finset.smul_sum, smul_smul,
        smul_eq_mul]
  let P : R[X] := T.charpoly
  have hP_zero : Polynomial.aeval T P = 0 := Matrix.aeval_self_charpoly T
  have hP_monic : P.Monic := Matrix.charpoly_monic T
  have hP_deg : P.natDegree = k := by
    simp [P]
  have hPg_v : ∀ j : Fin k, Polynomial.aeval g P (v j) = 0 := fun j => by
    rw [haeval P j, hP_zero]
    simp
  have hPg_zero : Polynomial.aeval g P = 0 := by
    ext x
    have hx : x ∈ Submodule.span R (Set.range v) := hv.symm ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    rcases hx with ⟨a, rfl⟩
    simp [map_sum, map_smul, hPg_v]
  have hP_expand : P = X ^ k + ∑ m : Fin k, C (P.coeff m.1) * X ^ m.1 := by
    conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
    rw [hP_deg, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range]
    have hlead : P.coeff k = 1 := by
      rw [← hP_deg]
      exact hP_monic.leadingCoeff
    rw [hlead, map_one, one_mul, add_comm]
  refine ⟨fun m => P.coeff m.1, ?_⟩
  have h1 : Polynomial.aeval g P = g ^ k + ∑ m : Fin k, P.coeff m.1 • g ^ m.1 := by
    conv_lhs => rw [hP_expand]
    simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, ← Algebra.smul_def]
  rw [← h1, hPg_zero]

private lemma finrank_adjoin_le_of_equiv_directSum_pow
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (a b : Module.End K M) (hab : Commute a b)
    (p : K[X]) (r : ℕ) (e : Fin r → ℕ) (he : Antitone e)
    (eM : Module.AEval' a ≃ₗ[K[X]] ⨁ j : Fin r, K[X] ⧸ (K[X] ∙ p ^ e j)) :
    Module.finrank K (Algebra.adjoin K ({a, b} : Set (Module.End K M))) ≤ Module.finrank K M := by
  by_cases hr0 : r = 0
  · subst hr0
    have hsub_ds : Subsingleton (⨁ j : Fin 0, K[X] ⧸ (K[X] ∙ p ^ e j)) := by
      refine ⟨fun x y => ?_⟩
      ext j
      exact j.elim0
    have hsub_M : Subsingleton M :=
      (Module.AEval'.of a).toEquiv.trans eM.toEquiv |>.subsingleton
    have hsub_end : Subsingleton (Module.End K M) := inferInstance
    have hsub_adj : Subsingleton (Algebra.adjoin K ({a, b} : Set (Module.End K M))) := inferInstance
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
  let Ma := Module.AEval' a
  let Q : Fin r → Type _ := fun j => K[X] ⧸ (K[X] ∙ p ^ e j)
  have hQ_fin : ∀ j : Fin r, Module.Finite K (Q j) := by
    intro j
    let inj : Q j →ₗ[K] M :=
      ((Module.AEval'.of a).symm.toLinearMap).comp
        ((eM.symm.restrictScalars K).toLinearMap.comp
          ((DirectSum.lof K[X] (Fin r) Q j).restrictScalars K))
    have hinj : Function.Injective inj :=
      (Module.AEval'.of a).symm.injective.comp
        (eM.symm.injective.comp fun x y h => by
          simpa [DirectSum.lof_eq_of, DirectSum.of_apply] using congrArg (fun z => z j) h)
    exact Module.Finite.of_injective inj hinj
  let bR : Ma →ₗ[K[X]] Ma :=
    LinearMap.ofAEval a ((Module.AEval'.of a).toLinearMap.comp b) fun m => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      rw [Module.AEval'.X_smul_of]
      exact congrArg (Module.AEval'.of a) (congrArg (fun f => f m) hab.symm.eq)
  have hbR_apply : ∀ m : M, bR (Module.AEval'.of a m) = Module.AEval'.of a (b m) := fun _ => rfl
  have hbR_pow : ∀ (k : ℕ) (m : M), (bR ^ k) (Module.AEval'.of a m) = Module.AEval'.of a ((b ^ k) m) := by
    intro k
    induction k with
    | zero => intro m; rfl
    | succ k ih =>
      intro m
      rw [pow_succ', Module.End.mul_apply, ih, hbR_apply, pow_succ', Module.End.mul_apply]
  let v : Fin r → Ma := fun j => eM.symm (DirectSum.lof K[X] (Fin r) Q j 1)
  have hv_span : Submodule.span K[X] (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hsum : eM x = ∑ j : Fin r, DirectSum.lof K[X] (Fin r) Q j (eM x j) := by
      ext i
      simp [DirectSum.lof_eq_of, DirectSum.of_apply]
    have hlift : ∀ j : Fin r, ∃ f : K[X], eM x j = f • (1 : Q j) := by
      intro j
      obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (eM x j)
      refine ⟨f, ?_⟩
      rw [← hf]
      change Submodule.Quotient.mk f = f • Submodule.Quotient.mk 1
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
    choose F hF using hlift
    have hx_eq : x = ∑ j : Fin r, F j • v j := by
      apply eM.injective
      rw [map_sum, hsum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, eM.apply_symm_apply, hF j, map_smul]
    rw [hx_eq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- Subspaces `C k = {∑_{j < k} aeval a (F j) * b^j}`
  let evalSum (k : ℕ) : (Fin k → K[X]) →ₗ[K] Module.End K M :=
    { toFun := fun F => ∑ j : Fin k, Polynomial.aeval a (F j) * b ^ j.1
      map_add' := fun F G => by
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c F => by
        simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply] }
  let C : ℕ → Submodule K (Module.End K M) := fun k => LinearMap.range (evalSum k)
  have hC0 : C 0 = ⊥ := by
    ext x
    simp [C, evalSum, eq_comm]
  have hC_aeval_mul : ∀ (k : ℕ) (q : K[X]) {x : Module.End K M},
      x ∈ C k → Polynomial.aeval a q * x ∈ C k := by
    rintro k q _ ⟨F, rfl⟩
    refine ⟨fun j => q * F j, ?_⟩
    dsimp only [evalSum, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_assoc]
  have hC_mono : ∀ k : ℕ, C k ≤ C (k + 1) := by
    rintro k _ ⟨F, rfl⟩
    refine ⟨Fin.snoc F 0, ?_⟩
    dsimp only [evalSum, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Fin.sum_univ_castSucc]
    simp
  let ψ (k : ℕ) : K[X] →ₗ[K] Module.End K M :=
    { toFun := fun f => Polynomial.aeval a f * b ^ k
      map_add' := fun f g => by simp [map_add, add_mul]
      map_smul' := fun c f => by simp [map_smul] }
  have hC_succ : ∀ k : ℕ, C (k + 1) = C k ⊔ LinearMap.range (ψ k) := by
    intro k
    apply le_antisymm
    · rintro _ ⟨F, rfl⟩
      dsimp only [evalSum, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Fin.sum_univ_castSucc]
      exact Submodule.add_mem_sup ⟨fun j => F j.castSucc, rfl⟩ ⟨F (Fin.last k), rfl⟩
    · refine sup_le (hC_mono k) ?_
      rintro _ ⟨f, rfl⟩
      refine ⟨Fin.snoc 0 f, ?_⟩
      dsimp only [evalSum, ψ, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Fin.sum_univ_castSucc]
      simp
  -- Claim A: `b ^ r ∈ C r` via Cayley–Hamilton on `Ma`
  have hbr_mem : b ^ r ∈ C r := by
    obtain ⟨c, hc⟩ := exists_monic_annihilating bR v hv_span
    refine ⟨fun m => -c m, ?_⟩
    dsimp only [evalSum, LinearMap.coe_mk, AddHom.coe_mk]
    ext x
    have h0 := congrArg (fun f : Ma →ₗ[K[X]] Ma => (Module.AEval'.of a).symm (f (Module.AEval'.of a x))) hc
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      map_add, map_sum, map_zero, hbR_pow,
      LinearEquiv.symm_apply_apply] at h0
    have h0' : (b ^ r) x + ∑ j : Fin r, Polynomial.aeval a (c j) ((b ^ j.1) x) = 0 := h0
    simp only [LinearMap.sum_apply]
    have hsum_neg : (∑ j : Fin r, (Polynomial.aeval a (-c j) * b ^ j.1) x) =
        -(∑ j : Fin r, Polynomial.aeval a (c j) ((b ^ j.1) x)) := by
      simp only [map_neg, neg_mul, LinearMap.neg_apply, Finset.sum_neg_distrib]
      rfl
    rw [hsum_neg]
    exact neg_eq_of_add_eq_zero_right (by rw [add_comm]; exact h0')
  -- Hence `C r` contains `Algebra.adjoin K {a, b}`
  have hC_b_mul : ∀ {x : Module.End K M}, x ∈ C r → b * x ∈ C r := by
    rintro _ ⟨F, rfl⟩
    dsimp only [evalSum, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.mul_sum]
    refine Submodule.sum_mem (C r) fun j _ => ?_
    have hcomm : b * (Polynomial.aeval a (F j) * b ^ j.1) =
        Polynomial.aeval a (F j) * b ^ (j.1 + 1) := by
      have hcomm1 : Commute b (Polynomial.aeval a (F j)) :=
        Commute.symm (aeval_commute hab (F j))
      rw [← mul_assoc, hcomm1.eq, mul_assoc, ← pow_succ']
    rw [hcomm]
    by_cases hlt : j.1 + 1 < r
    · refine ⟨Pi.single ⟨j.1 + 1, hlt⟩ (F j), ?_⟩
      dsimp only [evalSum, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single ⟨j.1 + 1, hlt⟩]
      · simp
      · intro i _ hi
        simp [Pi.single_eq_of_ne hi]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    · have heq : j.1 + 1 = r := by omega
      rw [heq]
      exact hC_aeval_mul r (F j) hbr_mem
  have hC_b_pow_mul : ∀ (m : ℕ) {x : Module.End K M}, x ∈ C r → b ^ m * x ∈ C r := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      intro x hx
      rw [pow_succ', mul_assoc]
      exact hC_b_mul (ih hx)
  have hone_mem : (1 : Module.End K M) ∈ C r := by
    refine ⟨Pi.single ⟨0, hr_pos⟩ 1, ?_⟩
    dsimp only [evalSum, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single ⟨0, hr_pos⟩]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hC_mul : ∀ {x y : Module.End K M}, x ∈ C r → y ∈ C r → x * y ∈ C r := by
    rintro _ y ⟨F, rfl⟩ hy
    dsimp only [evalSum, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_mul]
    refine Submodule.sum_mem (C r) fun j _ => ?_
    rw [mul_assoc]
    exact hC_aeval_mul r (F j) (hC_b_pow_mul j.1 hy)
  let CrAlg : Subalgebra K (Module.End K M) :=
    { carrier := C r
      add_mem' := (C r).add_mem
      zero_mem' := (C r).zero_mem
      one_mem' := hone_mem
      mul_mem' := hC_mul
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact (C r).smul_mem c hone_mem }
  have hadj_le : Algebra.adjoin K ({a, b} : Set (Module.End K M)) ≤ CrAlg := by
    refine Algebra.adjoin_le ?_
    rintro x (hx | hx)
    · rw [hx]
      change a ∈ C r
      have ha1 : a = Polynomial.aeval a (X : K[X]) * 1 := by simp
      rw [ha1]
      exact hC_aeval_mul r X hone_mem
    · rw [hx]
      change b ∈ C r
      simpa using hC_b_mul hone_mem
  -- Claim B: for every `k : Fin r`, `aeval a (p ^ e k) * b ^ k ∈ C k`
  have hpk_mem : ∀ k : Fin r, Polynomial.aeval a (p ^ e k) * b ^ k.1 ∈ C k.1 := by
    intro k
    let Nk : Submodule K[X] Ma := LinearMap.range (p ^ e k • (LinearMap.id : Ma →ₗ[K[X]] Ma))
    have hNk_inv : ∀ y ∈ Nk, bR y ∈ Nk := by
      rintro _ ⟨x, rfl⟩
      exact ⟨bR x, by simp [map_smul]⟩
    let bk : Nk →ₗ[K[X]] Nk := bR.restrict hNk_inv
    have hbk_pow : ∀ (m : ℕ) (y : Nk), ((bk ^ m) y : Ma) = (bR ^ m) (y : Ma) := by
      intro m
      induction m with
      | zero => intro y; rfl
      | succ m ih =>
        intro y
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
        change bR ((bk ^ m) y : Ma) = bR ((bR ^ m) (y : Ma))
        rw [ih y]
    let w : Fin k.1 → Nk := fun i =>
      ⟨p ^ e k • v ⟨i.1, lt_trans i.2 k.2⟩, ⟨v ⟨i.1, lt_trans i.2 k.2⟩, rfl⟩⟩
    have hw_span : Submodule.span K[X] (Set.range w) = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨y, ⟨x, rfl⟩⟩ _
      have hx : x ∈ Submodule.span K[X] (Set.range v) := hv_span.symm ▸ Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hx
      rcases hx with ⟨F, hF⟩
      have hkill : ∀ j : Fin r, k ≤ j → p ^ e k • v j = 0 := by
        intro j hkj
        have he_le : e j ≤ e k := he hkj
        have hdvd : p ^ e j ∣ p ^ e k := pow_dvd_pow p he_le
        apply eM.injective
        rw [map_smul, map_zero, eM.apply_symm_apply, ← map_smul]
        have hq0 : p ^ e k • (1 : Q j) = 0 := by
          change Submodule.Quotient.mk (p ^ e k * 1) = 0
          rw [mul_one, Submodule.Quotient.mk_eq_zero]
          exact Submodule.mem_span_singleton.mpr (by
            rcases hdvd with ⟨q, hq⟩
            exact ⟨q, by rw [smul_eq_mul, mul_comm, hq]⟩)
        rw [hq0, map_zero]
      have hy_eq : (⟨p ^ e k • x, ⟨x, rfl⟩⟩ : Nk) =
          ∑ i : Fin k.1, F ⟨i.1, lt_trans i.2 k.2⟩ • w i := by
        apply Subtype.ext
        simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, w]
        rw [← hF, Finset.smul_sum]
        have hsplit : (∑ j : Fin r, p ^ e k • (F j • v j)) =
            ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.1 < k.1), p ^ e k • (F j • v j) := by
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hnot => ?_
          have hge : k ≤ j := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
            exact hnot
          rw [smul_comm, hkill j hge, smul_zero]
        rw [hsplit]
        refine Finset.sum_bij (fun (j : Fin r) hj => ⟨j.1, (Finset.mem_filter.mp hj).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (congrArg (Fin.val (n := k.1)) h))
          (fun i _ => ⟨⟨i.1, lt_trans i.2 k.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩, rfl⟩)
          (fun j hj => by rw [smul_comm])
      change (⟨p ^ e k • x, ⟨x, rfl⟩⟩ : Nk) ∈ Submodule.span K[X] (Set.range w)
      rw [hy_eq]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨c, hc⟩ := exists_monic_annihilating bk w hw_span
    refine ⟨fun m => -(c m * p ^ e k), ?_⟩
    dsimp only [evalSum, LinearMap.coe_mk, AddHom.coe_mk]
    ext x
    let yk : Nk := ⟨p ^ e k • Module.AEval'.of a x, ⟨Module.AEval'.of a x, rfl⟩⟩
    have h0 := congrArg (fun f : Nk →ₗ[K[X]] Nk => (Module.AEval'.of a).symm ((f yk : Nk) : Ma)) hc
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      AddSubmonoidClass.coe_finsetSum, Submodule.coe_add, SetLike.val_smul, Submodule.coe_zero,
      map_add, map_sum, map_zero, hbk_pow] at h0
    have hterm : ∀ m : ℕ, (Module.AEval'.of a).symm ((bR ^ m) (yk : Ma)) =
        (Polynomial.aeval a (p ^ e k) * b ^ m) x := by
      intro m
      change (Module.AEval'.of a).symm ((bR ^ m) (p ^ e k • Module.AEval'.of a x)) = _
      rw [map_smul, hbR_pow, Module.AEval.of_symm_smul, LinearEquiv.symm_apply_apply]
      rfl
    have hterm_c : ∀ m : Fin k.1,
        (Module.AEval'.of a).symm (c m • (bR ^ m.1) (yk : Ma)) =
          (Polynomial.aeval a (c m * p ^ e k) * b ^ m.1) x := by
      intro m
      rw [Module.AEval.of_symm_smul, hterm m.1, map_mul, mul_assoc]
      rfl
    rw [hterm k.1] at h0
    have hsum0 : (∑ m : Fin k.1, (Module.AEval'.of a).symm (c m • (bR ^ m.1) (yk : Ma))) =
        ∑ m : Fin k.1, (Polynomial.aeval a (c m * p ^ e k) * b ^ m.1) x :=
      Finset.sum_congr rfl fun m _ => hterm_c m
    rw [hsum0] at h0
    simp only [LinearMap.sum_apply]
    have hsum_neg : (∑ m : Fin k.1, (Polynomial.aeval a (-(c m * p ^ e k)) * b ^ m.1) x) =
        -(∑ m : Fin k.1, (Polynomial.aeval a (c m * p ^ e k) * b ^ m.1) x) := by
      simp only [map_neg, neg_mul, LinearMap.neg_apply, Finset.sum_neg_distrib]
    rw [hsum_neg]
    exact neg_eq_of_add_eq_zero_right (by rw [add_comm]; exact h0)
  -- Dimension bound per step: `finrank K (C (k + 1)) ≤ finrank K (C k) + finrank K (Q k)`
  have hstep : ∀ k : Fin r,
      Module.finrank K (C (k.1 + 1)) ≤ Module.finrank K (C k.1) + Module.finrank K (Q k) := by
    intro k
    let S1 : Submodule K (Module.End K M) := C (k.1 + 1)
    let P0 : Submodule K S1 := (C k.1).comap S1.subtype
    have hP0_eq : Module.finrank K P0 = Module.finrank K (C k.1) := by
      let eqP : P0 ≃ₗ[K] C k.1 :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun x => ⟨⟨x.1, hC_mono k.1 x.2⟩, x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact eqP.finrank_eq
    have hquot_add : Module.finrank K (S1 ⧸ P0) + Module.finrank K P0 = Module.finrank K S1 :=
      Submodule.finrank_quotient_add_finrank P0
    let g : K[X] →ₗ[K] (S1 ⧸ P0) :=
      { toFun := fun f => Submodule.Quotient.mk ⟨ψ k.1 f, by
          change ψ k.1 f ∈ C (k.1 + 1)
          rw [hC_succ k.1]
          exact Submodule.mem_sup_right ⟨f, rfl⟩⟩
        map_add' := fun f₁ f₂ => by
          rw [← Submodule.Quotient.mk_add]
          congr 1; apply Subtype.ext; exact map_add (ψ k.1) f₁ f₂
        map_smul' := fun c f => by
          rw [← Submodule.Quotient.mk_smul]
          congr 1; apply Subtype.ext; exact map_smul (ψ k.1) c f }
    have hg_surj : Function.Surjective g := by
      rintro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective P0 q
      have hx' : x ∈ C k.1 ⊔ LinearMap.range (ψ k.1) := (hC_succ k.1) ▸ hx
      rcases Submodule.mem_sup.mp hx' with ⟨y, hy, _, ⟨f, rfl⟩, hxy⟩
      refine ⟨f, ?_⟩
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      rw [Submodule.Quotient.eq]
      change ψ k.1 f - x ∈ C k.1
      have hsub : ψ k.1 f - x = -y := by
        rw [← hxy]
        abel
      rw [hsub]
      exact (C k.1).neg_mem hy
    have hker : (K[X] ∙ p ^ e k).restrictScalars K ≤ LinearMap.ker g := by
      intro f hf
      change f ∈ K[X] ∙ p ^ e k at hf
      rw [Submodule.mem_span_singleton] at hf
      rcases hf with ⟨q, rfl⟩
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = (0 : S1 ⧸ P0)
      rw [Submodule.Quotient.mk_eq_zero]
      change ψ k.1 (q • p ^ e k) ∈ C k.1
      dsimp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
      rw [smul_eq_mul, map_mul, mul_assoc]
      exact hC_aeval_mul k.1 q (hpk_mem k)
    let gbar : Q k →ₗ[K] (S1 ⧸ P0) := Submodule.liftQ ((K[X] ∙ p ^ e k).restrictScalars K) g hker
    have hgbar_surj : Function.Surjective gbar := by
      intro z
      obtain ⟨f, rfl⟩ := hg_surj z
      exact ⟨Submodule.Quotient.mk f, rfl⟩
    have : Module.Finite K (Q k) := hQ_fin k
    have hle_q : Module.finrank K (S1 ⧸ P0) ≤ Module.finrank K (Q k) :=
      LinearMap.finrank_le_finrank_of_surjective hgbar_surj
    have hS1_eq : Module.finrank K S1 = Module.finrank K (C (k.1 + 1)) := rfl
    omega
  -- Telescope from `0` to `r`
  have htelescope : ∀ (m : ℕ) (hm : m ≤ r),
      Module.finrank K (C m) ≤ ∑ j : Fin m, Module.finrank K (Q ⟨j.1, lt_of_lt_of_le j.2 hm⟩) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [hC0, finrank_bot]
      simp
    | succ m ih =>
      intro hm
      rw [Fin.sum_univ_castSucc]
      have h1 := hstep ⟨m, hm⟩
      have h2 := ih (Nat.le_of_succ_le hm)
      exact le_trans h1 (Nat.add_le_add_right h2 _)
  have hCr_le : Module.finrank K (C r) ≤ ∑ j : Fin r, Module.finrank K (Q j) := htelescope r le_rfl
  have hadj_le_Cr : Module.finrank K (Algebra.adjoin K ({a, b} : Set (Module.End K M))) ≤
      Module.finrank K (C r) :=
    Submodule.finrank_mono (show (Algebra.adjoin K ({a, b} : Set (Module.End K M))).toSubmodule ≤ C r
      from hadj_le)
  have : ∀ j : Fin r, Module.Finite K (Q j) := hQ_fin
  have hfin_M : Module.finrank K M = ∑ j : Fin r, Module.finrank K (Q j) := by
    have h1 : Module.finrank K M = Module.finrank K Ma := (Module.AEval'.of a).finrank_eq
    have h2 : Module.finrank K Ma = Module.finrank K (⨁ j : Fin r, Q j) :=
      (eM.restrictScalars K).finrank_eq
    rw [h1, h2, Module.finrank_directSum]
  omega

private lemma finrank_pi_eq_sum {K : Type*} [Field K] {I : Type*} [Fintype I]
    (V : I → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module.Finite K (V i)] :
    Module.finrank K (∀ i, V i) = ∑ i, Module.finrank K (V i) := by
  have : ∀ i, Module.Free K (V i) := fun i => Module.Free.of_divisionRing K (V i)
  exact Module.finrank_pi_fintype K

private lemma finrank_adjoin_end_le
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (a b : Module.End K M) (hab : Commute a b) :
    Module.finrank K (Algebra.adjoin K ({a, b} : Set (Module.End K M))) ≤ Module.finrank K M := by
  let Ma := Module.AEval' a
  have hMa_tor : Module.IsTorsion K[X] Ma := by
    intro x
    have hint : IsIntegral K a := Algebra.IsIntegral.isIntegral a
    have hne : minpoly K a ≠ 0 := minpoly.ne_zero hint
    refine ⟨⟨minpoly K a, mem_nonZeroDivisors_of_ne_zero hne⟩, ?_⟩
    apply (Module.AEval'.of a).symm.injective
    change Polynomial.aeval a (minpoly K a) ((Module.AEval'.of a).symm x) = 0
    rw [minpoly.aeval K a]
    rfl
  obtain ⟨I, fI, decI, p, hp, e, hInt⟩ :=
    Submodule.exists_isInternal_prime_power_torsion_of_pid hMa_tor
  let T : I → Submodule K[X] Ma := fun i => Submodule.torsionBy K[X] Ma (p i ^ e i)
  let W : I → Submodule K M := fun i =>
    ((T i).restrictScalars K).comap (Module.AEval'.of a).toLinearMap
  have hmem_W : ∀ (i : I) (m : M), m ∈ W i ↔ Polynomial.aeval a (p i ^ e i) m = 0 := by
    intro i m
    change p i ^ e i • Module.AEval'.of a m = 0 ↔ _
    constructor
    · intro h
      have := congrArg (Module.AEval'.of a).symm h
      simpa using this
    · intro h
      apply (Module.AEval'.of a).symm.injective
      simpa using h
  have hW_comm_inv : ∀ (i : I) (f : Module.End K M), Commute a f → ∀ m ∈ W i, f m ∈ W i := by
    intro i f haf m hm
    rw [hmem_W] at hm ⊢
    have hcf : Commute (Polynomial.aeval a (p i ^ e i)) f := aeval_commute haf (p i ^ e i)
    have h1 : (Polynomial.aeval a (p i ^ e i) * f) m = (f * Polynomial.aeval a (p i ^ e i)) m :=
      congrArg (fun g => g m) hcf.eq
    change (Polynomial.aeval a (p i ^ e i) * f) m = 0
    rw [h1, Module.End.mul_apply, hm, map_zero]
  have ha_inv : ∀ i : I, ∀ m ∈ W i, a m ∈ W i := fun i => hW_comm_inv i a (Commute.refl a)
  have hb_inv : ∀ i : I, ∀ m ∈ W i, b m ∈ W i := fun i => hW_comm_inv i b hab
  let ai : ∀ i : I, Module.End K (W i) := fun i => a.restrict (ha_inv i)
  let bi : ∀ i : I, Module.End K (W i) := fun i => b.restrict (hb_inv i)
  have hab_i : ∀ i : I, Commute (ai i) (bi i) := fun i => by
    ext ⟨m, hm⟩
    exact congrArg (fun f : Module.End K M => f m) hab.eq
  -- Bound on each primary component `W i`
  have hcomp_bound : ∀ i : I,
      Module.finrank K (Algebra.adjoin K ({ai i, bi i} : Set (Module.End K (W i)))) ≤
        Module.finrank K (W i) := by
    intro i
    have hTi_tor : Module.IsTorsion' (T i) (Submonoid.powers (p i)) := fun x =>
      ⟨⟨p i ^ e i, ⟨e i, rfl⟩⟩, Submodule.smul_torsionBy (p i ^ e i) x⟩
    have : Module.Finite K[X] (T i) := by
      have : Module.Finite K (T i) :=
        Module.Finite.of_injective ((T i).restrictScalars K).subtype Subtype.val_injective
      exact Module.Finite.of_restrictScalars_finite K K[X] (T i)
    obtain ⟨d, k, ⟨eTi⟩⟩ := Module.torsion_by_prime_power_decomposition (hp i) hTi_tor
    -- Sort exponents `k` in decreasing order
    let σ : Equiv.Perm (Fin d) := Tuple.sort (OrderDual.toDual ∘ k)
    let k' : Fin d → ℕ := k ∘ σ
    have hk'_anti : Antitone k' := fun x y hxy => Tuple.monotone_sort (OrderDual.toDual ∘ k) hxy
    let ePerm : (⨁ j : Fin d, K[X] ⧸ (K[X] ∙ p i ^ k j)) ≃ₗ[K[X]]
        (⨁ j : Fin d, K[X] ⧸ (K[X] ∙ p i ^ k' j)) :=
      DirectSum.lequivCongrLeft K[X] σ.symm
    let eWT : W i ≃ₗ[K] T i :=
      { toFun := fun x => ⟨Module.AEval'.of a x.1, x.2⟩
        invFun := fun y => ⟨(Module.AEval'.of a).symm y.1, by
          change Module.AEval'.of a ((Module.AEval'.of a).symm y.1) ∈ T i
          simp [y.2]⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let eWi : Module.AEval' (ai i) ≃ₗ[K[X]] T i :=
      LinearEquiv.ofAEval (ai i) eWT fun x => by
        apply Subtype.ext
        change Module.AEval'.of a (a x.1) = (X : K[X]) • Module.AEval'.of a x.1
        rw [Module.AEval'.X_smul_of]
    exact finrank_adjoin_le_of_equiv_directSum_pow (ai i) (bi i) (hab_i i)
      (p i) d k' hk'_anti ((eWi.trans eTi).trans ePerm)
  -- Every element of `Algebra.adjoin K {a, b}` commutes with `a`, hence preserves each `W i`
  have hadj_comm : ∀ T ∈ Algebra.adjoin K ({a, b} : Set (Module.End K M)), Commute a T := by
    intro f hf
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hf
    · rintro x (hx | hx)
      · rw [hx]
      · rw [hx]; exact hab
    · intro c
      exact (Algebra.commutes c a).symm
    · intro x y _ _ hx hy
      exact hx.add_right hy
    · intro x y _ _ hx hy
      exact hx.mul_right hy
  have hadj_restrict : ∀ (i : I) (f : Module.End K M)
      (hf : f ∈ Algebra.adjoin K ({a, b} : Set (Module.End K M))),
      f.restrict (hW_comm_inv i f (hadj_comm f hf)) ∈
        Algebra.adjoin K ({ai i, bi i} : Set (Module.End K (W i))) := by
    intro i f hf
    refine Algebra.adjoin_induction
      (p := fun g hg => g.restrict (hW_comm_inv i g (hadj_comm g hg)) ∈
        Algebra.adjoin K ({ai i, bi i} : Set (Module.End K (W i)))) ?_ ?_ ?_ ?_ hf
    · rintro x (hx | hx)
      · subst hx
        exact Algebra.subset_adjoin (Set.mem_insert _ _)
      · subst hx
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · intro c
      have heq : (algebraMap K (Module.End K M) c).restrict
          (hW_comm_inv i _ (hadj_comm _ (algebraMap_mem _ c))) =
          algebraMap K (Module.End K (W i)) c := by
        ext ⟨m, hm⟩
        simp [Algebra.algebraMap_eq_smul_one]
      rw [heq]
      exact algebraMap_mem _ c
    · intro x y hx hy ihx ihy
      have heq : (x + y).restrict (hW_comm_inv i _ (hadj_comm _ (add_mem hx hy))) =
          x.restrict (hW_comm_inv i x (hadj_comm x hx)) +
            y.restrict (hW_comm_inv i y (hadj_comm y hy)) := by
        ext ⟨m, hm⟩; rfl
      rw [heq]
      exact add_mem ihx ihy
    · intro x y hx hy ihx ihy
      have heq : (x * y).restrict (hW_comm_inv i _ (hadj_comm _ (mul_mem hx hy))) =
          x.restrict (hW_comm_inv i x (hadj_comm x hx)) *
            y.restrict (hW_comm_inv i y (hadj_comm y hy)) := by
        ext ⟨m, hm⟩; rfl
      rw [heq]
      exact mul_mem ihx ihy
  -- Injective `K`-linear restriction map into `∀ i : I, (Algebra.adjoin K {ai i, bi i}).toSubmodule`
  let S : ∀ i : I, Submodule K (Module.End K (W i)) := fun i =>
    (Algebra.adjoin K ({ai i, bi i} : Set (Module.End K (W i)))).toSubmodule
  let Φ : Algebra.adjoin K ({a, b} : Set (Module.End K M)) →ₗ[K] ∀ i : I, S i :=
    { toFun := fun f i =>
        ⟨f.1.restrict (hW_comm_inv i f.1 (hadj_comm f.1 f.2)), hadj_restrict i f.1 f.2⟩
      map_add' := fun f g => by
        ext i ⟨m, hm⟩; rfl
      map_smul' := fun c f => by
        ext i ⟨m, hm⟩; rfl }
  have hΦ_inj : Function.Injective Φ := by
    intro f g hfg
    apply Subtype.ext
    ext m
    obtain ⟨u, hu⟩ := hInt.2 (Module.AEval'.of a m)
    have hm_eq : m = ∑ i : I, (Module.AEval'.of a).symm ((u i : T i) : Ma) := by
      have h1 : Module.AEval'.of a m = ∑ i : I, ((u i : T i) : Ma) := by
        rw [← hu]
        exact DirectSum.coeLinearMap_eq_dfinsuppSum (fun i => T i) u |>.trans
          (DFinsupp.sum_eq_sum_fintype _ fun _ => rfl)
      have h2 := congrArg (Module.AEval'.of a).symm h1
      simpa [map_sum] using h2
    have hfg_i : ∀ i : I, f.1 ((Module.AEval'.of a).symm ((u i : T i) : Ma)) =
        g.1 ((Module.AEval'.of a).symm ((u i : T i) : Ma)) := by
      intro i
      have hmem : (Module.AEval'.of a).symm ((u i : T i) : Ma) ∈ W i := by
        change Module.AEval'.of a ((Module.AEval'.of a).symm ((u i : T i) : Ma)) ∈ T i
        simp
      exact congrArg (fun h => ((h i).1 ⟨(Module.AEval'.of a).symm ((u i : T i) : Ma), hmem⟩ : M)) hfg
    rw [hm_eq, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => hfg_i i
  have hpi_fin : Module.finrank K (∀ i : I, S i) =
      ∑ i : I, Module.finrank K (S i) :=
    finrank_pi_eq_sum (fun i => S i)
  have hM_fin : Module.finrank K M = ∑ i : I, Module.finrank K (W i) := by
    have h1 : Module.finrank K M = Module.finrank K Ma := (Module.AEval'.of a).finrank_eq
    have h2 : Module.finrank K Ma = Module.finrank K (⨁ i : I, T i) :=
      ((LinearEquiv.ofBijective (DirectSum.coeLinearMap T) hInt).symm.restrictScalars K).finrank_eq
    have : ∀ i : I, Module.Finite K (T i) := fun i =>
      Module.Finite.of_injective ((T i).restrictScalars K).subtype Subtype.val_injective
    have : ∀ i : I, Module.Free K (T i) := fun _ => Module.Free.of_divisionRing K _
    have hTW : ∀ i : I, Module.finrank K (T i) = Module.finrank K (W i) := fun i => by
      let eqTW : T i ≃ₗ[K] W i :=
        { toFun := fun y => ⟨(Module.AEval'.of a).symm y.1, by
            change Module.AEval'.of a ((Module.AEval'.of a).symm y.1) ∈ T i
            simp [y.2]⟩
          invFun := fun x => ⟨Module.AEval'.of a x.1, x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact eqTW.finrank_eq
    rw [h1, h2, Module.finrank_directSum]
    exact Finset.sum_congr rfl fun i _ => hTW i
  calc
    Module.finrank K (Algebra.adjoin K ({a, b} : Set (Module.End K M)))
        ≤ Module.finrank K (∀ i : I, S i) :=
          LinearMap.finrank_le_finrank_of_injective hΦ_inj
    _ = ∑ i : I, Module.finrank K (S i) := hpi_fin
    _ ≤ ∑ i : I, Module.finrank K (W i) := Finset.sum_le_sum fun i _ => hcomp_bound i
    _ = Module.finrank K M := hM_fin.symm

private lemma finrank_adjoin_pair_le_main {K : Type*} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (hAB : Commute A B) :
    Module.finrank K (Algebra.adjoin K {A, B}) ≤ n := by
  let e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) :=
    AlgEquiv.ofLinearEquiv Matrix.toLin' Matrix.toLin'_one Matrix.toLin'_mul
  have hab : Commute (e A) (e B) := hAB.map e
  have hmap : Subalgebra.map e.toAlgHom (Algebra.adjoin K ({A, B} : Set (Matrix (Fin n) (Fin n) K))) =
      Algebra.adjoin K ({e A, e B} : Set (Module.End K (Fin n → K))) := by
    rw [AlgHom.map_adjoin, Set.image_pair]
    rfl
  have hfin_eq : Module.finrank K (Algebra.adjoin K ({A, B} : Set (Matrix (Fin n) (Fin n) K))) =
      Module.finrank K (Algebra.adjoin K ({e A, e B} : Set (Module.End K (Fin n → K)))) := by
    rw [← hmap]
    exact ((Algebra.adjoin K ({A, B} : Set (Matrix (Fin n) (Fin n) K))).equivMapOfInjective
      e.toAlgHom e.injective).toLinearEquiv.finrank_eq
  rw [hfin_eq]
  have hle := finrank_adjoin_end_le (e A) (e B) hab
  simpa [Module.finrank_fin_fun] using hle

end GerstenhaberProof

theorem OMA.solution : type_of% @Gerstenhaber.finrank_adjoin_pair_le :=
  fun A B hAB => GerstenhaberProof.finrank_adjoin_pair_le_main A B hAB
