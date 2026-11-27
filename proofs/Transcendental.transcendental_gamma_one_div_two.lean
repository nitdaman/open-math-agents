import FormalConjectures.Wikipedia.Transcendental
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Transcendence of `Γ(1/2) = √π`

We prove that `Real.Gamma (1 / 2)` is transcendental over `ℚ` by reducing to the transcendence of
`π * i` (Lindemann's theorem) using Mathlib's analytical part of Lindemann–Weierstrass together
with the fundamental theorem of symmetric polynomials and Vieta's formulas.
-/

open Polynomial Complex Finset

namespace OMAGammaHalf

private lemma complex_splits (p : ℂ[X]) : p.Splits := IsAlgClosed.splits p

private lemma card_aroots_int (q : ℤ[X]) : (q.aroots ℂ).card = q.natDegree := by
  have h1 : (q.map (algebraMap ℤ ℂ)).Splits := complex_splits _
  have h2 := h1.natDegree_eq_card_roots
  have hinj : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  rw [Polynomial.natDegree_map_eq_of_injective hinj] at h2
  exact h2.symm

private lemma symmetric_eval_monic_roots_mem_int
    {Q : ℤ[X]} (hQ : Q.Monic)
    {n : ℕ} (r : Fin n → ℂ)
    (hr : (Finset.univ.val.map r) = Q.aroots ℂ)
    (φ : MvPolynomial (Fin n) ℤ) (hφ : φ.IsSymmetric) :
    ∃ z : ℤ, MvPolynomial.aeval r φ = (z : ℂ) := by
  have hn : Q.natDegree = n := by
    have hcard : (Q.aroots ℂ).card = Q.natDegree := card_aroots_int Q
    rw [← hr, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin] at hcard
    exact hcard.symm
  obtain ⟨P, hP⟩ := MvPolynomial.esymmAlgHom_surjective (σ := Fin n) ℤ (n := n) (by simp)
    ⟨φ, (MvPolynomial.mem_symmetricSubalgebra φ).mpr hφ⟩
  have hPval : MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℤ (i + 1)) P = φ := by
    have h := congr_arg Subtype.val hP
    rw [MvPolynomial.esymmAlgHom_apply] at h
    exact h
  let c : Fin n → ℤ := fun i => (-1 : ℤ) ^ ((i : ℕ) + 1) * Q.coeff (n - ((i : ℕ) + 1))
  have hesymm : ∀ i : Fin n,
      MvPolynomial.aeval r (MvPolynomial.esymm (Fin n) ℤ ((i : ℕ) + 1)) = (c i : ℂ) := by
    intro i
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hr]
    set Qc : ℂ[X] := Q.map (algebraMap ℤ ℂ)
    have hQc_monic : Qc.Monic := hQ.map (algebraMap ℤ ℂ)
    have hQc_deg : Qc.natDegree = n := by
      rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hn]
    have hQc_roots : Qc.roots.card = Qc.natDegree := (complex_splits Qc).natDegree_eq_card_roots.symm
    have hle : n - ((i : ℕ) + 1) ≤ Qc.natDegree := by omega
    have hvieta := Polynomial.coeff_eq_esymm_roots_of_card hQc_roots hle
    rw [hQc_monic.leadingCoeff, one_mul, hQc_deg] at hvieta
    have hsub : n - (n - ((i : ℕ) + 1)) = (i : ℕ) + 1 := by omega
    rw [hsub] at hvieta
    have hcoeff : Qc.coeff (n - ((i : ℕ) + 1)) = ((Q.coeff (n - ((i : ℕ) + 1)) : ℤ) : ℂ) := by
      simp [Qc]
    rw [hcoeff] at hvieta
    have hsign : ((-1 : ℂ) ^ ((i : ℕ) + 1)) * ((-1 : ℂ) ^ ((i : ℕ) + 1)) = 1 := by
      rw [← mul_pow]
      simp
    have hres : Qc.roots.esymm ((i : ℕ) + 1) =
        (-1 : ℂ) ^ ((i : ℕ) + 1) * ((Q.coeff (n - ((i : ℕ) + 1)) : ℤ) : ℂ) := by
      calc Qc.roots.esymm ((i : ℕ) + 1)
          = 1 * Qc.roots.esymm ((i : ℕ) + 1) := (one_mul _).symm
        _ = ((-1 : ℂ) ^ ((i : ℕ) + 1) * (-1 : ℂ) ^ ((i : ℕ) + 1)) * Qc.roots.esymm ((i : ℕ) + 1) := by
            rw [hsign]
        _ = (-1 : ℂ) ^ ((i : ℕ) + 1) * ((-1 : ℂ) ^ ((i : ℕ) + 1) * Qc.roots.esymm ((i : ℕ) + 1)) := by
            ring
        _ = (-1 : ℂ) ^ ((i : ℕ) + 1) * ((Q.coeff (n - ((i : ℕ) + 1)) : ℤ) : ℂ) := by
            rw [← hvieta]
    simp only [c, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    exact hres
  refine ⟨MvPolynomial.eval c P, ?_⟩
  rw [← hPval]
  have hcomp : (MvPolynomial.aeval r).comp
      (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℤ ((i : ℕ) + 1))) =
      MvPolynomial.aeval (fun i : Fin n => (c i : ℂ)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hesymm i]
  have h1 := AlgHom.congr_fun hcomp P
  simp only [AlgHom.comp_apply] at h1
  rw [h1]
  have h2 : ∀ R : MvPolynomial (Fin n) ℤ,
      MvPolynomial.aeval (fun i : Fin n => (c i : ℂ)) R =
      ((MvPolynomial.eval c R : ℤ) : ℂ) := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  exact h2 P

private noncomputable def monicScale (f : ℤ[X]) : ℤ[X] :=
  if f.natDegree = 0 then 1
  else
    X ^ f.natDegree +
      ∑ i ∈ Finset.range f.natDegree,
        C (f.leadingCoeff ^ (f.natDegree - 1 - i) * f.coeff i) * X ^ i

private lemma monicScale_monic (f : ℤ[X]) : (monicScale f).Monic := by
  unfold monicScale
  split_ifs with h0
  · exact Polynomial.monic_one
  · refine Polynomial.monic_X_pow_add ?_
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (by simp)]
    intro i hi
    rw [Finset.mem_range] at hi
    refine (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact_mod_cast hi

private lemma monicScale_aroots {f : ℤ[X]} (hf : f ≠ 0) :
    (monicScale f).aroots ℂ = (f.aroots ℂ).map (fun r => (f.leadingCoeff : ℂ) * r) := by
  set d := f.natDegree
  set L := f.leadingCoeff
  have hL : (L : ℂ) ≠ 0 := by
    have : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
    exact_mod_cast this
  by_cases hd : d = 0
  · have hd' : f.natDegree = 0 := hd
    have hroots : f.aroots ℂ = 0 := by
      have hcard : (f.aroots ℂ).card = 0 := by rw [card_aroots_int, hd']
      exact Multiset.card_eq_zero.mp hcard
    simp [monicScale, hd', hroots]
  · set fc : ℂ[X] := f.map (algebraMap ℤ ℂ)
    set Qc : ℂ[X] := (monicScale f).map (algebraMap ℤ ℂ)
    have hcomp : Qc.comp (C (L : ℂ) * X) = C ((L : ℂ) ^ (d - 1)) * fc := by
      have hd' : f.natDegree ≠ 0 := hd
      have hQc_def : Qc = X ^ d +
          ∑ i ∈ Finset.range d, C ((L : ℂ) ^ (d - 1 - i) * (f.coeff i : ℂ)) * X ^ i := by
        unfold Qc monicScale
        rw [if_neg hd']
        simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
          Polynomial.map_mul, Polynomial.map_C, map_mul, map_pow]
        rfl
      rw [hQc_def]
      simp only [Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp,
        Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp]
      have hfc : fc = C (L : ℂ) * X ^ d + ∑ i ∈ Finset.range d, C (f.coeff i : ℂ) * X ^ i := by
        have hsum := Polynomial.as_sum_range' fc (d + 1) (by
          rw [Polynomial.natDegree_map_eq_of_injective (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective)]
          omega)
        simp only [← Polynomial.C_mul_X_pow_eq_monomial] at hsum
        rw [Finset.sum_range_succ, add_comm] at hsum
        have htop : fc.coeff d = (L : ℂ) := by
          rw [Polynomial.coeff_map]
          rfl
        rw [htop] at hsum
        have hlow : ∑ i ∈ Finset.range d, C (fc.coeff i) * X ^ i =
            ∑ i ∈ Finset.range d, C (f.coeff i : ℂ) * X ^ i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Polynomial.coeff_map]
          rfl
        rw [← hlow]
        exact hsum
      rw [hfc, mul_add, Finset.mul_sum]
      congr 1
      · rw [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, ← pow_succ]
        have : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.pos_of_ne_zero hd)
        rw [this]
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [mul_pow, ← C_pow]
        have hexp : d - 1 - i + i = d - 1 := Nat.sub_add_cancel (by omega)
        rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
        congr 2
        calc (L : ℂ) ^ (d - 1 - i) * (f.coeff i : ℂ) * (L : ℂ) ^ i
            = ((L : ℂ) ^ (d - 1 - i) * (L : ℂ) ^ i) * (f.coeff i : ℂ) := by ring
          _ = (L : ℂ) ^ (d - 1 - i + i) * (f.coeff i : ℂ) := by rw [← pow_add]
          _ = (L : ℂ) ^ (d - 1) * (f.coeff i : ℂ) := by rw [hexp]
    have hfc_prod : fc = C (L : ℂ) * ((f.aroots ℂ).map (fun r => X - C r)).prod := by
      have hcard : fc.roots.card = fc.natDegree := (complex_splits fc).natDegree_eq_card_roots.symm
      have hlead : fc.leadingCoeff = (L : ℂ) := by
        exact Polynomial.leadingCoeff_map_of_injective
          (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective) f
      have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
      rw [hlead] at h
      exact h.symm
    have hprod_eq : Qc.comp (C (L : ℂ) * X) =
        (((f.aroots ℂ).map (fun r => X - C ((L : ℂ) * r))).prod).comp (C (L : ℂ) * X) := by
      rw [hcomp, hfc_prod, ← mul_assoc, ← C_mul, ← pow_succ]
      have hd1 : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.pos_of_ne_zero hd)
      rw [hd1]
      have hcard : (f.aroots ℂ).card = d := card_aroots_int f
      rw [Polynomial.multiset_prod_comp]
      simp only [Multiset.map_map, Function.comp_def, Polynomial.sub_comp, Polynomial.X_comp,
        Polynomial.C_comp]
      have hfact : ∀ r : ℂ, C (L : ℂ) * X - C ((L : ℂ) * r) = C (L : ℂ) * (X - C r) := by
        intro r; rw [map_mul, mul_sub]
      simp_rw [hfact]
      rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard, C_pow]
    have hQc_eq : Qc = ((f.aroots ℂ).map (fun r => X - C ((L : ℂ) * r))).prod := by
      have h := congr_arg (fun p => p.comp (C ((L : ℂ)⁻¹) * X)) hprod_eq
      simp only [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp] at h
      have hinv : C (L : ℂ) * (C ((L : ℂ)⁻¹) * X) = X := by
        rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hL, map_one, one_mul]
      rw [hinv, Polynomial.comp_X, Polynomial.comp_X] at h
      exact h
    change Qc.roots = _
    rw [hQc_eq]
    have hmap : ((f.aroots ℂ).map (fun r => X - C ((L : ℂ) * r))) =
        (((f.aroots ℂ).map (fun r => (L : ℂ) * r)).map (fun a => X - C a)) := by
      rw [Multiset.map_map]; rfl
    rw [hmap, Polynomial.roots_multiset_prod_X_sub_C]

private lemma exists_fin_indexing (s : Multiset ℂ) :
    ∃ r : Fin s.card → ℂ, Finset.univ.val.map r = s := by
  let l := s.toList
  have hl : l.length = s.card := Multiset.length_toList s
  refine ⟨fun i => l.get (i.cast hl.symm), ?_⟩
  have huniv : (Finset.univ : Finset (Fin s.card)).val = (List.finRange s.card : Multiset (Fin s.card)) := by
    rfl
  rw [huniv, Multiset.map_coe]
  have hlist : (List.finRange s.card).map (fun i : Fin s.card => l.get (i.cast hl.symm)) = l := by
    apply List.ext_get (by simp [hl])
    intro i hi1 hi2
    simp
  rw [hlist, Multiset.coe_toList]

private lemma sum_aeval_roots_mul_leadingCoeff_pow_mem_int
    {f : ℤ[X]} (hf : f ≠ 0) (g : ℤ[X]) {K : ℕ} (hK : g.natDegree ≤ K) :
    ∃ z : ℤ, ((f.leadingCoeff : ℂ) ^ K) * ((f.aroots ℂ).map (fun r => Polynomial.aeval r g)).sum =
      (z : ℂ) := by
  set L := f.leadingCoeff
  set n := (f.aroots ℂ).card
  obtain ⟨r, hr⟩ := exists_fin_indexing (f.aroots ℂ)
  have hQ_monic : (monicScale f).Monic := monicScale_monic f
  have hQ_roots : Finset.univ.val.map (fun i : Fin n => (L : ℂ) * r i) = (monicScale f).aroots ℂ := by
    rw [monicScale_aroots hf, ← hr, Multiset.map_map]
    rfl
  have hpow_int : ∀ k : ℕ, ∃ z : ℤ, (∑ i : Fin n, ((L : ℂ) * r i) ^ k) = (z : ℂ) := by
    intro k
    obtain ⟨z, hz⟩ := symmetric_eval_monic_roots_mem_int hQ_monic
      (fun i : Fin n => (L : ℂ) * r i) hQ_roots (MvPolynomial.psum (Fin n) ℤ k)
      (MvPolynomial.psum_isSymmetric (Fin n) ℤ k)
    refine ⟨z, ?_⟩
    rw [← hz]
    simp [MvPolynomial.psum, map_sum, map_pow]
  choose z_pow hz_pow using hpow_int
  refine ⟨∑ k ∈ Finset.range (K + 1), g.coeff k * L ^ (K - k) * z_pow k, ?_⟩
  have hsum_r : ((f.aroots ℂ).map (fun r => Polynomial.aeval r g)).sum =
      ∑ i : Fin n, Polynomial.aeval (r i) g := by
    rw [← hr, Multiset.map_map]
    rfl
  rw [hsum_r]
  have haeval_sum : ∀ x : ℂ, Polynomial.aeval x g =
      ∑ k ∈ Finset.range (K + 1), (g.coeff k : ℂ) * x ^ k := by
    intro x
    rw [Polynomial.aeval_eq_sum_range' (by omega : g.natDegree < K + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  simp_rw [haeval_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [← hz_pow k, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow]
  have hexp : K - k + k = K := Nat.sub_add_cancel (by omega)
  calc (L : ℂ) ^ K * ((g.coeff k : ℂ) * r i ^ k)
      = (g.coeff k : ℂ) * ((L : ℂ) ^ (K - k + k) * r i ^ k) := by rw [hexp]; ring
    _ = (g.coeff k : ℂ) * (L : ℂ) ^ (K - k) * ((L : ℂ) ^ k * r i ^ k) := by rw [pow_add]; ring

private lemma exists_subset_sum_poly {q : ℤ[X]} (hq : q ≠ 0)
    (hroot : Polynomial.aeval (Real.pi * Complex.I) q = 0) :
    ∃ (f : ℤ[X]) (M : ℕ), 0 < M ∧ f.eval 0 ≠ 0 ∧ f ≠ 0 ∧
      (M : ℂ) + ((f.aroots ℂ).map Complex.exp).sum = 0 := by
  set a := q.leadingCoeff
  have ha_ne : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have ha_ne_c : (a : ℂ) ≠ 0 := by exact_mod_cast ha_ne
  set n := (q.aroots ℂ).card
  obtain ⟨α, hα⟩ := exists_fin_indexing (q.aroots ℂ)
  have hQ_monic : (monicScale q).Monic := monicScale_monic q
  let γ : Fin n → ℂ := fun j => (a : ℂ) * α j
  have hQ_roots : Finset.univ.val.map γ = (monicScale q).aroots ℂ := by
    rw [monicScale_aroots hq, ← hα, Multiset.map_map]
    rfl
  -- Define Phi(T) = ∏_{S : Finset (Fin n)} (T - C (∑ j ∈ S, X j)) over MvPolynomial (Fin n) ℤ
  let Φ : (MvPolynomial (Fin n) ℤ)[X] :=
    ∏ S : Finset (Fin n), (X - C (∑ j ∈ S, MvPolynomial.X j))
  have hΦ_symm : ∀ k : ℕ, (Φ.coeff k).IsSymmetric := by
    intro k σ
    have hmap : Φ.map (MvPolynomial.rename σ).toRingHom = Φ := by
      unfold Φ
      rw [Polynomial.map_prod]
      refine Finset.prod_equiv (Equiv.finsetCongr σ) (by simp) ?_
      intro S _
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      congr 2
      simp [Equiv.finsetCongr_apply, Finset.sum_map]
    have hcoeff := congr_arg (fun p => p.coeff k) hmap
    rw [Polynomial.coeff_map] at hcoeff
    exact hcoeff
  have hΦ_deg : Φ.natDegree ≤ Fintype.card (Finset (Fin n)) := by
    have h1 := Polynomial.natDegree_prod_le (s := (Finset.univ : Finset (Finset (Fin n))))
      (f := fun S : Finset (Fin n) => (X - C (∑ j ∈ S, MvPolynomial.X j) : (MvPolynomial (Fin n) ℤ)[X]))
    calc Φ.natDegree
        ≤ ∑ S : Finset (Fin n), (X - C (∑ j ∈ S, MvPolynomial.X j) : (MvPolynomial (Fin n) ℤ)[X]).natDegree := h1
      _ = ∑ _S : Finset (Fin n), 1 := by
          refine Finset.sum_congr rfl fun S _ => Polynomial.natDegree_X_sub_C _
      _ = Fintype.card (Finset (Fin n)) := by simp
  have hcoeff_int : ∀ k : ℕ, ∃ c : ℤ, MvPolynomial.aeval γ (Φ.coeff k) = (c : ℂ) :=
    fun k => symmetric_eval_monic_roots_mem_int hQ_monic γ hQ_roots (Φ.coeff k) (hΦ_symm k)
  choose c hc using hcoeff_int
  let N := Fintype.card (Finset (Fin n))
  let F₀ : ℤ[X] := ∑ k ∈ Finset.range (N + 1), C (c k) * X ^ k
  have hF₀_map : F₀.map (algebraMap ℤ ℂ) = ∏ S : Finset (Fin n), (X - C (∑ j ∈ S, γ j)) := by
    have h1 : Φ.map (MvPolynomial.aeval γ).toRingHom =
        ∏ S : Finset (Fin n), (X - C (∑ j ∈ S, γ j)) := by
      unfold Φ
      rw [Polynomial.map_prod]
      refine Finset.prod_congr rfl fun S _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      simp [map_sum]
    rw [← h1]
    ext k
    simp only [F₀, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    by_cases hk : k < N + 1
    · rw [Finset.sum_eq_single k]
      · simp [hc k]
      · intro b _ hbk; simp [hbk.symm]
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    · rw [Finset.sum_eq_zero]
      · have hzero : Φ.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hzero]
      · intro b hb; rw [Finset.mem_range] at hb; simp [show k ≠ b by omega]
  let F : ℤ[X] := F₀.comp (C a * X)
  have hF_map : F.map (algebraMap ℤ ℂ) =
      C ((a : ℂ) ^ N) * ∏ S : Finset (Fin n), (X - C (∑ j ∈ S, α j)) := by
    have hcomp : F.map (algebraMap ℤ ℂ) = (F₀.map (algebraMap ℤ ℂ)).comp (C (a : ℂ) * X) := by
      simp [F, Polynomial.map_comp]
    rw [hcomp, hF₀_map, Polynomial.prod_comp]
    have hterm : ∀ S : Finset (Fin n),
        (X - C (∑ j ∈ S, γ j)).comp (C (a : ℂ) * X) = C (a : ℂ) * (X - C (∑ j ∈ S, α j)) := by
      intro S
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
      simp only [γ, ← Finset.mul_sum, map_mul, mul_sub]
    simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, C_pow]
    rfl
  -- Split the product over S into S with sum = 0 and S with sum ≠ 0
  let S0 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => ∑ j ∈ S, α j = 0)
  let S1 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => ∑ j ∈ S, α j ≠ 0)
  let M : ℕ := S0.card
  have hM_pos : 0 < M := Finset.card_pos.mpr ⟨∅, by simp [S0]⟩
  have hsplit : (∏ S : Finset (Fin n), (X - C (∑ j ∈ S, α j))) =
      X ^ M * ∏ S ∈ S1, (X - C (∑ j ∈ S, α j)) := by
    have hpart := (Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
      (p := fun S : Finset (Fin n) => ∑ j ∈ S, α j = 0)
      (f := fun S => (X - C (∑ j ∈ S, α j)))).symm
    rw [hpart]
    congr 1
    calc (∏ S ∈ S0, (X - C (∑ j ∈ S, α j)))
        = ∏ _S ∈ S0, (X : ℂ[X]) := by
            refine Finset.prod_congr rfl fun S hS => ?_
            simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hS
            simp [hS]
      _ = X ^ M := by rw [Finset.prod_const]
  have hF_map2 : F.map (algebraMap ℤ ℂ) =
      X ^ M * (C ((a : ℂ) ^ N) * ∏ S ∈ S1, (X - C (∑ j ∈ S, α j))) := by
    rw [hF_map, hsplit]; ring
  -- Since X ^ M divides F.map _, all coefficients of F below M are 0, so X ^ M ∣ F in ℤ[X]
  have hXM_dvd : X ^ M ∣ F := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have h0 : (F.map (algebraMap ℤ ℂ)).coeff d = 0 := by
      rw [hF_map2, Polynomial.coeff_X_pow_mul']
      simp [hd]
    rw [Polynomial.coeff_map] at h0
    exact Int.cast_eq_zero.mp h0
  obtain ⟨f, hf_eq⟩ := hXM_dvd
  have hf_map : f.map (algebraMap ℤ ℂ) =
      C ((a : ℂ) ^ N) * ∏ S ∈ S1, (X - C (∑ j ∈ S, α j)) := by
    have h1 : (X : ℂ[X]) ^ M * f.map (algebraMap ℤ ℂ) =
        (X : ℂ[X]) ^ M * (C ((a : ℂ) ^ N) * ∏ S ∈ S1, (X - C (∑ j ∈ S, α j))) := by
      rw [← hF_map2, hf_eq, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    exact mul_left_cancel₀ (pow_ne_zero M Polynomial.X_ne_zero) h1
  have hf_eval0 : f.eval 0 ≠ 0 := by
    intro h0
    have hc0 : (f.map (algebraMap ℤ ℂ)).eval 0 = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_zero]
      have : f.coeff 0 = 0 := by rw [Polynomial.coeff_zero_eq_eval_zero, h0]
      simp [this]
    rw [hf_map, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hc0
    rcases mul_eq_zero.mp hc0 with ha0 | hprod0
    · exact pow_ne_zero N ha_ne_c ha0
    · rw [Finset.prod_eq_zero_iff] at hprod0
      obtain ⟨S, hS, hS0⟩ := hprod0
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub,
        neg_eq_zero] at hS0
      exact hS hS0
  have hf_ne : f ≠ 0 := by
    intro h0; subst h0; simp at hf_eval0
  have hf_aroots : f.aroots ℂ = S1.val.map (fun S => ∑ j ∈ S, α j) := by
    change (f.map (algebraMap ℤ ℂ)).roots = _
    rw [hf_map, Polynomial.roots_C_mul _ (pow_ne_zero N ha_ne_c)]
    have hprod : (∏ S ∈ S1, (X - C (∑ j ∈ S, α j))) =
        ((S1.val.map (fun S => ∑ j ∈ S, α j)).map (fun z => X - C z)).prod := by
      rw [Multiset.map_map]; rfl
    rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]
  -- Now prove (M : ℂ) + ∑_{r ∈ f.aroots ℂ} exp r = 0
  have hpi_root : Real.pi * Complex.I ∈ q.aroots ℂ := by
    rw [Polynomial.mem_roots ((Polynomial.map_ne_zero_iff
      (show Function.Injective (algebraMap ℤ ℂ) from Int.cast_injective)).mpr hq)]
    simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hroot
  rw [← hα, Multiset.mem_map] at hpi_root
  obtain ⟨i0, _, hi0⟩ := hpi_root
  have hprod_zero : (∏ j : Fin n, (Complex.exp (α j) + 1)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
    rw [hi0, Complex.exp_pi_mul_I]
    ring
  have hexpand : (∏ j : Fin n, (Complex.exp (α j) + 1)) =
      ∑ S : Finset (Fin n), Complex.exp (∑ j ∈ S, α j) := by
    rw [Finset.prod_add]
    have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
      ext S; simp
    rw [hpow]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.prod_const_one, mul_one, Complex.exp_sum]
  have hsum_zero : (∑ S : Finset (Fin n), Complex.exp (∑ j ∈ S, α j)) = 0 :=
    hexpand.symm.trans hprod_zero
  have hsum_split : (∑ S : Finset (Fin n), Complex.exp (∑ j ∈ S, α j)) =
      (M : ℂ) + ((f.aroots ℂ).map Complex.exp).sum := by
    have hpart := (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun S : Finset (Fin n) => ∑ j ∈ S, α j = 0)
      (f := fun S => Complex.exp (∑ j ∈ S, α j))).symm
    rw [hpart]
    congr 1
    · calc (∑ S ∈ S0, Complex.exp (∑ j ∈ S, α j))
          = ∑ _S ∈ S0, (1 : ℂ) := by
              refine Finset.sum_congr rfl fun S hS => ?_
              simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hS
              rw [hS, Complex.exp_zero]
        _ = (M : ℂ) := by simp [M]
    · rw [hf_aroots, Multiset.map_map]
      rfl
  exact ⟨f, M, hM_pos, hf_eval0, hf_ne, hsum_split.symm.trans hsum_zero⟩

private lemma not_isAlgebraic_int_pi_mul_I : ¬ ∃ q : ℤ[X], q ≠ 0 ∧
    Polynomial.aeval (Real.pi * Complex.I) q = 0 := by
  rintro ⟨q, hq, hroot⟩
  obtain ⟨f, M, hM_pos, hf0, hf_ne, hsum_exp⟩ := exists_subset_sum_poly hq hroot
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  set L : ℤ := f.leadingCoeff
  have hL_ne : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf_ne
  set D : ℕ := f.natDegree
  set m : ℕ := (f.aroots ℂ).card
  set B : ℝ := max |c| 1
  have hB_ge1 : 1 ≤ B := le_max_right _ _
  have hB_nonneg : 0 ≤ B := by positivity
  set C0 : ℝ := ((L.natAbs : ℝ) ^ D) * B
  have hC0_nonneg : 0 ≤ C0 := by positivity
  -- Choose a sufficiently large prime p
  have htend : Filter.Tendsto (fun k : ℕ => ((m : ℝ) * C0) * (C0 ^ k / (k.factorial : ℝ)))
      Filter.atTop (nhds (((m : ℝ) * C0) * 0)) :=
    (Real.summable_pow_div_factorial C0).tendsto_atTop_zero.const_mul _
  rw [mul_zero] at htend
  have hev : ∀ᶠ k : ℕ in Filter.atTop, ((m : ℝ) * C0) * (C0 ^ k / (k.factorial : ℝ)) < 1 :=
    htend.eventually (gt_mem_nhds zero_lt_one)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K0, hK0⟩ := hev
  let bound : ℕ := max (K0 + 1) (max (f.eval 0).natAbs (max M L.natAbs) + 1)
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes bound
  have hp_gt_f0 : p > (f.eval 0).natAbs := by omega
  have hp_gt_M : p > M := by omega
  have hp_gt_L : p > L.natAbs := by omega
  have hp_ge_K0 : K0 ≤ p - 1 := by omega
  have hsmall : (m : ℝ) * C0 ^ p / ((p - 1).factorial : ℝ) < 1 := by
    have h := hK0 (p - 1) hp_ge_K0
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_prime.pos
    calc (m : ℝ) * C0 ^ p / ((p - 1).factorial : ℝ)
        = (m : ℝ) * C0 ^ (p - 1 + 1) / ((p - 1).factorial : ℝ) := by rw [hp1]
      _ = ((m : ℝ) * C0) * (C0 ^ (p - 1) / ((p - 1).factorial : ℝ)) := by rw [pow_succ]; ring
      _ < 1 := h
  obtain ⟨np, hnp_ndvd, gp, hgp_deg, happrox⟩ := hc p hp_gt_f0 hp_prime
  have hgp_le : gp.natDegree ≤ p * D := hgp_deg.trans (Nat.sub_le _ _)
  obtain ⟨Z, hZ⟩ := sum_aeval_roots_mul_leadingCoeff_pow_mem_int hf_ne gp hgp_le
  -- Define integer N = - L^(p*D) * np * M - p * Z
  let N : ℤ := -(L ^ (p * D) * np * (M : ℤ)) - (p : ℤ) * Z
  -- 1. Show p does not divide N, hence N ≠ 0
  have hN_ne : N ≠ 0 := by
    intro hN0
    have hp_dvd_prod : (p : ℤ) ∣ L ^ (p * D) * np * (M : ℤ) := ⟨-Z, by linarith⟩
    have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
    rcases hp_int.dvd_or_dvd hp_dvd_prod with h1 | hpM
    · rcases hp_int.dvd_or_dvd h1 with hpLpow | hpnp
      · have hpL : (p : ℤ) ∣ L := hp_int.dvd_of_dvd_pow hpLpow
        have hnat : p ∣ L.natAbs := Int.natCast_dvd.mp hpL
        have hpos : 0 < L.natAbs := Int.natAbs_pos.mpr hL_ne
        have hle := Nat.le_of_dvd hpos hnat
        omega
      · exact hnp_ndvd hpnp
    · have hnat : p ∣ M := Int.ofNat_dvd.mp hpM
      have hle := Nat.le_of_dvd hM_pos hnat
      omega
  obtain ⟨r_fin, hr_fin⟩ := exists_fin_indexing (f.aroots ℂ)
  -- 2. Show (N : ℂ) = L^(p*D) * ∑_{i : Fin m} (np * exp (r_fin i) - p * aeval (r_fin i) gp)
  have hN_eq : (N : ℂ) = ((L : ℂ) ^ (p * D)) *
      ∑ i : Fin m, ((np : ℂ) * Complex.exp (r_fin i) - (p : ℂ) * Polynomial.aeval (r_fin i) gp) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, mul_sub]
    have hexp_sum : (∑ i : Fin m, Complex.exp (r_fin i)) = ((f.aroots ℂ).map Complex.exp).sum := by
      rw [← hr_fin, Multiset.map_map]; rfl
    have hgp_sum : (∑ i : Fin m, Polynomial.aeval (r_fin i) gp) =
        ((f.aroots ℂ).map (fun r => Polynomial.aeval r gp)).sum := by
      rw [← hr_fin, Multiset.map_map]; rfl
    rw [hexp_sum, hgp_sum]
    have hexp_eq : ((f.aroots ℂ).map Complex.exp).sum = -(M : ℂ) := by
      linear_combination hsum_exp
    rw [hexp_eq]
    have hZterm : (L : ℂ) ^ (p * D) * ((p : ℂ) * ((f.aroots ℂ).map (fun r => Polynomial.aeval r gp)).sum) =
        (p : ℂ) * (Z : ℂ) := by
      rw [← hZ]; ring
    rw [hZterm]
    simp only [N, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    ring
  -- 3. Bound ‖(N : ℂ)‖ < 1
  have hN_lt : ‖(N : ℂ)‖ < 1 := by
    rw [hN_eq, norm_mul, Complex.norm_pow]
    have hLnorm : ‖(L : ℂ)‖ = (L.natAbs : ℝ) := by
      rw [Complex.norm_intCast]
      have h1 : |(L : ℝ)| = ((|L| : ℤ) : ℝ) := by exact_mod_cast rfl
      rw [h1, Int.abs_eq_natAbs, Int.cast_natCast]
    rw [hLnorm]
    have hterm_bound : ∀ i : Fin m,
        ‖(np : ℂ) * Complex.exp (r_fin i) - (p : ℂ) * Polynomial.aeval (r_fin i) gp‖ ≤
          B ^ p / ((p - 1).factorial : ℝ) := by
      intro i
      have hi_mem : r_fin i ∈ f.aroots ℂ := by
        rw [← hr_fin]
        exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)
      have h := happrox hi_mem
      simp only [zsmul_eq_mul, nsmul_eq_mul] at h
      refine h.trans ?_
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc c ^ p ≤ |c ^ p| := le_abs_self _
        _ = |c| ^ p := abs_pow c p
        _ ≤ B ^ p := pow_le_pow_left₀ (abs_nonneg c) (le_max_left _ _) p
    have hsum_norm : ‖∑ i : Fin m, ((np : ℂ) * Complex.exp (r_fin i) -
          (p : ℂ) * Polynomial.aeval (r_fin i) gp)‖ ≤
        (m : ℝ) * (B ^ p / ((p - 1).factorial : ℝ)) := by
      calc ‖∑ i : Fin m, ((np : ℂ) * Complex.exp (r_fin i) -
              (p : ℂ) * Polynomial.aeval (r_fin i) gp)‖
          ≤ ∑ i : Fin m, ‖(np : ℂ) * Complex.exp (r_fin i) -
              (p : ℂ) * Polynomial.aeval (r_fin i) gp‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin m, (B ^ p / ((p - 1).factorial : ℝ)) :=
            Finset.sum_le_sum fun i _ => hterm_bound i
        _ = (m : ℝ) * (B ^ p / ((p - 1).factorial : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    calc (L.natAbs : ℝ) ^ (p * D) * ‖∑ i : Fin m, ((np : ℂ) * Complex.exp (r_fin i) -
            (p : ℂ) * Polynomial.aeval (r_fin i) gp)‖
        ≤ (L.natAbs : ℝ) ^ (p * D) * ((m : ℝ) * (B ^ p / ((p - 1).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum_norm (by positivity)
      _ = (m : ℝ) * C0 ^ p / ((p - 1).factorial : ℝ) := by
          simp only [C0, mul_pow, ← pow_mul, mul_comm D p]
          ring
      _ < 1 := hsmall
  have hN_ge1 : (1 : ℝ) ≤ ‖(N : ℂ)‖ := by
    rw [Complex.norm_intCast]
    have h1 : (1 : ℤ) ≤ |N| := Int.one_le_abs hN_ne
    exact_mod_cast h1
  linarith

private lemma rat_poly_to_int_poly {x : ℂ} (h : IsAlgebraic ℚ x) :
    ∃ q : ℤ[X], q ≠ 0 ∧ Polynomial.aeval x q = 0 := by
  obtain ⟨p, hp_ne, hp_root⟩ := h
  let d : ℕ := ∏ i ∈ p.support, (p.coeff i).den
  have hd_pos : 0 < d := Finset.prod_pos fun i _ => (p.coeff i).pos
  have hd_ne : (d : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  let q : ℤ[X] := ∑ i ∈ p.support, C ((p.coeff i).num * ((d / (p.coeff i).den : ℕ) : ℤ)) * X ^ i
  have hq_map : q.map (algebraMap ℤ ℚ) = C (d : ℚ) * p := by
    ext i
    simp only [q, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hi : i ∈ p.support
    · rw [Finset.sum_eq_single i]
      · simp only [↓reduceIte, mul_one, eq_intCast, Int.cast_mul, Int.cast_natCast]
        have hdvd : (p.coeff i).den ∣ d := Finset.dvd_prod_of_mem _ hi
        have hden_ne : ((p.coeff i).den : ℚ) ≠ 0 := by exact_mod_cast (p.coeff i).pos.ne'
        have hmul : ((d / (p.coeff i).den : ℕ) : ℚ) * ((p.coeff i).den : ℚ) = (d : ℚ) := by
          exact_mod_cast Nat.div_mul_cancel hdvd
        have hrat := Rat.num_div_den (p.coeff i)
        calc ((p.coeff i).num : ℚ) * ((d / (p.coeff i).den : ℕ) : ℚ)
            = (((p.coeff i).num : ℚ) / ((p.coeff i).den : ℚ)) *
                (((d / (p.coeff i).den : ℕ) : ℚ) * ((p.coeff i).den : ℚ)) := by
                field_simp [hden_ne]
          _ = p.coeff i * (d : ℚ) := by rw [hrat, hmul]
          _ = (d : ℚ) * p.coeff i := mul_comm _ _
      · intro b _ hbi; simp [hbi.symm]
      · intro h; exact absurd hi h
    · rw [Finset.sum_eq_zero]
      · have h0 : p.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
        simp [h0]
      · intro b hb; simp [show i ≠ b by intro h; subst h; exact hi hb]
  refine ⟨q, ?_, ?_⟩
  · intro hq0
    rw [hq0, Polynomial.map_zero] at hq_map
    have hmul0 : C (d : ℚ) * p = 0 := hq_map.symm
    rcases mul_eq_zero.mp hmul0 with hC0 | hp0
    · exact hd_ne (Polynomial.C_eq_zero.mp hC0)
    · exact hp_ne hp0
  · have h1 : Polynomial.aeval x q = Polynomial.aeval x (q.map (algebraMap ℤ ℚ)) := by
      rw [Polynomial.aeval_map_algebraMap]
    rw [h1, hq_map, map_mul, hp_root, mul_zero]

end OMAGammaHalf

theorem OMA.solution : type_of% @Transcendental.transcendental_gamma_one_div_two := by
  rw [Real.Gamma_one_half_eq]
  intro halg
  have hpi_alg : IsAlgebraic ℚ Real.pi := by
    have hsq := halg.pow 2
    rwa [Real.sq_sqrt Real.pi_nonneg] at hsq
  have hpi_c : IsAlgebraic ℚ (Real.pi : ℂ) := by
    obtain ⟨p, hp_ne, hp_root⟩ := hpi_alg
    refine ⟨p, hp_ne, ?_⟩
    have h := Polynomial.aeval_algebraMap_apply ℂ Real.pi p
    rw [hp_root, map_zero] at h
    exact h
  have hI_alg : IsAlgebraic ℚ Complex.I := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · intro h0
      have h2 := congr_arg (fun p => p.coeff 2) h0
      simp [Polynomial.coeff_one] at h2
    · simp
  have hpiI : IsAlgebraic ℚ ((Real.pi : ℂ) * Complex.I) := hpi_c.mul hI_alg
  exact OMAGammaHalf.not_isAlgebraic_int_pi_mul_I (OMAGammaHalf.rat_poly_to_int_poly hpiI)
