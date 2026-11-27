import FormalConjectures.Paper.CasasAlvero

/-!
Proof of `CasasAlvero.casas_alvero.prime_power` (Graf von Bothmer, Labs, Schicho,
and van de Woestijne, 2006) via reduction modulo a prime `p` using a valuation subring
dominating `ℤ_{(p)}`.
-/

-- Problem: Casas-Alvero Conjecture — prime power
-- Upstream: formal-conjectures FormalConjectures/Paper/CasasAlvero.lean:135 (declaration CasasAlvero.casas_alvero.prime_power)
-- Credit: @nitdaman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial CasasAlvero

namespace CasasAlveroPrimePower

/-- Existence of a valuation subring of a characteristic-zero field whose residue field
has characteristic `p` (for any prime `p`). -/
private lemma exists_valuationSubring_charP_residueField
    (L : Type*) [Field L] [CharZero L] (p : ℕ) (hp : p.Prime) :
    ∃ V : ValuationSubring L, CharP (IsLocalRing.ResidueField V) p := by
  let f : ℤ →+* L := Int.castRingHom L
  have hf_inj : Function.Injective f := Int.cast_injective
  let A : Subring L := f.range
  let e : ℤ ≃+* A := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf_inj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let P_int : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP_int_prime : P_int.IsPrime := (Ideal.span_singleton_prime hp_int.ne_zero).mpr hp_int
  let P : Ideal A := P_int.map e.toRingHom
  have hP_prime : P.IsPrime := Ideal.map_isPrime_of_equiv e
  let R : LocalSubring L := LocalSubring.ofPrime A P
  obtain ⟨V, hRV⟩ := R.exists_le_valuationSubring
  refine ⟨V, ?_⟩
  have hpA : ((p : ℕ) : A) ∈ P := by
    have hmem : (p : ℤ) ∈ P_int := Ideal.subset_span rfl
    have heq : e (p : ℤ) = ((p : ℕ) : A) := by
      ext
      simp [e, f]
    rw [← heq]
    exact Ideal.mem_map_of_mem e.toRingHom hmem
  have hpR_not_unit : ¬ IsUnit ((p : ℕ) : R.toSubring) := by
    have hmem_max : algebraMap A R.toSubring ((p : ℕ) : A) ∈
        IsLocalRing.maximalIdeal R.toSubring := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P]
      exact Ideal.mem_map_of_mem _ hpA
    have hcast : algebraMap A R.toSubring ((p : ℕ) : A) = ((p : ℕ) : R.toSubring) :=
      map_natCast (algebraMap A R.toSubring) p
    rw [hcast] at hmem_max
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem_max
  have hpV_not_unit : ¬ IsUnit ((p : ℕ) : V) := by
    intro hunit
    have hunit' : IsUnit (Subring.inclusion hRV.1 ((p : ℕ) : R.toSubring)) := by
      rw [map_natCast]
      exact hunit
    exact hpR_not_unit (hRV.2.1 _ hunit')
  have hpV_mem : ((p : ℕ) : V) ∈ IsLocalRing.maximalIdeal V :=
    (IsLocalRing.mem_maximalIdeal _).mpr hpV_not_unit
  have hp_res : ((p : ℕ) : IsLocalRing.ResidueField V) = 0 := by
    rw [← map_natCast (IsLocalRing.residue V) p]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hpV_mem
  have hrc : ringChar (IsLocalRing.ResidueField V) = p :=
    (hp.eq_one_or_self_of_dvd _ (ringChar.dvd hp_res)).resolve_left CharP.ringChar_ne_one
  exact ringChar.of_eq hrc

/-- In a valuation subring of a field, every nonempty finite set of nonzero elements contains
an element `m` such that `x / m ∈ V` for all `x` in the set. -/
private lemma exists_max_in_valuationSubring {L : Type*} [Field L] (V : ValuationSubring L)
    (s : Finset L) (hs : s.Nonempty) (hs0 : ∀ x ∈ s, x ≠ 0) :
    ∃ m ∈ s, ∀ x ∈ s, x / m ∈ V := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert a t ha ih =>
    by_cases ht : t.Nonempty
    · obtain ⟨m, hm_t, hm_max⟩ := ih ht (fun x hx => hs0 x (Finset.mem_insert_of_mem hx))
      have ha0 : a ≠ 0 := hs0 a (Finset.mem_insert_self a t)
      have hm0 : m ≠ 0 := hs0 m (Finset.mem_insert_of_mem hm_t)
      rcases V.2 (a / m) with h | h
      · refine ⟨m, Finset.mem_insert_of_mem hm_t, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hx_t
        · exact h
        · exact hm_max x hx_t
      · have hma : m / a ∈ V := by
          simpa [inv_div] using h
        refine ⟨a, Finset.mem_insert_self a t, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hx_t
        · rw [div_self ha0]; exact V.one_mem
        · have : x / a = (x / m) * (m / a) := by field_simp [hm0, ha0]
          rw [this]
          exact V.toSubring.mul_mem (hm_max x hx_t) hma
    · rw [Finset.not_nonempty_iff_eq_empty] at ht
      subst ht
      refine ⟨a, Finset.mem_singleton_self a, fun x hx => ?_⟩
      rw [Finset.mem_singleton.mp hx, div_self (hs0 a (Finset.mem_singleton_self a))]
      exact V.one_mem

/-- Coefficient formula for `f.comp (C c * X)`. -/
private lemma coeff_comp_C_mul_X {R : Type*} [CommSemiring R] (f : R[X]) (c : R) (i : ℕ) :
    (f.comp (C c * X)).coeff i = c ^ i * f.coeff i := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp [add_comp, coeff_add, hp, hq, mul_add]
  | monomial n a =>
    rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial,
      coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp

/-- Behavior of Hasse derivatives under affine change of variables, evaluated at a point. -/
private lemma eval_hasseDeriv_comp_linear {R : Type*} [CommRing R]
    (P : R[X]) (c a γ : R) (i : ℕ) :
    (hasseDeriv i (P.comp (C c * X + C a))).eval γ =
      c ^ i * (hasseDeriv i P).eval (c * γ + a) := by
  rw [← taylor_coeff, taylor_apply, comp_assoc]
  have hlin : (C c * X + C a).comp (X + C γ) = (X + C (c * γ + a)).comp (C c * X) := by
    simp [add_comp, mul_comp, C_comp, X_comp, mul_add, add_assoc]
  rw [hlin, ← comp_assoc, ← taylor_apply, coeff_comp_C_mul_X, taylor_coeff]

universe u in
/-- Given a monic polynomial `P` over an algebraically closed field `L` of char 0 with
`HasCasasAlveroPropᵣ P` that is NOT a pure power `(X - C α)^d`, and any prime `p`,
there exists a field `k` of characteristic `p` and a monic polynomial `Q : k[X]` of the same
degree with `Q.IsRoot 0`, `Q.IsRoot 1`, and `HasCasasAlveroPropᵣ Q`. -/
private lemma exists_reduction_mod_p
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (P : L[X]) (hP : P.Monic) (hd_pos : 0 < P.natDegree)
    (hca : HasCasasAlveroPropᵣ P)
    (hnot : ¬ ∃ α : L, P = (X - C α) ^ P.natDegree)
    (p : ℕ) (hp : p.Prime) :
    ∃ (k : Type u) (_ : Field k) (_ : CharP k p) (Q : k[X]),
      Q.Monic ∧ Q.natDegree = P.natDegree ∧ Q.IsRoot 0 ∧ Q.IsRoot 1 ∧
      HasCasasAlveroPropᵣ Q := by
  classical
  have hP_ne : P ≠ 0 := hP.ne_zero
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hcard : P.roots.card = P.natDegree := hsplits.natDegree_eq_card_roots.symm
  have hprod : P = (P.roots.map fun r => X - C r).prod := by
    have := hsplits.eq_prod_roots_of_monic hP
    simpa [Multiset.map_id'] using this
  have hroots_nonempty : P.roots ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hcard
    omega
  obtain ⟨a, ha_roots⟩ := Multiset.exists_mem_of_ne_zero hroots_nonempty
  have hex_diff : ∃ b ∈ P.roots, b ≠ a := by
    by_contra hall
    push Not at hall
    apply hnot
    refine ⟨a, ?_⟩
    have hrep : P.roots = Multiset.replicate P.natDegree a := by
      rw [← hcard]
      exact Multiset.eq_replicate_card.mpr hall
    conv_lhs => rw [hprod, hrep, Multiset.map_replicate, Multiset.prod_replicate]
  obtain ⟨b₁, hb₁_roots, hb₁_ne⟩ := hex_diff
  obtain ⟨V, hchar⟩ := exists_valuationSubring_charP_residueField L p hp
  let s : Finset L := (P.roots.toFinset.image (· - a)).erase 0
  have hs_ne : s.Nonempty := by
    refine ⟨b₁ - a, Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hb₁_ne, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨b₁, Multiset.mem_toFinset.mpr hb₁_roots, rfl⟩
  have hs0 : ∀ x ∈ s, x ≠ 0 := fun x hx => (Finset.mem_erase.mp hx).1
  obtain ⟨c, hc_s, hc_max⟩ := exists_max_in_valuationSubring V s hs_ne hs0
  have hc0 : c ≠ 0 := hs0 c hc_s
  have hc_img := (Finset.mem_erase.mp hc_s).2
  obtain ⟨b₀, hb₀_fin, hb₀_eq⟩ := Finset.mem_image.mp hc_img
  have hb₀_roots : b₀ ∈ P.roots := Multiset.mem_toFinset.mp hb₀_fin
  have hroot_mem_V : ∀ r ∈ P.roots, (r - a) / c ∈ V := by
    intro r hr
    by_cases hra : r = a
    · subst hra; simp [V.zero_mem]
    · apply hc_max
      exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hra,
        Finset.mem_image.mpr ⟨r, Multiset.mem_toFinset.mpr hr, rfl⟩⟩
  let fV : {r : L // r ∈ P.roots} → V := fun r => ⟨(r.1 - a) / c, hroot_mem_V r.1 r.2⟩
  let rootsV : Multiset V := P.roots.attach.map fV
  let QV : V[X] := (rootsV.map fun x => X - C x).prod
  have hQV_monic : QV.Monic :=
    monic_multiset_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)
  have hQV_deg : QV.natDegree = P.natDegree := by
    rw [natDegree_multiset_prod_of_monic (rootsV.map fun x => X - C x)
      (by rintro _ h; obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp h; exact monic_X_sub_C x)]
    simp only [Multiset.map_map, Function.comp_def, natDegree_X_sub_C, Multiset.map_const',
      Multiset.sum_replicate, smul_eq_mul, mul_one, rootsV, Multiset.card_attach, hcard]
  have h0_mem : (0 : V) ∈ rootsV := by
    refine Multiset.mem_map.mpr ⟨⟨a, ha_roots⟩, Multiset.mem_attach _ _, ?_⟩
    ext; simp [fV]
  have h1_mem : (1 : V) ∈ rootsV := by
    refine Multiset.mem_map.mpr ⟨⟨b₀, hb₀_roots⟩, Multiset.mem_attach _ _, ?_⟩
    ext; simp [fV, hb₀_eq, div_self hc0]
  have hQV_root : ∀ x ∈ rootsV, QV.IsRoot x := by
    intro x hx
    rw [IsRoot, eval_multiset_prod]
    exact Multiset.prod_eq_zero
      (Multiset.mem_map.mpr ⟨X - C x, Multiset.mem_map.mpr ⟨x, hx, rfl⟩, by simp⟩)
  have hQV_root0 : QV.IsRoot 0 := hQV_root 0 h0_mem
  have hQV_root1 : QV.IsRoot 1 := hQV_root 1 h1_mem
  have hQL_eq : C (c ^ P.natDegree) * QV.map V.subtype = P.comp (C c * X + C a) := by
    have hmap : QV.map V.subtype =
        (P.roots.map fun r => X - C ((r - a) / c)).prod := by
      simp only [QV, rootsV, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def,
        Polynomial.map_sub, map_X, map_C]
      congr 1
      conv_rhs => rw [← Multiset.attach_map_val P.roots]
      rw [Multiset.map_map]
      rfl
    rw [hmap]
    conv_rhs => rw [hprod]
    rw [multiset_prod_comp]
    have hterm : ∀ r : L, (X - C r).comp (C c * X + C a) = C c * (X - C ((r - a) / c)) := by
      intro r
      simp only [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel₀ _ hc0, map_sub]
      ring
    simp only [Multiset.map_map, Function.comp_def, hterm]
    rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← C_pow, hcard]
  have hQV_ca : ∀ i ∈ Finset.range P.natDegree,
      ∃ x : V, QV.IsRoot x ∧ (QV.hasseDeriv i).IsRoot x := by
    intro i hi
    obtain ⟨r, hr_P, hr_deriv⟩ := hca i hi
    have hr_roots : r ∈ P.roots := (mem_roots hP_ne).mpr hr_P
    let x : V := ⟨(r - a) / c, hroot_mem_V r hr_roots⟩
    refine ⟨x, ?_, ?_⟩
    · apply hQV_root
      exact Multiset.mem_map.mpr ⟨⟨r, hr_roots⟩, Multiset.mem_attach _ _, rfl⟩
    · have hval : (x : L) = (r - a) / c := rfl
      have hcxa : c * (x : L) + a = r := by
        rw [hval, mul_div_cancel₀ _ hc0, sub_add_cancel]
      have hderiv_map : (hasseDeriv i (QV.map V.subtype)).eval (x : L) = 0 := by
        have h1 := congrArg (fun f => (hasseDeriv i f).eval (x : L)) hQL_eq
        have hmul_deriv : hasseDeriv i (C (c ^ P.natDegree) * QV.map V.subtype) =
            C (c ^ P.natDegree) * hasseDeriv i (QV.map V.subtype) := by
          rw [← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
        rw [hmul_deriv, eval_mul, eval_C, eval_hasseDeriv_comp_linear, hcxa] at h1
        rw [IsRoot.def.mp hr_deriv, mul_zero] at h1
        exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc0)
      rw [IsRoot.def]
      apply V.subtype_injective
      rw [map_zero, ← eval_map_apply, ← hasseDeriv_map]
      exact hderiv_map
  let π : V →+* IsLocalRing.ResidueField V := IsLocalRing.residue V
  let Q : (IsLocalRing.ResidueField V)[X] := QV.map π
  refine ⟨IsLocalRing.ResidueField V, inferInstance, hchar, Q, ?_, ?_, ?_, ?_, ?_⟩
  · exact hQV_monic.map π
  · rw [hQV_monic.natDegree_map π, hQV_deg]
  · rw [IsRoot.def, ← map_zero π, eval_map_apply, IsRoot.def.mp hQV_root0, map_zero]
  · rw [IsRoot.def, ← map_one π, eval_map_apply, IsRoot.def.mp hQV_root1, map_zero]
  · intro i hi
    rw [hQV_monic.natDegree_map π, hQV_deg] at hi
    obtain ⟨x, hx0, hxi⟩ := hQV_ca i hi
    refine ⟨π x, ?_, ?_⟩
    · rw [IsRoot.def, eval_map_apply, IsRoot.def.mp hx0, map_zero]
    · rw [IsRoot.def, hasseDeriv_map, eval_map_apply, IsRoot.def.mp hxi, map_zero]

/-- In characteristic `p`, no monic polynomial of degree `p^k` can satisfy `HasCasasAlveroPropᵣ`
while having both `0` and `1` as roots. -/
private lemma no_casasAlvero_prime_power_charP
    {k : Type*} [Field k] (p n : ℕ) (hp : p.Prime) [CharP k p]
    (Q : k[X]) (hQ : Q.Monic) (hd : Q.natDegree = p ^ n)
    (h0 : Q.IsRoot 0) (h1 : Q.IsRoot 1) (hca : HasCasasAlveroPropᵣ Q) : False := by
  have hcoeff_zero : ∀ d : ℕ, ∀ j : ℕ, d = p ^ n - j → 1 ≤ j → j < p ^ n → Q.coeff j = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hd_eq hj1 hj_lt
      have hhasse : Q.hasseDeriv j = C (Q.coeff j) := by
        ext m
        rw [hasseDeriv_coeff, coeff_C]
        by_cases hm : m = 0
        · subst hm; simp
        · rw [if_neg hm]
          rcases lt_trichotomy (m + j) (p ^ n) with hlt | heq | hgt
          · have hih : Q.coeff (m + j) = 0 :=
              ih (p ^ n - (m + j)) (by omega) (m + j) rfl (by omega) hlt
            rw [hih, mul_zero]
          · rw [heq]
            have hdvd : p ∣ (p ^ n).choose j := hp.dvd_choose_pow (by omega) (by omega)
            have hcast : (((p ^ n).choose j : ℕ) : k) = 0 :=
              (CharP.cast_eq_zero_iff k p _).mpr hdvd
            rw [hcast, zero_mul]
          · rw [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < m + j), mul_zero]
      obtain ⟨α, _, hα⟩ := hca j (Finset.mem_range.mpr (by omega))
      rw [IsRoot.def, hhasse, eval_C] at hα
      exact hα
  have hQ_eq : Q = X ^ (p ^ n) := by
    ext j
    rw [coeff_X_pow]
    split_ifs with h
    · subst h
      rw [← hd, coeff_natDegree, hQ.leadingCoeff]
    · by_cases hj0 : j = 0
      · subst hj0
        rw [coeff_zero_eq_eval_zero]
        exact h0
      · by_cases hj_lt : j < p ^ n
        · exact hcoeff_zero (p ^ n - j) j rfl (by omega) hj_lt
        · exact coeff_eq_zero_of_natDegree_lt (by omega)
  rw [IsRoot.def, hQ_eq, eval_pow, eval_X, one_pow] at h1
  exact one_ne_zero h1

end CasasAlveroPrimePower

theorem OMA.solution : type_of% @CasasAlvero.casas_alvero.prime_power := by
  intro K _ _ P hP p k hp hd hP'
  let L := AlgebraicClosure K
  have hPL_monic : (P.map (algebraMap K L)).Monic := hP.map _
  have hPL_deg : (P.map (algebraMap K L)).natDegree = p ^ k := by
    rw [natDegree_map, hd]
  have hPL_ca : HasCasasAlveroPropᵣ (P.map (algebraMap K L)) :=
    hasCasasAlveroProp_iffᵣ.mp (HasCasasAlveroProp.map_iff.mpr hP')
  have hpos : 0 < P.natDegree := by
    rw [hd]
    exact pow_pos hp.pos k
  have hexL : ∃ α : L, P.map (algebraMap K L) = (X - C α) ^ (P.map (algebraMap K L)).natDegree := by
    by_contra hnot
    obtain ⟨kF, _, _, Q, hQ_monic, hQ_deg, hQ0, hQ1, hQca⟩ :=
      CasasAlveroPrimePower.exists_reduction_mod_p (P.map (algebraMap K L)) hPL_monic
        (by rw [hPL_deg]; exact pow_pos hp.pos k) hPL_ca hnot p hp
    exact CasasAlveroPrimePower.no_casasAlvero_prime_power_charP p k hp Q hQ_monic
      (by rw [hQ_deg, hPL_deg]) hQ0 hQ1 hQca
  obtain ⟨α, eq⟩ := hexL
  have h0 : P.natDegree ≠ 0 := hpos.ne'
  let α' : K := - P.nextCoeff / P.natDegree
  have hα' : algebraMap K L α' = α := by
    simp_rw [α', div_eq_inv_mul, map_mul, map_neg, ← nextCoeff_map (algebraMap K L).injective,
      congr_arg nextCoeff eq, (monic_X_sub_C α).nextCoeff_pow, nextCoeff_X_sub_C, nsmul_eq_mul,
      mul_neg _ α, neg_neg, ← mul_assoc, natDegree_map, map_inv₀, map_natCast]
    rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr h0), one_mul]
  refine ⟨α', ?_⟩
  apply map_injective _ (algebraMap K L).injective
  simpa [hα'] using eq
