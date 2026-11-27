import FormalConjectures.Wikipedia.NoetherProblem

-- Problem: NoetherProblem noether_problem variants two
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/NoetherProblem.lean (declaration NoetherProblem.noether_problem.variants.two)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)

/-!
With two indeterminates the group permuting them is trivial or the full symmetric group.
In the first case the fixed field is everything. In the second case the fixed field is the
field of symmetric rational functions, which is the fraction field of the ring of symmetric
polynomials (clear denominators with the product of all conjugates of the denominator), and
that ring is a polynomial ring by the fundamental theorem of symmetric polynomials.
-/

namespace OMA.Noether2

open MvPolynomial NoetherProblem Equiv

variable {K L ι : Type} [Field K] [Field L] [Fintype ι] [Algebra K L]

lemma phi_algebraMap (σ : Perm ι) (a : MvPolynomial ι K) :
    (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ) :
        FractionRing (MvPolynomial ι K) ≃ₐ[K] FractionRing (MvPolynomial ι K))
      (algebraMap _ (FractionRing (MvPolynomial ι K)) a) =
      algebraMap _ (FractionRing (MvPolynomial ι K)) (rename σ a) := by
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

lemma phi_one (y : FractionRing (MvPolynomial ι K)) :
    (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K (1 : Perm ι)) :
        FractionRing (MvPolynomial ι K) ≃ₐ[K] FractionRing (MvPolynomial ι K)) y = y := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial ι K) y
  rw [map_div₀, phi_algebraMap, phi_algebraMap]
  simp [Perm.coe_one, rename_id]

lemma prod_rename_symm [DecidableEq ι] (q : MvPolynomial ι K) (τ : Perm ι) :
    rename τ (∏ σ : Perm ι, rename σ q) = ∏ σ : Perm ι, rename σ q := by
  rw [map_prod]
  simp_rw [rename_rename]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) (fun σ => rename (⇑τ ∘ ⇑σ) q)
    (fun σ => rename ⇑σ q) (fun σ => by simp [Perm.coe_mul])

theorem main (e : L ≃ₐ[K] FractionRing (MvPolynomial ι K)) (E : IntermediateField K L)
    (hE : ∀ x : L, x ∈ E ↔ ∀ σ : Perm ι,
      e.symm ((IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ) :
        FractionRing (MvPolynomial ι K) ≃ₐ[K] FractionRing (MvPolynomial ι K)) (e x)) = x) :
    IsRationalExtension K E (Fin (Fintype.card ι)) := by
  classical
  set n := Fintype.card ι
  set P := MvPolynomial (Fin n) K
  set A := MvPolynomial ι K
  set FR := FractionRing A
  let s := esymmAlgEquiv ι K (rfl : Fintype.card ι = n)
  let f : P →+* L := (e.symm : FR →+* L).comp ((algebraMap A FR).comp
    ((symmetricSubalgebra ι K).val.toRingHom.comp (s : P →+* symmetricSubalgebra ι K)))
  have hf : ∀ p, f p = e.symm (algebraMap A FR (s p : A)) := fun p => rfl
  have fmem : ∀ p, f p ∈ E := by
    intro p
    rw [hE]
    intro σ
    rw [hf, AlgEquiv.apply_symm_apply, phi_algebraMap, (s p).2 σ]
  let g : P →+* E := f.codRestrict E fmem
  have hg : ∀ p, (g p : L) = e.symm (algebraMap A FR (s p : A)) := fun p => rfl
  have ginj : Function.Injective g := by
    intro p q hpq
    have h1 : (g p : L) = g q := by rw [hpq]
    rw [hg, hg] at h1
    have h2 := (IsFractionRing.injective A FR) (e.symm.injective h1)
    exact s.injective (Subtype.ext h2)
  letI : Algebra P E := g.toAlgebra
  have hgalg : ∀ p, algebraMap P E p = g p := fun p => rfl
  haveI : FaithfulSMul P E := (faithfulSMul_iff_algebraMap_injective P E).mpr ginj
  have hsurj : ∀ z : E, ∃ x y, z = algebraMap P E x / algebraMap P E y := by
    intro z
    have hz : ∀ σ : Perm ι, (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ) :
        FR ≃ₐ[K] FR) (e z) = e z := by
      intro σ
      have := (hE z).mp z.2 σ
      have h' := congrArg e this
      rwa [AlgEquiv.apply_symm_apply] at h'
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := A) (e z)
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have haq : algebraMap A FR q ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap A FR)]
      exact fun h => hq0 (IsFractionRing.injective A FR h)
    set R := ∏ σ ∈ Finset.univ.erase (1 : Perm ι), rename σ q with hRd
    set Q := ∏ σ : Perm ι, rename σ q with hQd
    have hQ : Q = q * R := by
      rw [hQd, hRd, ← Finset.mul_prod_erase Finset.univ (fun σ : Perm ι => rename σ q)
        (Finset.mem_univ 1)]
      simp [Perm.coe_one, rename_id]
    have hQsym : Q.IsSymmetric := fun τ => prod_rename_symm q τ
    have hQ0 : Q ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro σ _
      exact (rename_injective _ σ.injective).ne_iff' (map_zero _) |>.mpr hq0
    have hkey : algebraMap A FR (p * R) = e z * algebraMap A FR Q := by
      rw [← hpq, hQ, map_mul, map_mul, div_mul_eq_mul_div, eq_div_iff haq]
      ring
    have hPsym : (p * R).IsSymmetric := by
      intro τ
      apply IsFractionRing.injective A FR
      rw [← phi_algebraMap, hkey, map_mul, hz, phi_algebraMap, hQsym τ]
    refine ⟨s.symm ⟨p * R, hPsym⟩, s.symm ⟨Q, hQsym⟩, ?_⟩
    have hgy : g (s.symm ⟨Q, hQsym⟩) ≠ 0 := by
      rw [Ne, ← map_zero g]
      intro h
      have := ginj h
      rw [← map_zero s.symm] at this
      have := s.symm.injective this
      exact hQ0 (congrArg Subtype.val this)
    rw [hgalg, hgalg, eq_div_iff hgy]
    apply Subtype.ext
    apply e.injective
    rw [IntermediateField.coe_mul, map_mul, hg, hg, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hkey]
  haveI : IsFractionRing P E := IsFractionRing.of_field P E hsurj
  let eqv : FractionRing P ≃ₐ[P] E := IsLocalization.algEquiv (nonZeroDivisors P) (FractionRing P) E
  have hcomm : ∀ k : K, eqv.toRingEquiv (algebraMap K (FractionRing P) k) =
      algebraMap K E k := by
    intro k
    rw [IsScalarTower.algebraMap_apply K P (FractionRing P) k]
    change eqv (algebraMap P (FractionRing P) (algebraMap K P k)) = _
    rw [AlgEquiv.commutes, hgalg]
    apply Subtype.ext
    rw [hg, AlgEquiv.commutes]
    change e.symm (algebraMap A FR (algebraMap K A k)) = _
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
    rfl
  exact ⟨⟨(AlgEquiv.ofRingEquiv (f := eqv.toRingEquiv) hcomm).symm⟩⟩

end OMA.Noether2

open OMA.Noether2 Equiv in
theorem OMA.solution : type_of% @NoetherProblem.noether_problem.variants.two := by
  intro K L ι _ _ _ _ _ hι e H hH
  classical
  by_cases htriv : ∀ h ∈ H, h = 1
  · have htop : IntermediateField.fixedField H = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [IntermediateField.mem_fixedField_iff]
      intro h hh
      rw [htriv h hh]
      rfl
    exact ⟨ι, ⟨⟨((IntermediateField.equivOfEq htop).trans
      IntermediateField.topEquiv).trans e⟩⟩⟩
  · push Not at htriv
    obtain ⟨h, hh, hne⟩ := htriv
    obtain ⟨σ, hσdef⟩ := hH h hh
    have happ : ∀ (τ : Perm ι) (x : L),
        ((AlgEquiv.autCongr e).symm (IsFractionRing.algEquivOfAlgEquiv
          (MvPolynomial.renameEquiv K τ)) : L ≃ₐ[K] L) x =
        e.symm ((IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K τ) :
          FractionRing (MvPolynomial ι K) ≃ₐ[K] FractionRing (MvPolynomial ι K)) (e x)) := by
      intro τ x
      rfl
    have hσ : σ ≠ 1 := by
      rintro rfl
      apply hne
      rw [hσdef]
      ext x
      rw [happ, phi_one, AlgEquiv.symm_apply_apply]
      rfl
    have hall : ∀ τ : Perm ι, τ = 1 ∨ τ = σ := by
      intro τ
      by_contra hc
      push Not at hc
      have h3 : ({1, σ, τ} : Finset (Perm ι)).card = 3 :=
        Finset.card_eq_three.mpr ⟨1, σ, τ, hσ.symm, hc.1.symm, fun h' => hc.2 h'.symm, rfl⟩
      have hle := Finset.card_le_univ ({1, σ, τ} : Finset (Perm ι))
      rw [h3, Fintype.card_perm, hι] at hle
      norm_num at hle
    refine ⟨Fin (Fintype.card ι), main e _ ?_⟩
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    constructor
    · intro hx τ
      rcases hall τ with rfl | rfl
      · rw [phi_one, AlgEquiv.symm_apply_apply]
      · have := hx h hh
        rw [hσdef, happ] at this
        exact this
    · intro hx h' hh'
      obtain ⟨τ, rfl⟩ := hH h' hh'
      rw [happ]
      exact hx τ
