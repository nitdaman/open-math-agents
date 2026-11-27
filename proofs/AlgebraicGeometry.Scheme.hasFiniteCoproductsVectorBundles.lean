import FormalConjectures.Paper.HartshorneConjecture
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite coproducts of vector bundles on a scheme
-/

-- Problem: AlgebraicGeometry
-- Upstream: formal-conjectures FormalConjectures/Paper/HartshorneConjecture.lean:59 (declaration AlgebraicGeometry.Scheme.hasFiniteCoproductsVectorBundles)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

section Helpers

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

variable (S : Scheme.{u})

private def vectorBundlesToModuleFullyFaithful :
    (AlgebraicGeometry.Scheme.VectorBundles.toModule S).FullyFaithful where
  preimage f := ⟨f⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

private lemma isLeftAdjoint_overFunctor (W : S.Opens) :
    (SheafOfModules.overFunctor S.ringCatSheaf W).IsLeftAdjoint :=
  inferInstanceAs (SheafOfModules.pushforward (𝟙 (S.ringCatSheaf.over W))).IsLeftAdjoint

private lemma isVectorBundleWithRank_of_iso {M N : S.Modules} {n : ℕ}
    (e : M ≅ N)
    (hM : SheafOfModules.IsVectorBundleWithRank (J := Opens.grothendieckTopology S) M n) :
    SheafOfModules.IsVectorBundleWithRank (J := Opens.grothendieckTopology S) N n := by
  obtain ⟨D, hD⟩ := hM.exists_vector_bundle_data
  let D' : SheafOfModules.FiniteRankVectorBundleData (J := Opens.grothendieckTopology S) N := {
    OpensIndex := D.OpensIndex
    opens := D.opens
    coversTop := D.coversTop
    BasisIndex := D.BasisIndex
    locallyFree := fun i =>
      (SheafOfModules.overFunctor S.ringCatSheaf (D.opens i)).mapIso e.symm ≪≫ D.locallyFree i
    finite := D.finite
  }
  exact { exists_vector_bundle_data := ⟨D', hD⟩ }

private lemma isVectorBundleWithRank_free_pempty :
    SheafOfModules.IsVectorBundleWithRank (J := Opens.grothendieckTopology S)
      (SheafOfModules.free (R := S.ringCatSheaf) PEmpty.{u + 1}) 0 := by
  have : (SheafOfModules.overFunctor S.ringCatSheaf (⊤ : S.Opens)).IsLeftAdjoint :=
    isLeftAdjoint_overFunctor S ⊤
  let D : SheafOfModules.FiniteRankVectorBundleData (J := Opens.grothendieckTopology S)
      (SheafOfModules.free (R := S.ringCatSheaf) PEmpty.{u + 1}) := {
    OpensIndex := PUnit.{u + 1}
    opens := fun _ => (⊤ : S.Opens)
    coversTop := by
      rw [Opens.coversTop_iff]
      simp [IsOpenCover]
    BasisIndex := fun _ => PEmpty.{u + 1}
    locallyFree := fun _ =>
      (SheafOfModules.mapFreeIso (SheafOfModules.overFunctor S.ringCatSheaf (⊤ : S.Opens))
        PEmpty.{u + 1} (Iso.refl _)).symm
    finite := fun _ => inferInstance
  }
  exact { exists_vector_bundle_data := ⟨D, fun _ => Nat.card_of_isEmpty⟩ }

private lemma isVectorBundleWithRank_coprod {M N : S.Modules} {m n : ℕ}
    (hM : SheafOfModules.IsVectorBundleWithRank (J := Opens.grothendieckTopology S) M m)
    (hN : SheafOfModules.IsVectorBundleWithRank (J := Opens.grothendieckTopology S) N n) :
    SheafOfModules.IsVectorBundleWithRank (J := Opens.grothendieckTopology S) (M ⨿ N) (m + n) := by
  obtain ⟨DM, hDM⟩ := hM.exists_vector_bundle_data
  obtain ⟨DN, hDN⟩ := hN.exists_vector_bundle_data
  have hcovM : IsOpenCover DM.opens := (Opens.coversTop_iff S _).mp DM.coversTop
  have hcovN : IsOpenCover DN.opens := (Opens.coversTop_iff S _).mp DN.coversTop
  let D : SheafOfModules.FiniteRankVectorBundleData (J := Opens.grothendieckTopology S)
      (M ⨿ N) := {
    OpensIndex := DM.OpensIndex × DN.OpensIndex
    opens := fun p => DM.opens p.1 ⊓ DN.opens p.2
    coversTop := by
      rw [Opens.coversTop_iff, IsOpenCover, eq_top_iff]
      intro x _
      have hxM : x ∈ ⨆ i, DM.opens i := by rw [hcovM]; trivial
      have hxN : x ∈ ⨆ j, DN.opens j := by rw [hcovN]; trivial
      rw [Opens.mem_iSup] at hxM hxN ⊢
      obtain ⟨i, hi⟩ := hxM
      obtain ⟨j, hj⟩ := hxN
      exact ⟨(i, j), ⟨hi, hj⟩⟩
    BasisIndex := fun p => DM.BasisIndex p.1 ⊕ DN.BasisIndex p.2
    locallyFree := fun p => by
      let W : S.Opens := DM.opens p.1 ⊓ DN.opens p.2
      have : (SheafOfModules.overFunctor S.ringCatSheaf W).IsLeftAdjoint :=
        isLeftAdjoint_overFunctor S W
      let f₁ : W ⟶ DM.opens p.1 := homOfLE inf_le_left
      let f₂ : W ⟶ DN.opens p.2 := homOfLE inf_le_right
      let eM : M.over W ≅ SheafOfModules.free (DM.BasisIndex p.1) :=
        ((SheafOfModules.overFunctorMap S.ringCatSheaf f₁).app M).symm ≪≫
          (SheafOfModules.overMap S.ringCatSheaf f₁).mapIso (DM.locallyFree p.1) ≪≫
          (SheafOfModules.mapFreeIso (SheafOfModules.overMap S.ringCatSheaf f₁) (DM.BasisIndex p.1)
            (SheafOfModules.overMapUnitIso f₁).symm).symm
      let eN : N.over W ≅ SheafOfModules.free (DN.BasisIndex p.2) :=
        ((SheafOfModules.overFunctorMap S.ringCatSheaf f₂).app N).symm ≪≫
          (SheafOfModules.overMap S.ringCatSheaf f₂).mapIso (DN.locallyFree p.2) ≪≫
          (SheafOfModules.mapFreeIso (SheafOfModules.overMap S.ringCatSheaf f₂) (DN.BasisIndex p.2)
            (SheafOfModules.overMapUnitIso f₂).symm).symm
      exact (PreservesColimitPair.iso (SheafOfModules.overFunctor S.ringCatSheaf W) M N).symm ≪≫
        coprod.mapIso eM eN ≪≫
        SheafOfModules.freeSumIso (DM.BasisIndex p.1) (DN.BasisIndex p.2)
    finite := fun p => by
      have := DM.finite p.1
      have := DN.finite p.2
      infer_instance
  }
  refine { exists_vector_bundle_data := ⟨D, fun p => ?_⟩ }
  have := DM.finite p.1
  have := DN.finite p.2
  dsimp [D]
  rw [Nat.card_sum, hDM p.1, hDN p.2]

private lemma hasColimit_vectorBundles_of_isVectorBundle {J : Type*} [Category J]
    (F : J ⥤ S.VectorBundles)
    [HasColimit (F ⋙ AlgebraicGeometry.Scheme.VectorBundles.toModule S)]
    (n : ℕ)
    (h : SheafOfModules.IsVectorBundleWithRank (J := Opens.grothendieckTopology S)
      (colimit (F ⋙ AlgebraicGeometry.Scheme.VectorBundles.toModule S) : S.Modules) n) :
    HasColimit F := by
  have : (AlgebraicGeometry.Scheme.VectorBundles.toModule S).Full :=
    (vectorBundlesToModuleFullyFaithful S).full
  have : (AlgebraicGeometry.Scheme.VectorBundles.toModule S).Faithful :=
    (vectorBundlesToModuleFullyFaithful S).faithful
  let V : S.VectorBundles :=
    ⟨colimit (F ⋙ AlgebraicGeometry.Scheme.VectorBundles.toModule S), n, h⟩
  have : CreatesColimit F (AlgebraicGeometry.Scheme.VectorBundles.toModule S) :=
    createsColimitOfFullyFaithfulOfIso V (Iso.refl _)
  exact hasColimit_of_created F (AlgebraicGeometry.Scheme.VectorBundles.toModule S)

private lemma hasInitial_vectorBundles : HasInitial S.VectorBundles := by
  refine ⟨fun F => ?_⟩
  have : (AlgebraicGeometry.Scheme.VectorBundles.toModule S).Full :=
    (vectorBundlesToModuleFullyFaithful S).full
  have : (AlgebraicGeometry.Scheme.VectorBundles.toModule S).Faithful :=
    (vectorBundlesToModuleFullyFaithful S).faithful
  let l : Cocone (F ⋙ AlgebraicGeometry.Scheme.VectorBundles.toModule S) :=
    ⟨(SheafOfModules.free (R := S.ringCatSheaf) PEmpty.{u + 1} : S.Modules),
      ⟨fun j => PEmpty.elim j.as, fun j => PEmpty.elim j.as⟩⟩
  let hl : IsColimit l :=
    { desc := fun s => (SheafOfModules.freeHomEquiv s.pt).symm PEmpty.elim
      fac := fun _ j => PEmpty.elim j.as
      uniq := fun s _ _ =>
        (SheafOfModules.freeHomEquiv s.pt).injective (funext fun x => PEmpty.elim x) }
  have : HasColimit (F ⋙ AlgebraicGeometry.Scheme.VectorBundles.toModule S) := ⟨⟨l, hl⟩⟩
  let V : S.VectorBundles := ⟨l.pt, 0, isVectorBundleWithRank_free_pempty S⟩
  have : CreatesColimit F (AlgebraicGeometry.Scheme.VectorBundles.toModule S) :=
    createsColimitOfFullyFaithfulOfIso' hl V (Iso.refl _)
  exact hasColimit_of_created F (AlgebraicGeometry.Scheme.VectorBundles.toModule S)

private lemma hasBinaryCoproducts_vectorBundles : HasBinaryCoproducts S.VectorBundles := by
  have : ∀ (X Y : S.VectorBundles), HasColimit (pair X Y) := fun X Y => by
    let eDiag : pair X Y ⋙ AlgebraicGeometry.Scheme.VectorBundles.toModule S ≅
        pair X.carrier Y.carrier :=
      mapPairIso (Iso.refl _) (Iso.refl _)
    let eColim : X.carrier ⨿ Y.carrier ≅
        colimit (pair X Y ⋙ AlgebraicGeometry.Scheme.VectorBundles.toModule S) :=
      HasColimit.isoOfNatIso eDiag.symm
    exact hasColimit_vectorBundles_of_isVectorBundle S (pair X Y) (X.rank + Y.rank)
      (isVectorBundleWithRank_of_iso S eColim
        (isVectorBundleWithRank_coprod S X.isLocallyFreeFiniteConstantRank
          Y.isLocallyFreeFiniteConstantRank))
  exact hasBinaryCoproducts_of_hasColimit_pair S.VectorBundles

end Helpers

theorem OMA.solution : type_of% @AlgebraicGeometry.Scheme.hasFiniteCoproductsVectorBundles := by
  intro S
  exact @CategoryTheory.hasFiniteCoproducts_of_has_binary_and_initial S.VectorBundles _
    (hasBinaryCoproducts_vectorBundles S) (hasInitial_vectorBundles S)
