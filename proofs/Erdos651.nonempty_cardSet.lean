import FormalConjectures.ErdosProblems.«651»
import Mathlib.Algebra.Module.Submodule.Union

/-!
The existence proof uses finite Ramsey in the plane and Valtr's generic projection, as described by
Pohoata and Zakharov, Section 1 (https://arxiv.org/abs/2208.04878).
-/

open scoped EuclideanGeometry Finset

theorem OMA.finite_image_pullback {α β : Type*} [DecidableEq β] (L : α → β) (X : Finset α) (Z : Finset β)
    (hZ : Z ⊆ X.image L) (hL : Set.InjOn L (X : Set α)) :
    ∃ Y ⊆ X, Y.image L = Z ∧ Y.card = Z.card := by
  classical
  let Y := X.filter fun y => L y ∈ Z
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image L = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hy).2
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hZ hz)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hz⟩, rfl⟩
  refine ⟨Y, hYX, hYZ, ?_⟩
  rw [← hYZ, Finset.card_image_of_injOn (hL.mono hYX)]

open scoped Classical in
theorem OMA.convex_subset_lifts {k d n : ℕ} (L : (ℝ^d) →ₗ[ℝ] (ℝ^k)) (X : Finset (ℝ^d))
    (hL : Set.InjOn L (X : Set (ℝ^d))) (hX : Erdos651.HasConvexSubset n (X.image L)) :
    Erdos651.HasConvexSubset n X := by
  classical
  obtain ⟨Z, hZ, hZn, hconv⟩ := hX
  obtain ⟨Y, hYX, hYZ, hcard⟩ := OMA.finite_image_pullback L X Z hZ hL
  refine ⟨Y, hYX, hcard.trans hZn, ?_⟩
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hconv ⊢
  intro y hy h
  have hLy : L y ∈ (Z : Set (ℝ^k)) := by
    rw [← hYZ]
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  apply hconv (L y) hLy
  have himage : L '' ((Y : Set (ℝ^d)) \ {y}) ⊆ (Z : Set (ℝ^k)) \ {L y} := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hYZ]
      exact Finset.mem_image.mpr ⟨a, ha.1, rfl⟩
    · intro he
      exact ha.2 (hL (hYX ha.1) (hYX hy) he)
  apply convexHull_mono himage
  rw [← L.image_convexHull]
  exact ⟨y, h, rfl⟩

open scoped Classical in
theorem OMA.generic_projection {k : ℕ} (hk : 1 ≤ k) (X : Finset (ℝ^(k+1)))
    (hX : Erdos651.IsInGeneralPosition X) :
    ∃ L : (ℝ^(k+1)) →ₗ[ℝ] (ℝ^k),
      Set.InjOn L (X : Set (ℝ^(k+1))) ∧ Erdos651.IsInGeneralPosition (X.image L) := by
  classical
  let T := X.powerset.filter fun Y => Y.card ≤ k + 1
  let W (Y : T) : Submodule ℝ (ℝ^(k+1)) := vectorSpan ℝ (Y.val : Set (ℝ^(k+1)))
  have hW (Y : T) : W Y ≠ ⊤ := by
    have hsmall : Y.val.card ≤ k + 1 := (Finset.mem_filter.mp Y.prop).2
    have hdim : Module.finrank ℝ (W Y) ≤ k := by
      rcases Y.val.eq_empty_or_nonempty with hY | hY
      · change Module.finrank ℝ (vectorSpan ℝ (Y.val : Set (ℝ^(k+1)))) ≤ k
        rw [hY, Finset.coe_empty, vectorSpan_empty, finrank_bot]
        exact Nat.zero_le _
      · have hcard : Y.val.card = (Y.val.card - 1) + 1 := by
          have := Finset.card_pos.mpr hY
          omega
        have h := finrank_vectorSpan_image_finset_le ℝ id Y.val hcard
        rw [Finset.image_id] at h
        have h' : Module.finrank ℝ (W Y) ≤ Y.val.card - 1 := h
        omega
    intro htop
    rw [htop, finrank_top, finrank_euclideanSpace_fin] at hdim
    omega
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top W hW
  have hv₀ : v ≠ 0 := by
    let e : T := ⟨∅, by simp [T]⟩
    intro h
    exact hv e (h.symm ▸ (W e).zero_mem)
  let U := ℝ ∙ v
  have hdim : Module.finrank ℝ ((ℝ^(k+1)) ⧸ U) = Module.finrank ℝ (ℝ^k) := by
    have h := U.finrank_quotient_add_finrank
    rw [show Module.finrank ℝ U = 1 from finrank_span_singleton hv₀,
      finrank_euclideanSpace_fin] at h
    rw [finrank_euclideanSpace_fin]
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hdim
  let L : (ℝ^(k+1)) →ₗ[ℝ] (ℝ^k) := e.toLinearMap.comp U.mkQ
  have hker (Y : Finset (ℝ^(k+1))) (hYX : Y ⊆ X) (hY : Y.card ≤ k + 1) :
      Disjoint (vectorSpan ℝ (Y : Set (ℝ^(k+1)))) (LinearMap.ker L) := by
    let i : T := ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hYX, hY⟩⟩
    rw [Submodule.disjoint_def]
    intro u hu hlu
    have hU : u ∈ U := by
      rw [← Submodule.ker_mkQ U]
      apply LinearMap.mem_ker.mpr
      apply e.injective
      exact (LinearMap.mem_ker.mp hlu).trans e.map_zero.symm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hU
    by_cases ha₀ : a = 0
    · simpa [ha₀] using ha.symm
    · rw [← ha] at hu
      exact (hv i (((W i).smul_mem_iff ha₀).mp hu)).elim
  have hL : Set.InjOn L (X : Set (ℝ^(k+1))) := by
    intro a ha b hb hab
    let Y : Finset (ℝ^(k+1)) := {a, b}
    have hYX : Y ⊆ X := by
      intro x hx
      simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have hY : Y.card ≤ k + 1 := Finset.card_le_two.trans (by omega)
    have hm : a - b ∈ vectorSpan ℝ (Y : Set (ℝ^(k+1))) :=
      vsub_mem_vectorSpan ℝ (show a ∈ (Y : Set _) by simp [Y])
        (show b ∈ (Y : Set _) by simp [Y])
    have hd : a - b ∈ LinearMap.ker L := LinearMap.mem_ker.mpr (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp (hker Y hYX hY) _ hm hd)
  refine ⟨L, hL, fun Z hZ hcard => ?_⟩
  obtain ⟨Y, hYX, hYZ, hcardY⟩ := OMA.finite_image_pullback L X Z hZ hL
  have hYcard : Y.card ≤ k + 1 := hcardY.trans_le hcard
  let p : ↥(Y : Set (ℝ^(k+1))) → ℝ^(k+1) := Subtype.val
  have hrange : Set.range (L ∘ p) = (Z : Set (ℝ^k)) := by
    rw [Set.range_comp, Subtype.range_coe, ← Finset.coe_image, hYZ]
  suffices h : AffineIndependent ℝ (L ∘ p) by
    rw [← hrange]
    exact h.range
  rcases isEmpty_or_nonempty ↥(Y : Set (ℝ^(k+1))) with hEmpty | hNonempty
  · let _ := hEmpty
    exact affineIndependent_of_subsingleton _ (L ∘ p)
  · obtain ⟨y⟩ := hNonempty
    have hind : AffineIndependent ℝ p := hX Y hYX (by omega)
    have hd := (affineIndependent_iff_linearIndependent_vsub ℝ p y).mp hind
    apply (affineIndependent_iff_linearIndependent_vsub ℝ (L ∘ p) y).mpr
    have hs : Submodule.span ℝ (Set.range (fun i : {i // i ≠ y} => p i -ᵥ p y)) ≤
        vectorSpan ℝ (Y : Set (ℝ^(k+1))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact vsub_mem_vectorSpan ℝ i.val.prop y.prop
    have hm := hd.map ((hker Y hYX hYcard).mono_left hs)
    change LinearIndependent ℝ (fun i : {i // i ≠ y} => L (p i - p y)) at hm
    simpa only [Function.comp_apply, vsub_eq_sub, map_sub] using hm

theorem OMA.cardSet_projection {k n N : ℕ} (hk : 1 ≤ k) (hN : N ∈ Erdos651.cardSet k n) :
    N ∈ Erdos651.cardSet (k + 1) n := by
  classical
  intro X hX hcard
  obtain ⟨L, hL, hgp⟩ := OMA.generic_projection hk X hX
  apply OMA.convex_subset_lifts L X hL
  apply hN _ hgp
  rwa [Finset.card_image_of_injOn hL]

/-- Finite two-colour Ramsey existence for sets of a given size. -/
theorem OMA.finite_ramsey_sets (α : Type*) [DecidableEq α] (r n : ℕ) :
    ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ c : Finset α → Bool,
      ∃ Y ⊆ X, Y.card = n ∧ ∃ b : Bool, ∀ A ⊆ Y, A.card = r → c A = b := by
  induction r generalizing n with
  | zero =>
    refine ⟨n, fun X hX c => ?_⟩
    obtain ⟨Y, hYX, hcard⟩ := Finset.exists_subset_card_eq hX
    refine ⟨Y, hYX, hcard, c ∅, fun A _ hA => ?_⟩
    rw [Finset.card_eq_zero.mp hA]
  | succ r ih =>
    have stage (t : ℕ) : ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ c : Finset α → Bool,
        ∃ Y ⊆ X, Y.card = t ∧ ∃ labels : α → Bool,
          ∀ A ⊆ Y, A.card = r + 1 → ∃ a ∈ A, c A = labels a := by
      induction t with
      | zero =>
        refine ⟨0, fun X _ _ => ⟨∅, Finset.empty_subset X, rfl, fun _ => false, ?_⟩⟩
        intro A hA hcard
        have hempty := Finset.subset_empty.mp hA
        simp [hempty] at hcard
      | succ t it =>
        obtain ⟨M, hM⟩ := it
        obtain ⟨N, hN⟩ := ih M
        refine ⟨N + 1, fun X hX c => ?_⟩
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
        have herase : N ≤ (X.erase x).card := by
          rw [Finset.card_erase_of_mem hx]
          omega
        obtain ⟨R, hR, hcardR, b, hb⟩ := hN (X.erase x) herase (fun A => c (insert x A))
        obtain ⟨Y, hY, hcard, labels, hlabels⟩ := hM R hcardR.ge c
        have hxY : x ∉ Y := fun h => (Finset.mem_erase.mp (hR (hY h))).1 rfl
        have hYX := hY.trans (hR.trans (Finset.erase_subset x X))
        refine ⟨insert x Y, Finset.insert_subset hx hYX, by simp [hxY, hcard],
          Function.update labels x b, ?_⟩
        intro A hA hcardA
        by_cases hxA : x ∈ A
        · have hAY : A.erase x ⊆ Y := by
            intro a ha
            obtain ⟨hne, haA⟩ := Finset.mem_erase.mp ha
            exact (Finset.mem_insert.mp (hA haA)).resolve_left hne
          have hac : (A.erase x).card = r := by rw [Finset.card_erase_of_mem hxA, hcardA]; simp
          refine ⟨x, hxA, ?_⟩
          simpa [Finset.insert_erase hxA] using hb _ (hAY.trans hY) hac
        · have hAY : A ⊆ Y := by
            intro a ha
            exact (Finset.mem_insert.mp (hA ha)).resolve_left (fun he => hxA (he ▸ ha))
          obtain ⟨a, ha, hc⟩ := hlabels A hAY hcardA
          have hax : a ≠ x := by
            rintro rfl
            exact hxA ha
          exact ⟨a, ha, by rwa [Function.update_of_ne hax]⟩
    obtain ⟨N, hN⟩ := stage (2 * n)
    refine ⟨N, fun X hX c => ?_⟩
    obtain ⟨Y, hYX, hcard, labels, hlabels⟩ := hN X hX c
    let U := Y.filter fun a => labels a = true
    let V := Y.filter fun a => labels a ≠ true
    have hsum : U.card + V.card = 2 * n :=
      (Finset.card_filter_add_card_filter_not (s := Y) _).trans hcard
    by_cases hU : n ≤ U.card
    · obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq hU
      have hZY := hZ.trans (Finset.filter_subset _ _)
      refine ⟨Z, hZY.trans hYX, hcardZ, true, ?_⟩
      intro A hA hcardA
      obtain ⟨a, ha, he⟩ := hlabels A (hA.trans hZY) hcardA
      exact he.trans (Finset.mem_filter.mp (hZ (hA ha))).2
    · have hV : n ≤ V.card := by omega
      obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq hV
      have hZY := hZ.trans (Finset.filter_subset _ _)
      refine ⟨Z, hZY.trans hYX, hcardZ, false, ?_⟩
      intro A hA hcardA
      obtain ⟨a, ha, he⟩ := hlabels A (hA.trans hZY) hcardA
      have ht := (Finset.mem_filter.mp (hZ (hA ha))).2
      exact he.trans (by cases h : labels a <;> simp_all)

theorem OMA.planar_coordinates (X : Finset (ℝ^2)) :
    ∃ x y : (ℝ^2) →ₗ[ℝ] ℝ, Set.InjOn x (X : Set (ℝ^2)) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  classical
  let bad := (X ×ˢ X).image fun uv : (ℝ^2) × (ℝ^2) =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : ℝ^2) (hx : x p = x q) (hy : y p = y q) : p = q := by
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 = q 1 at hy
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      rw [hy] at hx
      exact add_right_cancel hx
    · exact hy
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq hx
  by_cases hy : y p = y q
  · exact hjoint p q hx hy
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 ≠ q 1 at hy
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    nlinarith only [hx]

noncomputable def OMA.planar_slope (x y : (ℝ^2) → ℝ) (p q : ℝ^2) : ℝ :=
  (y q - y p) / (x q - x p)

theorem OMA.planar_slope_ne (X : Finset (ℝ^2)) (hX : Erdos651.IsInGeneralPosition X)
    (x y : (ℝ^2) →ₗ[ℝ] ℝ) (hjoin : ∀ p q, x p = x q → y p = y q → p = q)
    {a b c : ℝ^2} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : x a < x b) (hbc : x b < x c) :
    OMA.planar_slope x y a b ≠ OMA.planar_slope x y b c := by
  classical
  intro he
  let r := (x b - x a) / (x c - x b)
  have hxb : x b - x a = r * (x c - x b) := by
    dsimp [r]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hbc.ne')]
  have hyb : y b - y a = r * (y c - y b) := by
    have hex := (div_eq_div_iff (sub_ne_zero.mpr hab.ne') (sub_ne_zero.mpr hbc.ne')).mp he
    dsimp [r]
    rw [div_mul_eq_mul_div, eq_div_iff (sub_ne_zero.mpr hbc.ne')]
    exact hex.trans (mul_comm _ _)
  have hdiff : b - a = r • (c - b) := by
    apply hjoin
    · simpa only [map_sub, map_smul, smul_eq_mul] using hxb
    · simpa only [map_sub, map_smul, smul_eq_mul] using hyb
  have hcol : Collinear ℝ ({a, b, c} : Set (ℝ^2)) := by
    apply (collinear_iff_of_mem (show b ∈ ({a, b, c} : Set (ℝ^2)) by simp)).mpr
    refine ⟨c - b, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · refine ⟨-r, ?_⟩
      change _ = (-r) • (c - b) + b
      rw [neg_smul, ← hdiff]
      abel
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  let S : Finset (ℝ^2) := {a, b, c}
  have hSX : S ⊆ X := by
    intro p hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hnab : a ≠ b := fun h => hab.ne (congrArg x h)
  have hnac : a ≠ c := fun h => (hab.trans hbc).ne (congrArg x h)
  have hnbc : b ≠ c := fun h => hbc.ne (congrArg x h)
  let w : Fin 3 → (S : Set (ℝ^2)) :=
    ![⟨a, by simp [S]⟩, ⟨b, by simp [S]⟩, ⟨c, by simp [S]⟩]
  have hw : Function.Injective w := by
    intro i j hij
    have h := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [w, hnab, hnac, hnbc, hnab.symm, hnac.symm, hnbc.symm] at h ⊢
  have hind : AffineIndependent ℝ ![a, b, c] := by
    have h := (hX S hSX Finset.card_le_three).comp_embedding (⟨w, hw⟩ : Fin 3 ↪ S)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  exact (affineIndependent_iff_not_collinear_set.mp hind) hcol

theorem OMA.planar_convex_of_increasing_slopes (Y : Finset (ℝ^2))
    (x y : (ℝ^2) →ₗ[ℝ] ℝ) (hinj : Set.InjOn x (Y : Set (ℝ^2)))
    (hslope : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, x a < x b → x b < x c →
      OMA.planar_slope x y a b < OMA.planar_slope x y b c) :
    ConvexIndependent ℝ (Subtype.val : ↥(Y : Set (ℝ^2)) → ℝ^2) := by
  classical
  have hsupport (p : ℝ^2) (hp : p ∈ Y) : ∃ L : (ℝ^2) →ₗ[ℝ] ℝ,
      ∀ q ∈ Y, q ≠ p → L p < L q := by
    let A := Y.filter fun q => x q < x p
    let B := Y.filter fun q => x p < x q
    by_cases hA : A.Nonempty
    · by_cases hB : B.Nonempty
      · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image A (fun a => OMA.planar_slope x y a p) hA
        obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image B (OMA.planar_slope x y p) hB
        obtain ⟨haY, hap⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbY, hpb⟩ := Finset.mem_filter.mp hb
        obtain ⟨s, h₁, h₂⟩ := exists_between (hslope a haY p hp b hbY hap hpb)
        refine ⟨y - s • x, fun q hq hqp => ?_⟩
        change y p - s * x p < y q - s * x q
        have hne : x q ≠ x p := fun h => hqp (hinj hq hp h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hs := (hmax q (Finset.mem_filter.mpr ⟨hq, hlt⟩)).trans_lt h₁
          have hs' := (div_lt_iff₀ (sub_pos.mpr hlt)).mp hs
          linarith
        · have hs := h₂.trans_le (hmin q (Finset.mem_filter.mpr ⟨hq, hgt⟩))
          have hs' := (lt_div_iff₀ (sub_pos.mpr hgt)).mp hs
          linarith
      · refine ⟨-x, fun q hq hqp => ?_⟩
        change -x p < -x q
        have hne : x q ≠ x p := fun h => hqp (hinj hq hp h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact neg_lt_neg hlt
        · exact (hB ⟨q, Finset.mem_filter.mpr ⟨hq, hgt⟩⟩).elim
    · refine ⟨x, fun q hq hqp => ?_⟩
      have hne : x q ≠ x p := fun h => hqp (hinj hq hp h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (hA ⟨q, Finset.mem_filter.mpr ⟨hq, hlt⟩⟩).elim
      · exact hgt
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro p hp h
  obtain ⟨L, hL⟩ := hsupport p hp
  have hsub : (Y : Set (ℝ^2)) \ {p} ⊆ {q | L p < L q} :=
    fun q hq => hL q hq.1 hq.2
  have he := (convexHull_min hsub (convex_halfSpace_gt L.isLinear (L p))) h
  exact (lt_irrefl (L p)) he

theorem OMA.planar_cardSet_nonempty (n : ℕ) : (Erdos651.cardSet 2 n).Nonempty := by
  classical
  obtain ⟨N, hN⟩ := OMA.finite_ramsey_sets (ℝ^2) 3 n
  refine ⟨N, fun X hX hNX => ?_⟩
  obtain ⟨x, y, hx, hjoin⟩ := OMA.planar_coordinates X
  let color (A : Finset (ℝ^2)) : Bool := decide
    (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, x a < x b ∧ x b < x c ∧
      OMA.planar_slope x y a b < OMA.planar_slope x y b c)
  obtain ⟨Y, hYX, hcard, col, hcol⟩ := hN X hNX color
  refine ⟨Y, hYX, hcard, ?_⟩
  have hY (a : ℝ^2) (ha : a ∈ Y) (b : ℝ^2) (hb : b ∈ Y) (c : ℝ^2) (hc : c ∈ Y)
      (hab : x a < x b) (hbc : x b < x c) :
      (OMA.planar_slope x y a b < OMA.planar_slope x y b c) ↔ col = true := by
    let A : Finset (ℝ^2) := {a, b, c}
    have hAY : A ⊆ Y := by
      intro p hp
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have hAcard : A.card = 3 := Finset.card_triple_eq_three_iff.mpr
      ⟨fun h => hab.ne (congrArg x h), fun h => (hab.trans hbc).ne (congrArg x h),
        fun h => hbc.ne (congrArg x h)⟩
    rw [← hcol A hAY hAcard]
    change _ ↔ decide _ = true
    rw [decide_eq_true_eq]
    constructor
    · exact fun hs => ⟨a, by simp [A], b, by simp [A], c, by simp [A], hab, hbc, hs⟩
    · rintro ⟨a', ha', b', hb', c', hc', hab', hbc', hs'⟩
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at ha' hb' hc'
      have heq : a' = a ∧ b' = b ∧ c' = c := by
        rcases ha' with rfl | rfl | rfl <;>
          rcases hb' with rfl | rfl | rfl <;>
          rcases hc' with rfl | rfl | rfl <;> grind
      rcases heq with ⟨rfl, rfl, rfl⟩
      exact hs'
  cases h : col with
  | true =>
    exact OMA.planar_convex_of_increasing_slopes Y x y (hx.mono hYX)
      (fun a ha b hb c hc hab hbc => (hY a ha b hb c hc hab hbc).mpr h)
  | false =>
    apply OMA.planar_convex_of_increasing_slopes Y x (-y) (hx.mono hYX)
    intro a ha b hb c hc hab hbc
    have hnot : ¬OMA.planar_slope x y a b < OMA.planar_slope x y b c := by
      rw [hY a ha b hb c hc hab hbc, h]
      decide
    have hne := OMA.planar_slope_ne X hX x y hjoin (hYX ha) (hYX hb) (hYX hc) hab hbc
    have hgt := lt_of_le_of_ne (le_of_not_gt hnot) hne.symm
    have hflip (u v : ℝ^2) : OMA.planar_slope x (-y) u v = -OMA.planar_slope x y u v := by
      change (-y v - -y u) / (x v - x u) = -((y v - y u) / (x v - x u))
      rw [show -y v - -y u = -(y v - y u) by ring, neg_div]
    calc
      OMA.planar_slope x (-y) a b = -OMA.planar_slope x y a b := hflip a b
      _ < -OMA.planar_slope x y b c := neg_lt_neg hgt
      _ = OMA.planar_slope x (-y) b c := (hflip b c).symm

theorem OMA.solution : type_of% @Erdos651.nonempty_cardSet := by
  intro k hk n
  induction k, hk using Nat.le_induction with
  | base => exact OMA.planar_cardSet_nonempty n
  | succ k hk ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N, OMA.cardSet_projection (by omega) hN⟩