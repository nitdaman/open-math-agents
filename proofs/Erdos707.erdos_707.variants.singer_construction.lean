import FormalConjectures.ErdosProblems.«707»

/-!
# Erdős Problem 707, the Singer construction

Problem: Erdős Problem 707 — singer construction.
Upstream: formal-conjectures FormalConjectures/ErdosProblems/707.lean:164.

Idea (Singer): let `F` be a field with `q` elements, `K` an extension of degree three, `γ` a
generator of the multiplicative group of `K`, and `n = q ^ 2 + q + 1`. A power `γ ^ i` lies in `F`
exactly when `n` divides `i`, so `γ ^ i` and `γ ^ j` are proportional over `F` exactly when
`i ≡ j` modulo `n`. Fix a plane `W` (an `F`-subspace of dimension two) and let `B` be the set of
`i < n` with `γ ^ i ∈ W`. For `c` outside `F` the planes `W` and `c W` are different, so they meet
in a line. Taking `c = γ ^ d` this says that every nonzero residue `d` is a difference of two
elements of `B` in exactly one way. Counting the differences then gives `B.ncard = q + 1`.
-/

namespace Erdos707Singer

lemma cube_sub_one (q : ℕ) (hq : 1 ≤ q) : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hq
  apply Nat.sub_eq_of_eq_add
  simp only [Nat.add_sub_cancel_left]
  ring

/-- An element fixed by the `q`-th power map lies in the subfield with `q` elements. -/
lemma mem_range_of_pow_card_eq {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F]
    (x : K) (hx : x ^ Nat.card F = x) : ∃ a : F, algebraMap F K a = x := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at hx
  have hP0 : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hdeg : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).natDegree
      = Fintype.card F := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  have hroot : ∀ y : K, y ^ Fintype.card F = y →
      y ∈ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hy, sub_self]
  have hsub : (Finset.univ.image (algebraMap F K)) ⊆
      (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset := by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
    apply hroot
    rw [← map_pow, FiniteField.pow_card]
  have hcard : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset.card
      ≤ (Finset.univ.image (algebraMap F K)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap F K).injective, Finset.card_univ]
    calc (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset.card
        ≤ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.card :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).natDegree :=
          Polynomial.card_roots' _
      _ = Fintype.card F := hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hxmem := hroot x hx
  rw [← heq] at hxmem
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hxmem
  exact ⟨a, ha⟩

/-- A generator of the multiplicative group of a finite field, as an element of the field. -/
lemma exists_gen (K : Type*) [Field K] [Finite K] :
    ∃ γ : K, γ ≠ 0 ∧ (∀ x : K, x ≠ 0 → ∃ i : ℕ, γ ^ i = x) ∧
      (∀ m : ℕ, γ ^ m = 1 → (Nat.card K - 1) ∣ m) ∧ γ ^ (Nat.card K - 1) = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  have hord : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_powers hg, Nat.card_units]
  refine ⟨(g : K), g.ne_zero, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (hg (Units.mk0 x hx))
    exact ⟨i, by rw [← Units.val_pow_eq_pow_val, hi, Units.val_mk0]⟩
  · intro m hm
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hm, Units.val_one]
  · rw [← hord, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]

lemma exists_plane {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) : ∃ W : Submodule F K, Module.finrank F W = 2 := by
  have hli : LinearIndependent F
      (fun i : Fin 2 => (Module.finBasisOfFinrankEq F K h3) (Fin.castSucc i)) :=
    (Module.finBasisOfFinrankEq F K h3).linearIndependent.comp _ (Fin.castSucc_injective 2)
  exact ⟨Submodule.span F
    (Set.range (fun i : Fin 2 => (Module.finBasisOfFinrankEq F K h3) (Fin.castSucc i))), by
      rw [finrank_span_eq_card hli, Fintype.card_fin]⟩

/-- A plane is not stable under multiplication by an element outside the base field. -/
lemma not_stable {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) (W : Submodule F K) (hW : Module.finrank F W = 2)
    (c : K) (hc : c ∉ (algebraMap F K).range) : ¬ ∀ w ∈ W, c * w ∈ W := by
  intro hst
  have hpos : 0 < Module.finrank F W := by omega
  obtain ⟨⟨w, hwW⟩, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hw : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hint : IsIntegral F c := IsIntegral.of_finite F c
  have hdeg : (minpoly F c).natDegree = 3 := by
    have hdvd := minpoly.degree_dvd hint
    rw [h3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
    · exact absurd (minpoly.natDegree_eq_one_iff.1 h1) hc
    · exact h3'
  have hli := linearIndependent_pow (K := F) c
  rw [hdeg] at hli
  have hli2 : LinearIndependent F (fun i : Fin 3 => c ^ (i : ℕ) * w) := by
    have hker : LinearMap.ker (LinearMap.mulRight F w) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      exact mul_right_cancel₀ hw hxy
    exact hli.map' (LinearMap.mulRight F w) hker
  have hmem : ∀ i : ℕ, c ^ i * w ∈ W := by
    intro i
    induction i with
    | zero => simpa using hwW
    | succ k ih =>
      rw [pow_succ', mul_assoc]
      exact hst _ ih
  have hspan : Submodule.span F (Set.range (fun i : Fin 3 => c ^ (i : ℕ) * w)) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hle := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli2, Fintype.card_fin, hW] at hle
  omega

/-- Two planes in a three-dimensional space meet: some nonzero `y ∈ W` has `c * y ∈ W`. -/
lemma key_exists {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) (W : Submodule F K) (hW : Module.finrank F W = 2)
    (c : K) (hc0 : c ≠ 0) : ∃ y ∈ W, y ≠ 0 ∧ c * y ∈ W := by
  have hinj : Function.Injective (LinearMap.mulLeft F c) := by
    intro x y hxy
    exact mul_left_cancel₀ hc0 hxy
  have h1 : Module.finrank F
      (W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
        K →ₗ[F] K)) = 2 := by
    rw [LinearEquiv.finrank_map_eq, hW]
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq W
    (W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
      K →ₗ[F] K))
  have h4 : Module.finrank F
      ↥(W ⊔ W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
        K →ₗ[F] K)) ≤ 3 := by
    rw [← h3]
    exact Submodule.finrank_le _
  have hpos : 0 < Module.finrank F
      ↥(W ⊓ W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
        K →ₗ[F] K)) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hx' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  rw [Submodule.mem_inf, Submodule.mem_map] at hx
  obtain ⟨hxW, y, hyW, hyx⟩ := hx
  have hcy : c * y = x := by
    rw [← hyx]
    rfl
  refine ⟨y, hyW, ?_, ?_⟩
  · rintro rfl
    exact hx' (by rw [← hcy, mul_zero])
  · rw [hcy]
    exact hxW

/-- For `c` outside the base field, the solutions `y ∈ W` of `c * y ∈ W` form a line. -/
lemma key_unique {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) (W : Submodule F K) (hW : Module.finrank F W = 2)
    (c : K) (hc : c ∉ (algebraMap F K).range) {y y' : K} (hy : y ∈ W) (hy0 : y ≠ 0)
    (hcy : c * y ∈ W) (hy' : y' ∈ W) (hcy' : c * y' ∈ W) : ∃ a : F, y' = a • y := by
  have hne : W ⊓ W.comap (LinearMap.mulLeft F c) ≠ W := by
    intro h
    apply not_stable h3 W hW c hc
    intro w hw
    rw [← h] at hw
    exact (Submodule.mem_inf.1 hw).2
  have hlt : W ⊓ W.comap (LinearMap.mulLeft F c) < W := lt_of_le_of_ne inf_le_left hne
  have hfr := Submodule.finrank_lt_finrank_of_lt hlt
  have hle1 : Module.finrank F ↥(W ⊓ W.comap (LinearMap.mulLeft F c)) ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hle1
  have hyU : y ∈ W ⊓ W.comap (LinearMap.mulLeft F c) := Submodule.mem_inf.2 ⟨hy, hcy⟩
  have hyU' : y' ∈ W ⊓ W.comap (LinearMap.mulLeft F c) := Submodule.mem_inf.2 ⟨hy', hcy'⟩
  obtain ⟨t, ht⟩ := hv ⟨y, hyU⟩
  obtain ⟨t', ht'⟩ := hv ⟨y', hyU'⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact hy0 (congrArg Subtype.val ht).symm
  have e1 : t • (v : K) = y := congrArg Subtype.val ht
  have e2 : t' • (v : K) = y' := congrArg Subtype.val ht'
  refine ⟨t' * t⁻¹, ?_⟩
  rw [← e1, ← e2, smul_smul, inv_mul_cancel_right₀ ht0]

/-- The Singer construction for a field `F` with a cubic extension `K`. -/
theorem core {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3) :
    ∃ B : Set ℕ, IsPerfectDifferenceSet B (Nat.card F ^ 2 + Nat.card F + 1) ∧
      B.ncard = Nat.card F + 1 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨q, hqdef⟩ : ∃ q, q = Nat.card F := ⟨_, rfl⟩
  rw [← hqdef]
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    exact Finite.one_lt_card
  obtain ⟨n, hn⟩ : ∃ n, n = q ^ 2 + q + 1 := ⟨_, rfl⟩
  rw [← hn]
  have hnpos : 0 < n := by omega
  have : NeZero n := ⟨hnpos.ne'⟩
  have hcardK : Nat.card K = q ^ 3 := by
    rw [hqdef, ← h3]
    exact Module.natCard_eq_pow_finrank
  have hN : Nat.card K - 1 = (q - 1) * n := by
    rw [hcardK, hn]
    exact cube_sub_one q (by omega)
  obtain ⟨γ, hγ0, hγsurj, hγord, hγpow⟩ := exists_gen K
  rw [hN] at hγord hγpow
  obtain ⟨W, hW⟩ := exists_plane (F := F) (K := K) h3
  -- powers of `γ` in the base field
  have hA1 : ∀ (i : ℕ) (a : F), algebraMap F K a = γ ^ i → n ∣ i := by
    intro i a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact pow_ne_zero i hγ0 ha.symm
    have h1 : a ^ (q - 1) = 1 := by
      rw [hqdef, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one a ha0
    have h2 : γ ^ (i * (q - 1)) = 1 := by
      rw [pow_mul, ← ha, ← map_pow, h1, map_one]
    have h3' := hγord _ h2
    rw [mul_comm i] at h3'
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) h3'
  have hA2 : ∀ i : ℕ, n ∣ i → ∃ a : F, algebraMap F K a = γ ^ i := by
    rintro i ⟨m, rfl⟩
    apply mem_range_of_pow_card_eq
    have h1 : (γ ^ (n * m)) ^ (q - 1) = 1 := by
      rw [← pow_mul, show n * m * (q - 1) = (q - 1) * n * m by ring, pow_mul, hγpow, one_pow]
    rw [← hqdef]
    calc (γ ^ (n * m)) ^ q = (γ ^ (n * m)) ^ (q - 1 + 1) := by
          rw [Nat.sub_add_cancel (by omega)]
      _ = γ ^ (n * m) := by rw [pow_succ, h1, one_mul]
  -- the exponent `M'` acts as `-1`
  obtain ⟨M', hM'⟩ : ∃ M', (q - 1) * n = M' + 1 :=
    ⟨(q - 1) * n - 1, by
      have : 0 < (q - 1) * n := Nat.mul_pos (by omega) hnpos
      omega⟩
  have hM'cast : (M' : ZMod n) = -1 := by
    have h : ((M' + 1 : ℕ) : ZMod n) = 0 := by
      rw [← hM', Nat.cast_mul, ZMod.natCast_self, mul_zero]
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have hrel1 : ∀ i j : ℕ, γ ^ (j + M' * i) * γ ^ i = γ ^ j := by
    intro i j
    rw [← pow_add, show j + M' * i + i = j + (M' + 1) * i by ring, ← hM', pow_add, pow_mul,
      hγpow, one_pow, mul_one]
  have hrel2 : ∀ i j : ℕ, ((j + M' * i : ℕ) : ZMod n) = (j : ZMod n) - (i : ZMod n) := by
    intro i j
    push_cast
    rw [hM'cast]
    ring
  -- proportional powers have congruent exponents, and conversely
  have hP : ∀ (i j : ℕ) (a : F), γ ^ j = algebraMap F K a * γ ^ i →
      (j : ZMod n) = (i : ZMod n) := by
    intro i j a h
    have h1 : algebraMap F K a = γ ^ (j + M' * i) := by
      have h' := hrel1 i j
      rw [h] at h'
      exact (mul_right_cancel₀ (pow_ne_zero i hγ0) h').symm
    have h2 := hA1 _ a h1
    have h3' : ((j + M' * i : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
    rw [hrel2] at h3'
    exact sub_eq_zero.1 h3'
  have hQ : ∀ i j : ℕ, (j : ZMod n) = (i : ZMod n) →
      ∃ a : F, γ ^ j = algebraMap F K a * γ ^ i := by
    intro i j h
    have h1 : ((j + M' * i : ℕ) : ZMod n) = 0 := by rw [hrel2, h, sub_self]
    obtain ⟨a, ha⟩ := hA2 _ ((ZMod.natCast_eq_zero_iff _ _).1 h1)
    exact ⟨a, by rw [ha, hrel1]⟩
  have hWmod : ∀ i j : ℕ, (j : ZMod n) = (i : ZMod n) → γ ^ i ∈ W → γ ^ j ∈ W := by
    intro i j h hi
    obtain ⟨a, ha⟩ := hQ i j h
    rw [ha, ← Algebra.smul_def]
    exact W.smul_mem a hi
  have hcast : ∀ a b : ℕ, a < n → b < n → (a : ZMod n) = (b : ZMod n) → a = b := by
    intro a b ha hb h
    have h' := (ZMod.natCast_eq_natCast_iff' a b n).1 h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  -- the difference set
  obtain ⟨B, hB⟩ : ∃ B : Set ℕ, B = {i : ℕ | i < n ∧ γ ^ i ∈ W} := ⟨_, rfl⟩
  have hBmem : ∀ i : ℕ, i ∈ B ↔ i < n ∧ γ ^ i ∈ W := by
    intro i
    rw [hB]
    rfl
  have hpds : IsPerfectDifferenceSet B n := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb, hne⟩ := hab
      show (a : ZMod n) - (b : ZMod n) ≠ 0
      intro h
      exact hne (hcast a b ((hBmem a).1 ha).1 ((hBmem b).1 hb).1 (sub_eq_zero.1 h))
    · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
      obtain ⟨ha, hb, hne⟩ := hab
      obtain ⟨ha', hb', hne'⟩ := hab'
      have heq' : (a : ZMod n) - (b : ZMod n) = (a' : ZMod n) - (b' : ZMod n) := heq
      obtain ⟨han, haW⟩ := (hBmem a).1 ha
      obtain ⟨hbn, hbW⟩ := (hBmem b).1 hb
      obtain ⟨han', haW'⟩ := (hBmem a').1 ha'
      obtain ⟨hbn', hbW'⟩ := (hBmem b').1 hb'
      -- `c = γ ^ a / γ ^ b`, written as a power of `γ`
      have hc : γ ^ (a + M' * b) ∉ (algebraMap F K).range := by
        rintro ⟨t, ht⟩
        have h1 := hA1 _ t ht
        have h2 : ((a + M' * b : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h1
        rw [hrel2] at h2
        exact hne (hcast a b han hbn (sub_eq_zero.1 h2))
      have hcy : γ ^ (a + M' * b) * γ ^ b ∈ W := by
        rw [hrel1]
        exact haW
      have hcy' : γ ^ (a + M' * b) * γ ^ b' ∈ W := by
        rw [← pow_add]
        refine hWmod a' _ ?_ haW'
        push_cast
        rw [hM'cast]
        linear_combination heq'
      obtain ⟨s, hs⟩ := key_unique h3 W hW _ hc hbW (pow_ne_zero b hγ0) hcy hbW' hcy'
      rw [Algebra.smul_def] at hs
      have hbb : b' = b := hcast b' b hbn' hbn (hP b b' s hs)
      subst hbb
      have haa : (a : ZMod n) = (a' : ZMod n) := by linear_combination heq'
      have haa' : a = a' := hcast a a' han han' haa
      subst haa'
      rfl
    · intro x hx
      have hx0 : x ≠ 0 := hx
      obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ZMod n) = x := ⟨x.val, ZMod.natCast_zmod_val x⟩
      obtain ⟨y, hyW, hy0, hcy⟩ := key_exists h3 W hW (γ ^ d) (pow_ne_zero d hγ0)
      obtain ⟨j, rfl⟩ := hγsurj y hy0
      rw [← pow_add] at hcy
      refine ⟨((d + j) % n, j % n), ⟨?_, ?_, ?_⟩, ?_⟩
      · exact (hBmem _).2 ⟨Nat.mod_lt _ hnpos, hWmod (d + j) _ (ZMod.natCast_mod _ _) hcy⟩
      · exact (hBmem _).2 ⟨Nat.mod_lt _ hnpos, hWmod j _ (ZMod.natCast_mod _ _) hyW⟩
      · intro h
        apply hx0
        have h' : ((d + j : ℕ) : ZMod n) = (j : ZMod n) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).2 h
        push_cast at h'
        rw [← hd]
        linear_combination h'
      · show (((d + j) % n : ℕ) : ZMod n) - ((j % n : ℕ) : ZMod n) = x
        rw [ZMod.natCast_mod, ZMod.natCast_mod, ← hd]
        push_cast
        ring
  -- counting the differences gives the size
  have hfin : B.Finite := (Set.finite_Iio n).subset (fun i hi => ((hBmem i).1 hi).1)
  have hcard : B.ncard = q + 1 := by
    have h1 : B.offDiag.ncard = n - 1 := by
      have h' := hpds.injOn.ncard_image
      rw [hpds.image_eq] at h'
      rw [← h']
      have h0 : {x : ZMod n | x ≠ 0} = ({0} : Set (ZMod n))ᶜ := by
        ext x
        simp
      rw [h0, Set.ncard_compl, Set.ncard_singleton, Nat.card_zmod]
    clear hB hBmem
    lift B to Finset ℕ using hfin
    rw [← Finset.coe_offDiag, Set.ncard_coe_finset, Finset.offDiag_card] at h1
    rw [Set.ncard_coe_finset]
    have hk : B.card * B.card = q ^ 2 + q + B.card := by
      have := Nat.le_mul_self B.card
      omega
    have hz : ((B.card : ℤ) - (q + 1)) * ((B.card : ℤ) + q) = 0 := by
      have hk' : (B.card : ℤ) * B.card = q ^ 2 + q + B.card := by exact_mod_cast hk
      linear_combination hk'
    rcases mul_eq_zero.1 hz with h | h
    · omega
    · omega
  exact ⟨B, hpds, hcard⟩

end Erdos707Singer

theorem OMA.solution : type_of% @Erdos707.erdos_707.variants.singer_construction := by
  intro p hp
  obtain ⟨r, k, hr, hk, rfl⟩ := hp
  have : Fact r.Prime := ⟨Nat.prime_iff.2 hr⟩
  have h := Erdos707Singer.core (F := GaloisField r k)
    (K := FiniteField.Extension (GaloisField r k) r 3)
    (FiniteField.finrank_extension (GaloisField r k) r 3)
  rw [GaloisField.card r k hk.ne'] at h
  exact h
