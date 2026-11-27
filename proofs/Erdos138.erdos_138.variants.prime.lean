import FormalConjectures.ErdosProblems.«138»
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Erdos Problem 138 — prime

We formalize Berlekamp's 1968 theorem that `p * 2 ^ p ≤ W (p + 1)` for every prime `p`.
Using a primitive root `α` of the multiplicative group of `GaloisField 2 p` (order `2 ^ p - 1`)
and the unique `ZMod 2`-linear functional taking value `1` on the `p` consecutive powers
`α ^ (-⌊p / 2⌋), ..., α ^ (⌈p / 2⌉ - 1)`, we obtain a `(2 ^ p - 1)`-periodic sequence `f : ℤ → ZMod 2`
and wrap `p` periods with `⌊p / 2⌋` zeros on the left and `⌈p / 2⌉` zeros on the right to color
`{1, ..., p * 2 ^ p}` with no monochromatic `(p + 1)`-term arithmetic progression.
-/

namespace OMAErdos138Prime

open Module IntermediateField

/- ### Nonemptiness of `monoAP_guarantee_set` via Hales-Jewett -/

lemma progressionImage {N k : ℕ} (f : Fin k → ↥(Finset.Icc 1 N))
    (a d : ℕ) (hd : 0 < d) (hv : ∀ j, (f j).val = a + j.val * d) :
    (Subtype.val '' Set.range f).IsAPOfLength k := by
  have hf : Function.Injective f := by
    intro i j hij
    have heq := congrArg Subtype.val hij
    rw [hv i, hv j] at heq
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel heq)
  refine ⟨a, d, ?_, ?_⟩
  · rw [ENat.card_image_of_injective _ _ Subtype.val_injective,
      ← ENat.card_congr (Equiv.ofInjective f hf),
      ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  · ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, by
        simpa [nsmul_eq_mul] using (hv i).symm⟩
    · rintro ⟨n, hn, rfl⟩
      let i : Fin k := ⟨n, by exact_mod_cast hn⟩
      refine ⟨f i, ⟨i, rfl⟩, ?_⟩
      simpa [i, nsmul_eq_mul] using hv i

lemma guarantee_nonempty (r k : ℕ) : (Erdos138.monoAP_guarantee_set r k).Nonempty := by
  classical
  obtain ⟨ι, fi, hj⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  let _ := fi
  let N := 1 + Fintype.card ι * k
  refine ⟨N, ?_⟩
  intro coloring
  let point (w : ι → Fin k) : Finset.Icc 1 N :=
    ⟨1 + ∑ i, (w i).val, Finset.mem_Icc.mpr ⟨by omega, by
      have bound : (∑ i, (w i).val) ≤ ∑ _i : ι, k :=
        Finset.sum_le_sum fun i _ => (w i).isLt.le
      exact Nat.add_le_add_left (by simpa [nsmul_eq_mul] using bound) 1⟩⟩
  obtain ⟨line, color, mono⟩ := hj (fun w => coloring (point w))
  let fixed (i : ι) : ℕ := ((line.idxFun i).map Fin.val).getD 0
  let variableWeight (i : ι) : ℕ := if line.idxFun i = none then 1 else 0
  let a := 1 + ∑ i, fixed i
  let d := ∑ i, variableWeight i
  have hd : 0 < d := by
    obtain ⟨i, hi⟩ := line.proper
    exact Finset.sum_pos' (fun j _ => Nat.zero_le (variableWeight j))
      ⟨i, Finset.mem_univ i, by simp [variableWeight, hi]⟩
  have digit (j : Fin k) (i : ι) :
      (line j i).val = fixed i + j.val * variableWeight i := by
    cases h : line.idxFun i <;>
      simp [Combinatorics.Line.coe_apply, fixed, variableWeight, h]
  have value (j : Fin k) : (point (line j)).val = a + j.val * d := by
    change 1 + ∑ i, (line j i).val = (1 + ∑ i, fixed i) + j.val * ∑ i, variableWeight i
    simp only [digit, Finset.sum_add_distrib, Finset.mul_sum, Nat.add_assoc]
  refine ⟨color, Set.range (fun j : Fin k => point (line j)), ?_, ?_⟩
  · exact progressionImage (fun j : Fin k => point (line j)) a d hd value
  · rintro _ ⟨j, rfl⟩
    exact mono j

/- ### Arithmetic helper lemmas -/

lemma p_add_one_le_two_pow_sub_one {p : ℕ} (hp : 2 ≤ p) : p + 1 ≤ 2 ^ p - 1 := by
  induction p with
  | zero => omega
  | succ m ih =>
    by_cases hm : 2 ≤ m
    · have ihm := ih hm
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    · have hm1 : m = 1 := by omega
      subst hm1
      decide

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/- ### Shifted power bases in `GaloisField 2 p` -/

lemma linearIndependent_shifted_pow {p : ℕ} (hp : p.Prime) [Fact (Nat.Prime 2)]
    {δ γ : GaloisField 2 p} (hδ : δ ≠ 0) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1) :
    LinearIndependent (ZMod 2) (fun i : Fin p => δ * γ ^ (i : ℕ)) := by
  classical
  let K := GaloisField 2 p
  have hfinK : Module.finrank (ZMod 2) K = p := GaloisField.finrank 2 hp.ne_zero
  have hint : IsIntegral (ZMod 2) γ := Algebra.IsIntegral.isIntegral γ
  let F : IntermediateField (ZMod 2) K := (ZMod 2)⟮γ⟯
  have hmul : Module.finrank (ZMod 2) F * Module.finrank F K = p := by
    rw [Module.finrank_mul_finrank (ZMod 2) F K, hfinK]
  have hdvd : Module.finrank (ZMod 2) F ∣ p := ⟨Module.finrank F K, hmul.symm⟩
  have hfinF_ne_one : Module.finrank (ZMod 2) F ≠ 1 := by
    intro h1
    let _ : Fintype F := Fintype.ofFinite F
    have hcardF : Fintype.card F = 2 := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := F), h1, pow_one, ZMod.card]
    let gF : F := ⟨γ, IntermediateField.mem_adjoin_simple_self (ZMod 2) γ⟩
    have hg0 : gF ≠ 0 := fun h => hγ0 (congrArg Subtype.val h)
    have hg1 : gF ≠ 1 := fun h => hγ1 (congrArg Subtype.val h)
    have h01 : (0 : F) ≠ 1 := zero_ne_one
    have hsub : ({0, 1, gF} : Finset F) ⊆ Finset.univ := Finset.subset_univ _
    have h3 : ({0, 1, gF} : Finset F).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · exact Finset.notMem_singleton.mpr hg1.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h01, hg0.symm⟩
    have hle := Finset.card_le_card hsub
    rw [h3, Finset.card_univ, hcardF] at hle
    omega
  have hfinF : Module.finrank (ZMod 2) F = p :=
    (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hfinF_ne_one
  have hdeg : (minpoly (ZMod 2) γ).natDegree = p := by
    have h := IntermediateField.adjoin.finrank hint
    exact h.symm.trans hfinF
  let pb := IntermediateField.adjoin.powerBasis hint
  have hli_pb : LinearIndependent (ZMod 2) pb.basis := pb.basis.linearIndependent
  have hker : LinearMap.ker F.val.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr Subtype.val_injective
  have hli_K0 : LinearIndependent (ZMod 2)
      (fun i : Fin pb.dim => F.val.toLinearMap (pb.basis i)) :=
    hli_pb.map' F.val.toLinearMap hker
  have hpb_dim : pb.dim = p := hdeg
  let e : Fin p ≃ Fin pb.dim := (finCongr hpb_dim).symm
  have hli_pow : LinearIndependent (ZMod 2) (fun i : Fin p => γ ^ (i : ℕ)) := by
    have hcomp : LinearIndependent (ZMod 2)
        ((fun i : Fin pb.dim => F.val.toLinearMap (pb.basis i)) ∘ e) :=
      hli_K0.comp e e.injective
    have hfun : ((fun i : Fin pb.dim => F.val.toLinearMap (pb.basis i)) ∘ e) =
        (fun i : Fin p => γ ^ (i : ℕ)) := by
      funext i
      change (pb.basis (e i) : K) = γ ^ (i : ℕ)
      rw [pb.basis_eq_pow]
      have heval : (e i : ℕ) = (i : ℕ) := by simp [e]
      rw [heval]
      simp [pb, IntermediateField.AdjoinSimple.gen]
    rwa [hfun] at hcomp
  let mulMap : K →ₗ[ZMod 2] K := LinearMap.mulLeft (ZMod 2) δ
  have hker_mul : LinearMap.ker mulMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hδ)
  exact hli_pow.map' mulMap hker_mul

noncomputable def omaShiftedBasis {p : ℕ} (hp : p.Prime) [Fact (Nat.Prime 2)]
    {δ γ : GaloisField 2 p} (hδ : δ ≠ 0) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1) :
    Basis (Fin p) (ZMod 2) (GaloisField 2 p) :=
  let _ : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_shifted_pow hp hδ hγ0 hγ1)
    (by rw [Fintype.card_fin, GaloisField.finrank 2 hp.ne_zero])

lemma linearMap_eq_zero_of_shifted_pow {p : ℕ} (hp : p.Prime) [Fact (Nat.Prime 2)]
    (L : GaloisField 2 p →ₗ[ZMod 2] ZMod 2)
    {δ γ : GaloisField 2 p} (hδ : δ ≠ 0) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1)
    (hvan : ∀ i : Fin p, L (δ * γ ^ (i : ℕ)) = 0) :
    L = 0 := by
  have _ : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
  let B := omaShiftedBasis hp hδ hγ0 hγ1
  refine B.ext fun i => ?_
  have hBi : B i = δ * γ ^ (i : ℕ) := by
    simp [B, omaShiftedBasis]
  rw [hBi, hvan i, LinearMap.zero_apply]

lemma zpow_add_mul_orderOf {G : Type*} [Group G] (g : G) (z q : ℤ) :
    g ^ (z + q * (orderOf g : ℤ)) = g ^ z := by
  rw [zpow_add, mul_comm q, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]

/- ### Periodic sequence over `ZMod 2` from `GaloisField 2 p` -/

lemma exists_berlekamp_periodic_func (p : ℕ) (hp : p.Prime) :
    ∃ f : ℤ → ZMod 2,
      (∀ z : ℤ, -((p / 2 : ℕ) : ℤ) ≤ z → z < ((p - p / 2 : ℕ) : ℤ) → f z = 1) ∧
      (∀ z q : ℤ, f (z + q * ((2 ^ p - 1 : ℕ) : ℤ)) = f z) ∧
      (∀ (b : ℤ) (d : ℕ), ¬ ((2 ^ p - 1) ∣ d) →
        ¬ (∀ i : Fin p, f (b + (i : ℕ) * (d : ℤ)) = 0)) ∧
      (∀ (b : ℤ) (d : ℕ), ¬ ((2 ^ p - 1) ∣ d) →
        ¬ (∀ j ≤ p, f (b + (j : ℤ) * (d : ℤ)) = 1)) := by
  classical
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : 2 ≤ p := hp.two_le
  set M : ℕ := 2 ^ p - 1
  have hpM : p + 1 ≤ M := p_add_one_le_two_pow_sub_one hp2
  set aL : ℕ := p / 2
  set aR : ℕ := p - aL
  let K := GaloisField 2 p
  let _ : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ p := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := K), GaloisField.finrank 2 hp.ne_zero,
      ZMod.card]
  have hcardU : Nat.card Kˣ = M := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
  obtain ⟨α, hα_ord0⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hα_ord : orderOf α = M := hα_ord0.trans hcardU
  have hα0 : (α : K) ≠ 0 := α.ne_zero
  have hα1 : (α : K) ≠ 1 := by
    intro h1
    have hu : α = 1 := Units.ext h1
    rw [hu, orderOf_one] at hα_ord
    omega
  let δ₀ : K := ((α ^ (-(aL : ℤ)) : Kˣ) : K)
  have hδ₀ : δ₀ ≠ 0 := Units.ne_zero _
  let B₀ := omaShiftedBasis hp hδ₀ hα0 hα1
  let L : K →ₗ[ZMod 2] ZMod 2 := B₀.constr (ZMod 2) (fun _ : Fin p => (1 : ZMod 2))
  have hL_basis : ∀ i : Fin p, L (δ₀ * (α : K) ^ (i : ℕ)) = 1 := by
    intro i
    have hBi : B₀ i = δ₀ * (α : K) ^ (i : ℕ) := by simp [B₀, omaShiftedBasis]
    rw [← hBi]
    exact B₀.constr_basis (ZMod 2) (fun _ : Fin p => (1 : ZMod 2)) i
  let f : ℤ → ZMod 2 := fun z => L (((α ^ z : Kˣ) : K))
  have hf_win : ∀ z : ℤ, -(aL : ℤ) ≤ z → z < (aR : ℤ) → f z = 1 := by
    intro z hz1 hz2
    let k : ℕ := (z + (aL : ℤ)).toNat
    have hk_eq : (k : ℤ) = z + (aL : ℤ) := Int.toNat_of_nonneg (by omega)
    have hk_lt : k < p := by omega
    have hz_eq : z = -(aL : ℤ) + (k : ℕ) := by omega
    have hpow : ((α ^ z : Kˣ) : K) = δ₀ * (α : K) ^ k := by
      rw [hz_eq, zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
    dsimp [f]
    rw [hpow]
    exact hL_basis ⟨k, hk_lt⟩
  have hL_one : L 1 = 1 := by
    have h0 := hf_win 0 (by omega) (by omega)
    simpa [f] using h0
  refine ⟨f, hf_win, ?_, ?_, ?_⟩
  · intro z q
    dsimp [f]
    rw [← hα_ord, zpow_add_mul_orderOf]
  · intro b d hndvd hvan0
    let γu : Kˣ := α ^ d
    have hγu1 : γu ≠ 1 := by
      intro h1
      apply hndvd
      rw [← hα_ord]
      exact orderOf_dvd_iff_pow_eq_one.mpr h1
    let γ : K := (γu : K)
    have hγ0 : γ ≠ 0 := Units.ne_zero _
    have hγ1 : γ ≠ 1 := fun h => hγu1 (Units.ext h)
    let δ : K := ((α ^ b : Kˣ) : K)
    have hδ : δ ≠ 0 := Units.ne_zero _
    have hvan : ∀ i : Fin p, L (δ * γ ^ (i : ℕ)) = 0 := by
      intro i
      have hpow : (((α ^ (b + (i : ℕ) * (d : ℤ)) : Kˣ) : K)) = δ * γ ^ (i : ℕ) := by
        have hexp : (i : ℕ) * (d : ℤ) = (((i : ℕ) * d : ℕ) : ℤ) := by push_cast; rfl
        rw [hexp, zpow_add, zpow_natCast, Units.val_mul]
        congr 1
        dsimp [γ, γu]
        rw [← pow_mul, mul_comm d (i : ℕ)]
      rw [← hpow]
      exact hvan0 i
    have hL0 := linearMap_eq_zero_of_shifted_pow hp L hδ hγ0 hγ1 hvan
    have h10 : L 1 = 0 := by rw [hL0]; rfl
    rw [hL_one] at h10
    exact one_ne_zero h10
  · intro b d hndvd hall1
    let γu : Kˣ := α ^ d
    have hγu1 : γu ≠ 1 := by
      intro h1
      apply hndvd
      rw [← hα_ord]
      exact orderOf_dvd_iff_pow_eq_one.mpr h1
    let γ : K := (γu : K)
    have hγ0 : γ ≠ 0 := Units.ne_zero _
    have hγ1 : γ ≠ 1 := fun h => hγu1 (Units.ext h)
    let δ : K := (((α ^ b : Kˣ) : K)) * (γ - 1)
    have hδ : δ ≠ 0 := mul_ne_zero (Units.ne_zero _) (sub_ne_zero.mpr hγ1)
    have hvan : ∀ i : Fin p, L (δ * γ ^ (i : ℕ)) = 0 := by
      intro i
      have h1 : (((α ^ (b + (i : ℕ) * (d : ℤ)) : Kˣ) : K)) =
          (((α ^ b : Kˣ) : K)) * γ ^ (i : ℕ) := by
        have hexp : (i : ℕ) * (d : ℤ) = (((i : ℕ) * d : ℕ) : ℤ) := by push_cast; rfl
        rw [hexp, zpow_add, zpow_natCast, Units.val_mul]
        congr 1
        dsimp [γ, γu]
        rw [← pow_mul, mul_comm d (i : ℕ)]
      let j1 : ℕ := (i : ℕ) + 1
      have h2 : (((α ^ (b + (j1 : ℤ) * (d : ℤ)) : Kˣ) : K)) =
          (((α ^ b : Kˣ) : K)) * γ ^ j1 := by
        have hexp : (j1 : ℤ) * (d : ℤ) = ((j1 * d : ℕ) : ℤ) := by
          push_cast; rfl
        rw [hexp, zpow_add, zpow_natCast, Units.val_mul]
        congr 1
        dsimp [γ, γu]
        rw [← pow_mul, mul_comm d j1]
      have hdiff : δ * γ ^ (i : ℕ) =
          (((α ^ (b + (j1 : ℤ) * (d : ℤ)) : Kˣ) : K)) -
          (((α ^ (b + (i : ℕ) * (d : ℤ)) : Kˣ) : K)) := by
        rw [h1, h2]
        dsimp [j1, δ]
        rw [pow_succ]
        ring
      rw [hdiff, map_sub]
      have hv2 : f (b + (j1 : ℤ) * (d : ℤ)) = 1 := hall1 j1 (by dsimp [j1]; omega)
      have hv1 : f (b + (i : ℕ) * (d : ℤ)) = 1 := hall1 (i : ℕ) (by omega)
      dsimp [f] at hv1 hv2
      rw [hv2, hv1, sub_self]
    have hL0 := linearMap_eq_zero_of_shifted_pow hp L hδ hγ0 hγ1 hvan
    have h10 : L 1 = 0 := by rw [hL0]; rfl
    rw [hL_one] at h10
    exact one_ne_zero h10

/- ### Combinatorial check of Berlekamp's interval coloring -/

lemma fin2_eq_zero_or_one (c : Fin 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

lemma berlekamp_comb_aux (p M aL aR : ℕ)
    (hp2 : 2 ≤ p) (hpM : p + 1 ≤ M) (haLR : aL + aR = p)
    (haL_le_aR : aL ≤ aR) (haR_sub_le_aL : aR - 1 ≤ aL)
    (f : ℤ → ZMod 2)
    (hf_win : ∀ z : ℤ, -(aL : ℤ) ≤ z → z < (aR : ℤ) → f z = 1)
    (hf_per : ∀ z q : ℤ, f (z + q * (M : ℤ)) = f z)
    (hf_no0 : ∀ (b : ℤ) (d : ℕ), ¬ (M ∣ d) → ¬ (∀ i : Fin p, f (b + (i : ℕ) * (d : ℤ)) = 0))
    (hf_no1 : ∀ (b : ℤ) (d : ℕ), ¬ (M ∣ d) → ¬ (∀ j ≤ p, f (b + (j : ℤ) * (d : ℤ)) = 1)) :
    ∃ col : ℕ → Fin 2,
      ∀ (c : Fin 2) (a₀ d : ℕ), 1 ≤ d → 1 ≤ a₀ → a₀ + p * d ≤ aL + p * M + aR →
        ¬ (∀ j ≤ p, col (a₀ + j * d) = c) := by
  classical
  have hpM_gt_p : p < p * M := by
    have h2M : 2 ≤ M := by omega
    calc p = p * 1 := (mul_one p).symm
      _ < p * M := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  let zOf : ℕ → ℤ := fun m => (m : ℤ) - 1 - (aL : ℤ)
  let col : ℕ → Fin 2 := fun m =>
    if aL + 1 ≤ m ∧ m ≤ aL + p * M then
      if f (zOf m) = 0 then 0 else 1
    else 0
  have hcol_eq_one_of : ∀ m : ℕ, aL + 1 ≤ m → m ≤ aL + p * M → f (zOf m) = 1 → col m = 1 := by
    intro m hm1 hm2 hf1
    have hmid : aL + 1 ≤ m ∧ m ≤ aL + p * M := ⟨hm1, hm2⟩
    have hne0 : f (zOf m) ≠ 0 := by rw [hf1]; decide
    dsimp [col]
    rw [if_pos hmid, if_neg hne0]
  have hf_eq_zero_of_col_zero : ∀ m : ℕ, aL + 1 ≤ m → m ≤ aL + p * M → col m = 0 →
      f (zOf m) = 0 := by
    intro m hm1 hm2 hc0
    have hmid : aL + 1 ≤ m ∧ m ≤ aL + p * M := ⟨hm1, hm2⟩
    dsimp [col] at hc0
    rw [if_pos hmid] at hc0
    by_contra hne
    rw [if_neg hne] at hc0
    exact (by decide : (1 : Fin 2) ≠ 0) hc0
  refine ⟨col, ?_⟩
  intro c a₀ d hd1 ha₀1 hlast hmono
  rcases fin2_eq_zero_or_one c with rfl | rfl
  · -- Case `c = 0`
    have hbar_left : ∀ m : ℕ, aL + 1 ≤ m → m ≤ p → col m = 1 := by
      intro m hm1 hm2
      apply hcol_eq_one_of m hm1 (by omega)
      exact hf_win (zOf m) (by dsimp [zOf]; omega) (by dsimp [zOf]; omega)
    have hbar_right : ∀ m : ℕ, p * M + 1 ≤ m → m ≤ aL + p * M → col m = 1 := by
      intro m hm1 hm2
      apply hcol_eq_one_of m (by omega) hm2
      let w : ℤ := zOf m - (p : ℤ) * (M : ℤ)
      have hzeq : zOf m = w + (p : ℤ) * (M : ℤ) := by dsimp [w]; ring
      rw [hzeq, hf_per w p]
      exact hf_win w (by dsimp [w, zOf]; omega) (by dsimp [w, zOf]; omega)
    by_cases hdvd : M ∣ d
    · rcases hdvd with ⟨q, rfl⟩
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with rfl | hpos
        · simp at hd1
        · exact hpos
      have hq_le1 : q ≤ 1 := by
        by_contra hq2
        have hq2' : 2 ≤ q := by omega
        have hMq : M * 2 ≤ M * q := Nat.mul_le_mul_left M hq2'
        have hpMq : p * (M * 2) ≤ p * (M * q) := Nat.mul_le_mul_left p hMq
        have hpM2 : p * (M * 2) = p * M + p * M := by ring
        omega
      have hq_eq : q = 1 := by omega
      subst hq_eq
      rw [mul_one] at hlast
      have ha₀_le_p : a₀ ≤ p := by omega
      have h2pM : 2 * M ≤ p * M := Nat.mul_le_mul_right M hp2
      have hm1_lo : aL + 1 ≤ a₀ + M := by omega
      have hm1_hi : a₀ + M ≤ aL + p * M := by omega
      have hcol1 : col (a₀ + M) = 0 := by
        have h1 := hmono 1 (by omega)
        simpa using h1
      have hf1 : f (zOf (a₀ + M)) = 1 := by
        have hzeq : zOf (a₀ + M) = zOf a₀ + 1 * (M : ℤ) := by
          dsimp [zOf]; omega
        rw [hzeq, hf_per (zOf a₀) 1]
        exact hf_win (zOf a₀) (by dsimp [zOf]; omega) (by dsimp [zOf]; omega)
      have hcol1_one := hcol_eq_one_of (a₀ + M) hm1_lo hm1_hi hf1
      rw [hcol1] at hcol1_one
      exact Fin.zero_ne_one hcol1_one
    · have hm1_ge : aL + 1 ≤ a₀ + d := by
        by_contra hlt
        have hm1_le : a₀ + d ≤ aL := by omega
        have hd_le : d ≤ aL - 1 := by omega
        let q : ℕ := (aL - a₀) / d
        let r : ℕ := (aL - a₀) % d
        have hdiv : d * q + r = aL - a₀ := Nat.div_add_mod (aL - a₀) d
        have hr_lt : r < d := Nat.mod_lt _ (by omega)
        have hq_lt_p : q < p := by
          have h1 : q ≤ aL - a₀ := Nat.div_le_self _ _
          omega
        let k : ℕ := q + 1
        have hk_le : k ≤ p := by omega
        have hmk_eq : a₀ + k * d = aL + d - r := by
          have hkd : k * d = d * q + d := by dsimp [k]; ring
          omega
        have hc1 := hbar_left (a₀ + k * d) (by omega) (by omega)
        have hc0 := hmono k hk_le
        rw [hc0] at hc1
        exact Fin.zero_ne_one hc1
      have hmp1_le : a₀ + (p - 1) * d ≤ aL + p * M := by
        by_contra hgt
        have hm_hi : aL + p * M + 1 ≤ a₀ + (p - 1) * d := by omega
        have hmp_eq : a₀ + p * d = a₀ + (p - 1) * d + d := by
          have hp1 : (p - 1) + 1 = p := by omega
          calc a₀ + p * d = a₀ + ((p - 1) + 1) * d := by rw [hp1]
            _ = a₀ + (p - 1) * d + d := by ring
        have hd_le_aR : d ≤ aR - 1 := by omega
        have hd_le_aL : d ≤ aL := by omega
        have hp_le_pd : p ≤ p * d := Nat.le_mul_of_pos_right p (by omega)
        have ha₀_le : a₀ ≤ p * M := by omega
        let s : ℕ := (aL + p * M - a₀) / d
        let r : ℕ := (aL + p * M - a₀) % d
        have hdiv : d * s + r = aL + p * M - a₀ := Nat.div_add_mod (aL + p * M - a₀) d
        have hr_lt : r < d := Nat.mod_lt _ (by omega)
        have hs_lt : s < p - 1 := by
          by_contra hs_ge
          have hs_ge' : p - 1 ≤ s := by omega
          have hmul : (p - 1) * d ≤ s * d := Nat.mul_le_mul_right d hs_ge'
          have hsd : s * d = d * s := mul_comm s d
          omega
        have hs_le : s ≤ p := by omega
        have hms_eq : a₀ + s * d = aL + p * M - r := by
          have hsd : s * d = d * s := mul_comm s d
          omega
        have hc1 := hbar_right (a₀ + s * d) (by omega) (by omega)
        have hc0 := hmono s hs_le
        rw [hc0] at hc1
        exact Fin.zero_ne_one hc1
      have hor : aL + 1 ≤ a₀ ∨ a₀ + p * d ≤ aL + p * M := by
        by_contra hboth
        push Not at hboth
        rcases hboth with ⟨h1, h2⟩
        have hpd : p * M + 1 ≤ p * d := by omega
        have hd_gt_M : M < d := by
          by_contra hd_le_M
          have hmul : p * d ≤ p * M := Nat.mul_le_mul_left p (by omega)
          omega
        have hmul2 : p * (M + 1) ≤ p * d := Nat.mul_le_mul_left p (by omega)
        have hpM1 : p * (M + 1) = p * M + p := by ring
        omega
      rcases hor with ha₀_mid | hmp_mid
      · refine hf_no0 (zOf a₀) d hdvd (fun i => ?_)
        have hi_le : (i : ℕ) ≤ p - 1 := by omega
        have hid_le : (i : ℕ) * d ≤ (p - 1) * d := Nat.mul_le_mul_right d hi_le
        have hlo : aL + 1 ≤ a₀ + (i : ℕ) * d := by omega
        have hhi : a₀ + (i : ℕ) * d ≤ aL + p * M := by omega
        have hc0 := hmono (i : ℕ) (by omega)
        have hfz := hf_eq_zero_of_col_zero (a₀ + (i : ℕ) * d) hlo hhi hc0
        have hzeq : zOf (a₀ + (i : ℕ) * d) = zOf a₀ + (i : ℕ) * (d : ℤ) := by
          dsimp [zOf]; ring
        rwa [hzeq] at hfz
      · refine hf_no0 (zOf (a₀ + d)) d hdvd (fun i => ?_)
        have hidx : a₀ + d + (i : ℕ) * d = a₀ + ((i : ℕ) + 1) * d := by ring
        have hi1_le : (i : ℕ) + 1 ≤ p := by omega
        have h1_le_i1 : 1 ≤ (i : ℕ) + 1 := by omega
        have hd_le_i1d : d ≤ ((i : ℕ) + 1) * d := by simpa using Nat.mul_le_mul_right d h1_le_i1
        have hi1d_le_pd : ((i : ℕ) + 1) * d ≤ p * d := Nat.mul_le_mul_right d hi1_le
        have hlo : aL + 1 ≤ a₀ + ((i : ℕ) + 1) * d := by omega
        have hhi : a₀ + ((i : ℕ) + 1) * d ≤ aL + p * M := by omega
        have hc0 := hmono ((i : ℕ) + 1) hi1_le
        have hfz := hf_eq_zero_of_col_zero (a₀ + ((i : ℕ) + 1) * d) hlo hhi hc0
        have hzeq : zOf (a₀ + ((i : ℕ) + 1) * d) = zOf (a₀ + d) + (i : ℕ) * (d : ℤ) := by
          rw [← hidx]; dsimp [zOf]; ring
        rwa [hzeq] at hfz
  · -- Case `c = 1`
    have hall_mid : ∀ j ≤ p,
        aL + 1 ≤ a₀ + j * d ∧ a₀ + j * d ≤ aL + p * M ∧ f (zOf (a₀ + j * d)) = 1 := by
      intro j hj
      have hc1 := hmono j hj
      dsimp [col] at hc1
      split_ifs at hc1 with hmid hL0
      · exact absurd hc1 (by decide)
      · rcases zmod2_eq_zero_or_one (f (zOf (a₀ + j * d))) with hz0 | hz1
        · exact absurd hz0 hL0
        · exact ⟨hmid.1, hmid.2, hz1⟩
      · exact absurd hc1 (by decide)
    have h0 := (hall_mid 0 (by omega)).1
    have hp_hi := (hall_mid p (le_refl p)).2.1
    have hd_lt_M : d < M := by
      by_contra hge
      have hmul : p * M ≤ p * d := Nat.mul_le_mul_left p (by omega)
      omega
    have hndvd : ¬ (M ∣ d) := Nat.not_dvd_of_pos_of_lt (by omega) hd_lt_M
    refine hf_no1 (zOf a₀) d hndvd (fun j hj => ?_)
    have hfz := (hall_mid j hj).2.2
    have hzeq : zOf (a₀ + j * d) = zOf a₀ + (j : ℤ) * (d : ℤ) := by
      dsimp [zOf]; ring
    rwa [hzeq] at hfz

lemma berlekamp_no_mono_ap (p : ℕ) (hp : p.Prime) :
    ∃ col : ℕ → Fin 2,
      ∀ (c : Fin 2) (a₀ d : ℕ), 1 ≤ d → 1 ≤ a₀ → a₀ + p * d ≤ p * 2 ^ p →
        ¬ (∀ j ≤ p, col (a₀ + j * d) = c) := by
  obtain ⟨f, hf_win, hf_per, hf_no0, hf_no1⟩ := exists_berlekamp_periodic_func p hp
  have hp2 : 2 ≤ p := hp.two_le
  have hpM : p + 1 ≤ 2 ^ p - 1 := p_add_one_le_two_pow_sub_one hp2
  have hM1 : (2 ^ p - 1) + 1 = 2 ^ p := by
    have hpos : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by decide)
    omega
  have htotal : (p / 2) + p * (2 ^ p - 1) + (p - p / 2) = p * 2 ^ p := by
    have haLR : (p / 2) + (p - p / 2) = p := by omega
    calc (p / 2) + p * (2 ^ p - 1) + (p - p / 2)
      _ = p * (2 ^ p - 1) + ((p / 2) + (p - p / 2)) := by ring
      _ = p * (2 ^ p - 1) + p := by rw [haLR]
      _ = p * ((2 ^ p - 1) + 1) := by ring
      _ = p * 2 ^ p := by rw [hM1]
  obtain ⟨col, hcol⟩ := berlekamp_comb_aux p (2 ^ p - 1) (p / 2) (p - p / 2)
    hp2 hpM (by omega) (by omega) (by omega) f hf_win hf_per hf_no0 hf_no1
  exact ⟨col, fun c a₀ d hd1 ha₀1 hlast => hcol c a₀ d hd1 ha₀1 (htotal.symm ▸ hlast)⟩

end OMAErdos138Prime

theorem OMA.solution : type_of% @Erdos138.erdos_138.variants.prime := by
  classical
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨col, hcol⟩ := OMAErdos138Prime.berlekamp_no_mono_ap p hp
  refine le_csInf (OMAErdos138Prime.guarantee_nonempty 2 (p + 1)) ?_
  intro N hN
  by_contra hlt
  have hN_le : N ≤ p * 2 ^ p := by omega
  obtain ⟨c, ap, hap_len, hap_mono⟩ := hN (fun x : Finset.Icc 1 N => col x.1)
  let S : Set ℕ := Subtype.val '' ap
  have hS_ap : S.IsAPOfLength ((p + 1 : ℕ) : ℕ∞) := hap_len
  rcases hap_len with ⟨a₀, d, hcard, hset⟩
  have hS_sub : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N ∧ col x = c := by
    rintro x ⟨m, hm, rfl⟩
    have hmIcc := Finset.mem_Icc.mp m.2
    exact ⟨hmIcc.1, hmIcc.2, hap_mono m hm⟩
  have hmem_S : ∀ j ≤ p, a₀ + j * d ∈ S := by
    intro j hj
    change a₀ + j * d ∈ Subtype.val '' ap
    rw [hset]
    refine ⟨j, ?_, by simp⟩
    exact_mod_cast Nat.lt_succ_of_le hj
  have hd_pos : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · have hS_eq : S = {a₀} := by
        ext x
        constructor
        · intro hx
          change x ∈ Subtype.val '' ap at hx
          rw [hset] at hx
          rcases hx with ⟨n, _, rfl⟩
          simp
        · intro hx
          rw [Set.mem_singleton_iff] at hx
          subst hx
          simpa using hmem_S 0 (by omega)
      have hS_one : S.IsAPOfLength 1 := ⟨a₀, 0, Set.IsAPOfLengthWith.one.mpr hS_eq⟩
      have heq : ((p + 1 : ℕ) : ℕ∞) = 1 := hS_ap.congr hS_one
      have hp_bad : p + 1 = 1 := by exact_mod_cast heq
      omega
    · exact hpos
  have ha₀1 : 1 ≤ a₀ := by
    have h0 := (hS_sub _ (hmem_S 0 (by omega))).1
    simpa using h0
  have hlast : a₀ + p * d ≤ p * 2 ^ p :=
    ((hS_sub _ (hmem_S p (le_refl p))).2.1).trans hN_le
  exact hcol c a₀ d hd_pos ha₀1 hlast (fun j hj => (hS_sub _ (hmem_S j hj)).2.2)
