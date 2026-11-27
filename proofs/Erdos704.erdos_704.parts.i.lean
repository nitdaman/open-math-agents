import FormalConjectures.ErdosProblems.«704»
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Bertrand

/-!
# Erdős Problem 704 (Part i): Exponential growth of `χ(G_n)`

We prove that the chromatic number of the unit distance graph on `ℝⁿ` grows exponentially in `n`:
1. **Exponential lower bound** (Frankl–Wilson 1981): using `ZMod p`-linear independence of
   indicator-product functions on `(2p - 1)`-subsets of `Fin (4p - 1)` avoiding intersection size
   `p - 1`, together with Bertrand's postulate, we show `1.05 ^ n ≤ k` for every `k`-coloring of
   `unitDistanceGraph n` for all sufficiently large `n`.
2. **Exponential upper bound**: using Zorn's lemma to construct a maximal `1/2`-separated net in
   `ℝⁿ`, Lebesgue volume packing to show every net point has fewer than `9 ^ n` net neighbors
   within distance `2` and that the net is countable, and greedy coloring along a countable
   enumeration, we show `unitDistanceGraph n` is `9 ^ n`-colorable for every `n`.
-/

open Filter Finset MeasureTheory Metric Set

namespace OMAErdos704

/- ### Part 1: Frankl–Wilson exponential lower bound -/

section LowerBound

/-- Subset indicator function on a family `F` over `ZMod p`: `e_S(B) = 1` if `S ⊆ B`, else `0`. -/
private def subInd {m p : ℕ} (F : Finset (Finset (Fin m))) (S : Finset (Fin m)) :
    {B // B ∈ F} → ZMod p :=
  fun B => if S ⊆ B.1 then 1 else 0

private lemma subInd_mul {m p : ℕ} (F : Finset (Finset (Fin m)))
    (S T : Finset (Fin m)) :
    subInd (p := p) F S * subInd (p := p) F T = subInd (p := p) F (S ∪ T) := by
  ext B
  simp only [Pi.mul_apply, subInd, Finset.union_subset_iff]
  split_ifs <;> simp_all

/-- The intersection-size function `B ↦ |(A ∩ B)| mod p` equals the sum of singleton indicators. -/
private lemma card_inter_eq_sum_subInd {m p : ℕ} (F : Finset (Finset (Fin m)))
    (A : Finset (Fin m)) :
    (fun B : {B // B ∈ F} => ((A ∩ B.1).card : ZMod p)) =
      ∑ a ∈ A, subInd (p := p) F {a} := by
  ext B
  simp only [Finset.sum_apply, subInd, Finset.singleton_subset_iff, Finset.sum_boole]
  congr 1

/-- Subspace of `F → ZMod p` spanned by indicators `e_S` with `|S| ≤ d`. -/
private def spanSubInd (m p : ℕ) (F : Finset (Finset (Fin m))) (d : ℕ) :
    Submodule (ZMod p) ({B // B ∈ F} → ZMod p) :=
  Submodule.span (ZMod p)
    ((Finset.univ.filter (fun S : Finset (Fin m) => S.card ≤ d)).image (subInd (p := p) F) :
      Set ({B // B ∈ F} → ZMod p))

private lemma spanSubInd_mono {m p : ℕ} (F : Finset (Finset (Fin m))) {d₁ d₂ : ℕ}
    (hd : d₁ ≤ d₂) :
    spanSubInd m p F d₁ ≤ spanSubInd m p F d₂ := by
  apply Submodule.span_mono
  intro v hv
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨S, hS, rfl⟩ := hv
  exact ⟨S, hS.trans hd, rfl⟩

private lemma mul_subInd_singleton_mem_spanSubInd {m p : ℕ} (F : Finset (Finset (Fin m)))
    {d : ℕ} {v : {B // B ∈ F} → ZMod p} (hv : v ∈ spanSubInd m p F d) (a : Fin m) :
    v * subInd (p := p) F {a} ∈ spanSubInd m p F (d + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨S, hS, rfl⟩ := hu
    rw [subInd_mul]
    apply Submodule.subset_span
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨S ∪ {a}, ?_, rfl⟩
    calc (S ∪ {a}).card ≤ S.card + ({a} : Finset (Fin m)).card := Finset.card_union_le S {a}
      _ = S.card + 1 := by simp
      _ ≤ d + 1 := Nat.add_le_add_right hS 1
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r hx

/-- The Frankl–Wilson polynomial function `f_A(B) = ∏_{j < k} (|A ∩ B| - j)` lies in `U_k`. -/
private lemma prod_inter_sub_mem_spanSubInd {m p : ℕ} (F : Finset (Finset (Fin m)))
    (A : Finset (Fin m)) (k : ℕ) :
    (fun B : {B // B ∈ F} =>
      ∏ j ∈ Finset.range k, (((A ∩ B.1).card : ZMod p) - (j : ZMod p))) ∈
      spanSubInd m p F k := by
  induction k with
  | zero =>
    have h1 : (fun _ : {B // B ∈ F} => (1 : ZMod p)) = subInd (p := p) F ∅ := by
      ext B; simp [subInd]
    simp only [Finset.range_zero, Finset.prod_empty]
    rw [h1]
    apply Submodule.subset_span
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨∅, by simp, rfl⟩
  | succ k ih =>
    have heq :
        (fun B : {B // B ∈ F} =>
          ∏ j ∈ Finset.range (k + 1), (((A ∩ B.1).card : ZMod p) - (j : ZMod p))) =
        (∑ a ∈ A, (fun B : {B // B ∈ F} =>
          ∏ j ∈ Finset.range k, (((A ∩ B.1).card : ZMod p) - (j : ZMod p))) *
            subInd (p := p) F {a}) -
        (k : ZMod p) • (fun B : {B // B ∈ F} =>
          ∏ j ∈ Finset.range k, (((A ∩ B.1).card : ZMod p) - (j : ZMod p))) := by
      ext B
      rw [Finset.prod_range_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
      have hcard : ((A ∩ B.1).card : ZMod p) = ∑ a ∈ A, subInd (p := p) F {a} B := by
        simpa using congr_fun (card_inter_eq_sum_subInd (p := p) F A) B
      rw [mul_sub]
      congr 1
      · rw [hcard, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [Pi.mul_apply, hcard]
      · exact mul_comm _ _
    rw [heq]
    apply Submodule.sub_mem
    · apply Submodule.sum_mem
      intro a _
      exact mul_subInd_singleton_mem_spanSubInd F ih a
    · apply Submodule.smul_mem
      exact spanSubInd_mono F (Nat.le_succ k) ih

/-- **Frankl–Wilson modular intersection bound** for `(2p - 1)`-subsets of `Fin (4p - 1)`
avoiding intersection size `p - 1`. -/
private lemma frankl_wilson_bound {p : ℕ} [hp : Fact p.Prime]
    (F : Finset (Finset (Fin (4 * p - 1))))
    (hcard : ∀ A ∈ F, A.card = 2 * p - 1)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ p - 1) :
    F.card ≤ ∑ r ∈ Finset.range p, (4 * p - 1).choose r := by
  have hp2 : 2 ≤ p := hp.out.two_le
  -- Show that `spanSubInd (4*p - 1) p F (p - 1)` equals `⊤`
  have htop : spanSubInd (4 * p - 1) p F (p - 1) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg_sum : g = ∑ A : {B // B ∈ F}, g A • Pi.single A (1 : ZMod p) := by
      ext B
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hg_sum]
    apply Submodule.sum_mem
    intro A _
    apply Submodule.smul_mem
    let fA : {B // B ∈ F} → ZMod p := fun B =>
      ∏ j ∈ Finset.range (p - 1), (((A.1 ∩ B.1).card : ZMod p) - (j : ZMod p))
    have hfA_mem : fA ∈ spanSubInd (4 * p - 1) p F (p - 1) :=
      prod_inter_sub_mem_spanSubInd F A.1 (p - 1)
    have hfA_self : fA A ≠ 0 := by
      dsimp only [fA]
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.inter_self, hcard A.1 A.2]
      intro heq
      have hmod : (2 * p - 1) % p = j % p := by
        have h1 : ((2 * p - 1 : ℕ) : ZMod p) = (j : ZMod p) := sub_eq_zero.mp heq
        exact (ZMod.natCast_eq_natCast_iff' _ _ p).mp h1
      have h1 : (2 * p - 1) % p = p - 1 := by
        have hsplit : 2 * p - 1 = (p - 1) + p := by omega
        rw [hsplit, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h2 : j % p = j := Nat.mod_eq_of_lt (by omega)
      omega
    have hfA_other : ∀ B : {B // B ∈ F}, B ≠ A → fA B = 0 := by
      intro B hBA
      dsimp only [fA]
      rw [Finset.prod_eq_zero_iff]
      have hne_inter : (A.1 ∩ B.1).card ≠ p - 1 := hinter A.1 A.2 B.1 B.2
      have hlt_card : (A.1 ∩ B.1).card < 2 * p - 1 := by
        have hle : (A.1 ∩ B.1).card ≤ A.1.card := Finset.card_le_card Finset.inter_subset_left
        rw [hcard A.1 A.2] at hle
        rcases hle.lt_or_eq with hlt | heq
        · exact hlt
        · exfalso
          have hsub1 : A.1 ∩ B.1 = A.1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
            (by rw [heq, hcard A.1 A.2])
          have hAB : A.1 ⊆ B.1 := by rw [← hsub1]; exact Finset.inter_subset_right
          have hEq : A.1 = B.1 := Finset.eq_of_subset_of_card_le hAB
            (by rw [hcard A.1 A.2, hcard B.1 B.2])
          exact hBA (Subtype.ext hEq.symm)
      have hmod_lt : (A.1 ∩ B.1).card % p < p - 1 := by
        have hltp : (A.1 ∩ B.1).card % p < p := Nat.mod_lt _ (by omega)
        by_contra hge
        have hmod_eq : (A.1 ∩ B.1).card % p = p - 1 := by omega
        have hdm : p * ((A.1 ∩ B.1).card / p) + (A.1 ∩ B.1).card % p = (A.1 ∩ B.1).card :=
          Nat.div_add_mod (A.1 ∩ B.1).card p
        rcases Nat.lt_trichotomy ((A.1 ∩ B.1).card / p) 1 with h0 | h1 | h2
        · have hq0 : (A.1 ∩ B.1).card / p = 0 := Nat.lt_one_iff.mp h0
          rw [hq0, mul_zero, zero_add, hmod_eq] at hdm; omega
        · rw [h1, mul_one, hmod_eq] at hdm; omega
        · have : p * 2 ≤ p * ((A.1 ∩ B.1).card / p) := Nat.mul_le_mul_left p h2
          omega
      refine ⟨(A.1 ∩ B.1).card % p, Finset.mem_range.mpr hmod_lt, ?_⟩
      rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff']
      simp
    have hsingle : Pi.single A (1 : ZMod p) = (fA A)⁻¹ • fA := by
      ext B
      by_cases hBA : B = A
      · subst hBA
        simp [inv_mul_cancel₀ hfA_self]
      · simp [hBA, hfA_other B hBA]
    rw [hsingle]
    exact Submodule.smul_mem _ _ hfA_mem
  -- Compare finranks
  let genFinset : Finset (Finset (Fin (4 * p - 1))) :=
    Finset.univ.filter (fun S : Finset (Fin (4 * p - 1)) => S.card ≤ p - 1)
  have hfinrank_le : Module.finrank (ZMod p) ({B // B ∈ F} → ZMod p) ≤
      (genFinset.image (subInd (p := p) F)).card := by
    let img : Finset ({B // B ∈ F} → ZMod p) := genFinset.image (subInd (p := p) F)
    have h1 := finrank_span_le_card (R := ZMod p) (img : Set ({B // B ∈ F} → ZMod p))
    have hcard_eq : (img : Set ({B // B ∈ F} → ZMod p)).toFinset = img := by
      ext x; simp
    rw [hcard_eq] at h1
    have hspan_eq : Submodule.span (ZMod p) (img : Set ({B // B ∈ F} → ZMod p)) =
        spanSubInd (4 * p - 1) p F (p - 1) := by
      congr 1
    have h2 : Module.finrank (ZMod p) (spanSubInd (4 * p - 1) p F (p - 1)) =
        Module.finrank (ZMod p) ({B // B ∈ F} → ZMod p) := by
      rw [htop]
      exact finrank_top (ZMod p) ({B // B ∈ F} → ZMod p)
    rw [← h2, ← hspan_eq]
    exact h1
  have hlhs : Module.finrank (ZMod p) ({B // B ∈ F} → ZMod p) = F.card := by
    simp [Fintype.card_coe]
  have hrhs_img : (genFinset.image (subInd (p := p) F)).card ≤ genFinset.card :=
    Finset.card_image_le
  have hgen_card : genFinset.card = ∑ r ∈ Finset.range p, (4 * p - 1).choose r := by
    have hdisj : genFinset = (Finset.range p).biUnion
        (fun r => (Finset.univ : Finset (Fin (4 * p - 1))).powersetCard r) := by
      ext S
      simp only [genFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ]
      constructor
      · intro h; exact ⟨S.card, by omega, rfl⟩
      · rintro ⟨r, hr, rfl⟩; omega
    rw [hdisj, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp [Finset.card_powersetCard]
    · intro r₁ _ r₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro S h1 h2
      simp only [Finset.mem_powersetCard] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  omega

/-- Pure `ℕ` binomial inequality combining the lower bound on `C(4p - 1, 2p - 1)` and the upper
bound on `∑_{r < p} C(4p - 1, r)`. -/
private lemma nat_exp_bound_of_choose_le {p k : ℕ} (hp : 1 ≤ p)
    (h : (4 * p - 1).choose (2 * p - 1) ≤ k * ∑ r ∈ Finset.range p, (4 * p - 1).choose r) :
    27 ^ p ≤ 2 * p * k * 16 ^ p := by
  -- 1. Lower bound on central binomial coefficient: 2^(4p - 1) ≤ 4p * C(4p - 1, 2p - 1)
  have hcentral : 2 ^ (4 * p - 1) ≤ 4 * p * (4 * p - 1).choose (2 * p - 1) := by
    have hsum : ∑ r ∈ Finset.range (4 * p), (4 * p - 1).choose r = 2 ^ (4 * p - 1) := by
      have := Nat.sum_range_choose (4 * p - 1)
      have hsucc : 4 * p - 1 + 1 = 4 * p := by omega
      rwa [hsucc] at this
    rw [← hsum]
    calc ∑ r ∈ Finset.range (4 * p), (4 * p - 1).choose r
        ≤ ∑ _r ∈ Finset.range (4 * p), (4 * p - 1).choose (2 * p - 1) := by
          refine Finset.sum_le_sum fun r _ => ?_
          have hmid : (4 * p - 1) / 2 = 2 * p - 1 := by omega
          rw [← hmid]
          exact Nat.choose_le_middle r (4 * p - 1)
      _ = 4 * p * (4 * p - 1).choose (2 * p - 1) := by simp
  -- 2. Upper bound on tail sum: 3^(3p) * ∑_{r < p} C(4p - 1, r) ≤ 4^(4p - 1)
  have htail : 3 ^ (3 * p) * ∑ r ∈ Finset.range p, (4 * p - 1).choose r ≤ 4 ^ (4 * p - 1) := by
    rw [Finset.mul_sum]
    calc ∑ r ∈ Finset.range p, 3 ^ (3 * p) * (4 * p - 1).choose r
        ≤ ∑ r ∈ Finset.range p, 3 ^ (4 * p - 1 - r) * (4 * p - 1).choose r := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [Finset.mem_range] at hr
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ ∑ r ∈ Finset.range (4 * p), 3 ^ (4 * p - 1 - r) * (4 * p - 1).choose r := by
          refine Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      _ = (1 + 3) ^ (4 * p - 1) := by
          rw [add_pow]
          have hsucc : 4 * p - 1 + 1 = 4 * p := by omega
          rw [hsucc]
          refine Finset.sum_congr rfl fun r _ => by simp [mul_comm]
      _ = 4 ^ (4 * p - 1) := by norm_num
  -- 3. Combine and cancel 2^(4p - 1)
  have hcomb : 2 ^ (4 * p - 1) * 3 ^ (3 * p) ≤ 4 * p * k * 4 ^ (4 * p - 1) := by
    calc 2 ^ (4 * p - 1) * 3 ^ (3 * p)
        ≤ (4 * p * (4 * p - 1).choose (2 * p - 1)) * 3 ^ (3 * p) :=
          Nat.mul_le_mul_right _ hcentral
      _ ≤ (4 * p * (k * ∑ r ∈ Finset.range p, (4 * p - 1).choose r)) * 3 ^ (3 * p) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)
      _ = 4 * p * k * (3 ^ (3 * p) * ∑ r ∈ Finset.range p, (4 * p - 1).choose r) := by ring
      _ ≤ 4 * p * k * 4 ^ (4 * p - 1) := Nat.mul_le_mul_left _ htail
  have h4pow : 4 ^ (4 * p - 1) = 2 ^ (4 * p - 1) * 2 ^ (4 * p - 1) := by
    rw [← mul_pow]; norm_num
  have hcancel : 3 ^ (3 * p) ≤ 4 * p * k * 2 ^ (4 * p - 1) := by
    have hpos : 0 < 2 ^ (4 * p - 1) := pow_pos (by omega) _
    rw [h4pow] at hcomb
    have hcomb' : 2 ^ (4 * p - 1) * 3 ^ (3 * p) ≤ 2 ^ (4 * p - 1) * (4 * p * k * 2 ^ (4 * p - 1)) := by
      linarith
    exact Nat.le_of_mul_le_mul_left hcomb' hpos
  have h27 : 3 ^ (3 * p) = 27 ^ p := by rw [pow_mul]; norm_num
  have h16 : 4 * p * k * 2 ^ (4 * p - 1) = 2 * p * k * 16 ^ p := by
    have h2pow : 2 * 2 ^ (4 * p - 1) = 16 ^ p := by
      have : 2 ^ (4 * p) = 16 ^ p := by rw [pow_mul]; norm_num
      rw [← this]
      have hsucc : 4 * p = (4 * p - 1) + 1 := by omega
      conv_rhs => rw [hsucc, pow_succ]
      ring
    calc 4 * p * k * 2 ^ (4 * p - 1)
        = 2 * p * k * (2 * 2 ^ (4 * p - 1)) := by ring
      _ = 2 * p * k * 16 ^ p := by rw [h2pow]
  omega

/-- Embedding of subsets of `Fin (4p - 1)` into `EuclideanSpace ℝ (Fin n)` with scale `1/√(2p)`. -/
private noncomputable def embedSubset (p n : ℕ) (A : Finset (Fin (4 * p - 1))) :
    EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm fun i =>
    if hi : (i : ℕ) < 4 * p - 1 then
      if (⟨i, hi⟩ : Fin (4 * p - 1)) ∈ A then (Real.sqrt (2 * p : ℝ))⁻¹ else 0
    else 0

private lemma dist_embedSubset_eq_one {p n : ℕ} (hp : 1 ≤ p) (hpn : 4 * p - 1 ≤ n)
    {A B : Finset (Fin (4 * p - 1))}
    (hA : A.card = 2 * p - 1) (hB : B.card = 2 * p - 1)
    (hAB : (A ∩ B).card = p - 1) :
    dist (embedSubset p n A) (embedSubset p n B) = 1 := by
  have hp_pos : (0 : ℝ) < 2 * (p : ℝ) := by positivity
  have hdist_sq : dist (embedSubset p n A) (embedSubset p n B) ^ 2 = 1 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have hsplit :
        ∑ i : Fin n, dist (embedSubset p n A i) (embedSubset p n B i) ^ 2 =
        ∑ j : Fin (4 * p - 1),
          (if (j ∈ A ∧ j ∉ B) ∨ (j ∉ A ∧ j ∈ B) then ((2 * (p : ℝ))⁻¹) else 0) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < 4 * p - 1)]
      have hzero :
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < 4 * p - 1),
            dist (embedSubset p n A i) (embedSubset p n B i) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [embedSubset, hi]
      rw [hzero, add_zero]
      refine Finset.sum_bij (fun i hi => ⟨i.1, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
      · intro i hi; exact Finset.mem_univ _
      · intro i₁ _ i₂ _ h
        ext
        exact congr_arg (Fin.val : Fin (4 * p - 1) → ℕ) h
      · intro j _
        refine ⟨⟨j.1, lt_of_lt_of_le j.2 hpn⟩, ?_, by ext; rfl⟩
        simp [j.2]
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        set j : Fin (4 * p - 1) := ⟨i.1, hi⟩
        have hcoordA : embedSubset p n A i =
            if j ∈ A then (Real.sqrt (2 * (p : ℝ)))⁻¹ else 0 := by
          simp [embedSubset, hi, j]
        have hcoordB : embedSubset p n B i =
            if j ∈ B then (Real.sqrt (2 * (p : ℝ)))⁻¹ else 0 := by
          simp [embedSubset, hi, j]
        rw [hcoordA, hcoordB]
        by_cases hjA : j ∈ A <;> by_cases hjB : j ∈ B
        · simp [hjA, hjB]
        · simp only [hjA, hjB, ↓reduceIte, not_false_eq_true, and_self, true_or, dist_zero_right,
            Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hp_pos.le]
        · simp only [hjA, hjB, ↓reduceIte, not_false_eq_true, and_self, or_true, dist_zero_left,
            Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hp_pos.le]
        · simp [hjA, hjB]
    rw [hsplit]
    have hfilter_card :
        (Finset.univ.filter (fun j : Fin (4 * p - 1) =>
          (j ∈ A ∧ j ∉ B) ∨ (j ∉ A ∧ j ∈ B))).card = 2 * p := by
      have heq : Finset.univ.filter (fun j : Fin (4 * p - 1) =>
          (j ∈ A ∧ j ∉ B) ∨ (j ∉ A ∧ j ∈ B)) = (A \ B) ∪ (B \ A) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
        tauto
      rw [heq, Finset.card_union_of_disjoint]
      · have h1 := Finset.card_sdiff_add_card_inter A B
        have h2 := Finset.card_sdiff_add_card_inter B A
        rw [Finset.inter_comm] at h2
        omega
      · rw [Finset.disjoint_left]
        intro j hj1 hj2
        simp only [Finset.mem_sdiff] at hj1 hj2
        exact hj1.2 hj2.1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      hfilter_card]
    push_cast
    exact mul_inv_cancel₀ hp_pos.ne'
  nlinarith [dist_nonneg (x := embedSubset p n A) (y := embedSubset p n B)]

/-- For a prime `p` with `4p - 1 ≤ n`, every `k`-coloring of `unitDistanceGraph n` satisfies
`27 ^ p ≤ 2 * p * k * 16 ^ p`. -/
private lemma coloring_bound_prime {p n k : ℕ} (hp : p.Prime) (hpn : 4 * p - 1 ≤ n)
    (hcol : (Erdos704.unitDistanceGraph n).Colorable k) :
    27 ^ p ≤ 2 * p * k * 16 ^ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨col⟩ := hcol
  let V : Finset (Finset (Fin (4 * p - 1))) :=
    (Finset.univ : Finset (Fin (4 * p - 1))).powersetCard (2 * p - 1)
  have hV_card : V.card = (4 * p - 1).choose (2 * p - 1) := by
    simp [V, Finset.card_powersetCard]
  have hfiber : ∀ c : Fin k,
      (V.filter (fun A => col (embedSubset p n A) = c)).card ≤
        ∑ r ∈ Finset.range p, (4 * p - 1).choose r := by
    intro c
    apply frankl_wilson_bound
    · intro A hA
      simp only [V, Finset.mem_filter, Finset.mem_powersetCard] at hA
      exact hA.1.2
    · intro A hA B hB hAB
      simp only [V, Finset.mem_filter, Finset.mem_powersetCard] at hA hB
      have hadj : (Erdos704.unitDistanceGraph n).Adj (embedSubset p n A) (embedSubset p n B) :=
        dist_embedSubset_eq_one hp.one_le hpn hA.1.2 hB.1.2 hAB
      exact col.valid hadj (hA.2.trans hB.2.symm)
  have hsum : V.card ≤ k * ∑ r ∈ Finset.range p, (4 * p - 1).choose r := by
    have hpart : V.card = ∑ c : Fin k, (V.filter (fun A => col (embedSubset p n A) = c)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext A
        simp
      · intro c₁ _ c₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro A h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hne (h1.2.symm.trans h2.2)
    rw [hpart]
    calc ∑ c : Fin k, (V.filter (fun A => col (embedSubset p n A) = c)).card
        ≤ ∑ _c : Fin k, ∑ r ∈ Finset.range p, (4 * p - 1).choose r :=
          Finset.sum_le_sum fun c _ => hfiber c
      _ = k * ∑ r ∈ Finset.range p, (4 * p - 1).choose r := by simp
  rw [hV_card] at hsum
  exact nat_exp_bound_of_choose_le hp.one_le hsum

/-- Elementary exponential-beats-polynomial bound: `(2 * n) ^ 8 ≤ (9 / 8 : ℝ) ^ n` for large `n`. -/
private lemma poly_le_exp_nine_eighths {n : ℕ} (hn : 10 ^ 19 ≤ n) :
    ((2 * (n : ℝ)) ^ 8) ≤ ((9 / 8 : ℝ) ^ n) := by
  have h1 : (9 / 8 : ℝ) = 1 / 8 + 1 := by norm_num
  rw [h1, add_pow]
  have h9 : 9 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hterm_le :
      (1 / 8 : ℝ) ^ 9 * (1 : ℝ) ^ (n - 9) * (n.choose 9 : ℝ) ≤
        ∑ m ∈ Finset.range (n + 1), (1 / 8 : ℝ) ^ m * (1 : ℝ) ^ (n - m) * (n.choose m : ℝ) :=
    Finset.single_le_sum
      (f := fun m => (1 / 8 : ℝ) ^ m * (1 : ℝ) ^ (n - m) * (n.choose m : ℝ))
      (fun m _ => by positivity) h9
  have hdesc_nat : (n - 8) ^ 9 ≤ Nat.descFactorial n 9 := by
    have hstep : ∀ k : ℕ, k ≤ 9 → (n - 8) ^ k ≤ Nat.descFactorial n k := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.descFactorial_succ, pow_succ]
        have h1 : n - 8 ≤ n - k := by omega
        calc (n - 8) ^ k * (n - 8)
            ≤ Nat.descFactorial n k * (n - k) := Nat.mul_le_mul (ih (by omega)) h1
          _ = (n - k) * Nat.descFactorial n k := mul_comm _ _
    exact hstep 9 le_rfl
  have hchoose_nat : (n - 8) ^ 9 ≤ Nat.factorial 9 * n.choose 9 := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact hdesc_nat
  have hchoose_real : ((n : ℝ) - 8) ^ 9 ≤ (Nat.factorial 9 : ℝ) * (n.choose 9 : ℝ) := by
    have hcast : (((n - 8) ^ 9 : ℕ) : ℝ) ≤ ((Nat.factorial 9 * n.choose 9 : ℕ) : ℝ) := by
      exact_mod_cast hchoose_nat
    have hsub : ((n - 8 : ℕ) : ℝ) = (n : ℝ) - 8 := Nat.cast_sub (by omega)
    simpa [Nat.cast_pow, Nat.cast_mul, hsub] using hcast
  have hn_real : (10 ^ 19 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 8 := by linarith
  have hpow9 : ((n : ℝ) / 2) ^ 9 ≤ ((n : ℝ) - 8) ^ 9 :=
    pow_le_pow_left₀ (by positivity) hhalf 9
  have hchoose_lb : ((n : ℝ) / 2) ^ 9 / 362880 ≤ (n.choose 9 : ℝ) := by
    have hfac : (Nat.factorial 9 : ℝ) = 362880 := by norm_num [Nat.factorial]
    rw [hfac] at hchoose_real
    linarith
  have hstep1 : (2 * (n : ℝ)) ^ 8 ≤ (1 / 8 : ℝ) ^ 9 * (((n : ℝ) / 2) ^ 9 / 362880) := by
    have hcoeff : (2 : ℝ) ^ 8 ≤ (n : ℝ) * ((1 / 8 : ℝ) ^ 9 * ((1 / 2 : ℝ) ^ 9 / 362880)) := by
      nlinarith
    have hn8 : 0 ≤ (n : ℝ) ^ 8 := by positivity
    calc (2 * (n : ℝ)) ^ 8
        = (2 : ℝ) ^ 8 * (n : ℝ) ^ 8 := by ring
      _ ≤ ((n : ℝ) * ((1 / 8 : ℝ) ^ 9 * ((1 / 2 : ℝ) ^ 9 / 362880))) * (n : ℝ) ^ 8 :=
          mul_le_mul_of_nonneg_right hcoeff hn8
      _ = (1 / 8 : ℝ) ^ 9 * (((n : ℝ) / 2) ^ 9 / 362880) := by ring
  calc (2 * (n : ℝ)) ^ 8
      ≤ (1 / 8 : ℝ) ^ 9 * (((n : ℝ) / 2) ^ 9 / 362880) := hstep1
    _ ≤ (1 / 8 : ℝ) ^ 9 * (n.choose 9 : ℝ) :=
        mul_le_mul_of_nonneg_left hchoose_lb (by positivity)
    _ = (1 / 8 : ℝ) ^ 9 * (1 : ℝ) ^ (n - 9) * (n.choose 9 : ℝ) := by simp
    _ ≤ ∑ m ∈ Finset.range (n + 1), (1 / 8 : ℝ) ^ m * (1 : ℝ) ^ (n - m) * (n.choose m : ℝ) :=
        hterm_le

/-- **Exponential lower bound** for `χ(G_n)` (Frankl–Wilson 1981). -/
private lemma exponential_lower_bound :
    ∃ c > (1 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, (Erdos704.unitDistanceGraph n).Colorable k → c ^ n ≤ (k : ℝ) := by
  refine ⟨(1.05 : ℝ), by norm_num, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨10 ^ 19, fun n hn k hcol => ?_⟩
  -- Bertrand's postulate gives a prime p with n / 8 < p ≤ 2 * (n / 8)
  have hm0 : n / 8 ≠ 0 := by omega
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 8) hm0
  have hpn : 4 * p - 1 ≤ n := by omega
  have h8p : n ≤ 8 * p := by omega
  have hbound_nat : 27 ^ p ≤ 2 * p * k * 16 ^ p := coloring_bound_prime hp_prime hpn hcol
  have hbound_real : (27 : ℝ) ^ p ≤ 2 * (p : ℝ) * (k : ℝ) * (16 : ℝ) ^ p := by
    exact_mod_cast hbound_nat
  have hratio_p : (27 / 16 : ℝ) ^ p ≤ (2 * (p : ℝ)) * (k : ℝ) := by
    rw [div_pow]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (16 : ℝ) ^ p)]
    linarith
  have h2p_le : 2 * (p : ℝ) ≤ 2 * (n : ℝ) := by
    have : p ≤ n := by omega
    have : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have hratio_n : (27 / 16 : ℝ) ^ n ≤ ((2 * (n : ℝ)) * (k : ℝ)) ^ 8 := by
    have hpow_le : (27 / 16 : ℝ) ^ n ≤ (27 / 16 : ℝ) ^ (8 * p) :=
      pow_le_pow_right₀ (by norm_num) h8p
    have hpow8 : ((27 / 16 : ℝ) ^ p) ^ 8 ≤ ((2 * (p : ℝ)) * (k : ℝ)) ^ 8 :=
      pow_le_pow_left₀ (by positivity) hratio_p 8
    have h2pk : (2 * (p : ℝ)) * (k : ℝ) ≤ (2 * (n : ℝ)) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right h2p_le (by positivity)
    have hpow8' : ((2 * (p : ℝ)) * (k : ℝ)) ^ 8 ≤ ((2 * (n : ℝ)) * (k : ℝ)) ^ 8 :=
      pow_le_pow_left₀ (by positivity) h2pk 8
    calc (27 / 16 : ℝ) ^ n
        ≤ (27 / 16 : ℝ) ^ (8 * p) := hpow_le
      _ = ((27 / 16 : ℝ) ^ p) ^ 8 := by rw [mul_comm, pow_mul]
      _ ≤ ((2 * (n : ℝ)) * (k : ℝ)) ^ 8 := hpow8.trans hpow8'
  have h105_pow8 : ((1.05 : ℝ) ^ 8) ≤ 3 / 2 := by norm_num
  have hpoly : (2 * (n : ℝ)) ^ 8 ≤ (9 / 8 : ℝ) ^ n := poly_le_exp_nine_eighths hn
  have hfinal8 : ((1.05 : ℝ) ^ n) ^ 8 ≤ (k : ℝ) ^ 8 := by
    have hpos_2n : (0 : ℝ) < (2 * (n : ℝ)) ^ 8 := by positivity
    have hmul : (2 * (n : ℝ)) ^ 8 * ((1.05 : ℝ) ^ n) ^ 8 ≤ (2 * (n : ℝ)) ^ 8 * (k : ℝ) ^ 8 := by
      calc (2 * (n : ℝ)) ^ 8 * ((1.05 : ℝ) ^ n) ^ 8
          ≤ (9 / 8 : ℝ) ^ n * ((3 / 2 : ℝ) ^ n) := by
            refine mul_le_mul hpoly ?_ (by positivity) (by positivity)
            rw [← pow_mul, mul_comm, pow_mul]
            exact pow_le_pow_left₀ (by positivity) h105_pow8 n
        _ = (27 / 16 : ℝ) ^ n := by rw [← mul_pow]; norm_num
        _ ≤ ((2 * (n : ℝ)) * (k : ℝ)) ^ 8 := hratio_n
        _ = (2 * (n : ℝ)) ^ 8 * (k : ℝ) ^ 8 := by rw [mul_pow]
    exact le_of_mul_le_mul_left hmul hpos_2n
  by_contra hlt
  push Not at hlt
  have hpow_lt : (k : ℝ) ^ 8 < ((1.05 : ℝ) ^ n) ^ 8 :=
    pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
  linarith

end LowerBound

/- ### Part 2: Volumetric net packing exponential upper bound -/

section UpperBound

/-- A maximal `1/2`-separated net in `ℝⁿ` exists by Zorn's lemma and is `1/2`-covering. -/
private lemma exists_maximal_net (n : ℕ) :
    ∃ N : Set (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ N, ∀ y ∈ N, x ≠ y → (1 / 2 : ℝ) ≤ dist x y) ∧
      (∀ p : EuclideanSpace ℝ (Fin n), ∃ x ∈ N, dist p x < 1 / 2) := by
  let S : Set (Set (EuclideanSpace ℝ (Fin n))) :=
    {A | ∀ x ∈ A, ∀ y ∈ A, x ≠ y → (1 / 2 : ℝ) ≤ dist x y}
  obtain ⟨N, hN_max⟩ := zorn_subset S fun c hc hchain => by
    refine ⟨⋃₀ c, ?_, fun A hA => Set.subset_sUnion_of_mem hA⟩
    intro x hx y hy hxy
    rcases Set.mem_sUnion.mp hx with ⟨A, hAc, hxA⟩
    rcases Set.mem_sUnion.mp hy with ⟨B, hBc, hyB⟩
    rcases hchain.total hAc hBc with hAB | hBA
    · exact hc hBc x (hAB hxA) y hyB hxy
    · exact hc hAc x hxA y (hBA hyB) hxy
  have hN_sep : N ∈ S := hN_max.prop
  refine ⟨N, hN_sep, fun p => ?_⟩
  by_contra hfar
  push Not at hfar
  have hp_not : p ∉ N := by
    intro hp
    have := hfar p hp
    rw [dist_self] at this
    linarith
  have hins : insert p N ∈ S := by
    intro x hx y hy hxy
    rcases Set.mem_insert_iff.mp hx with rfl | hxN <;>
      rcases Set.mem_insert_iff.mp hy with rfl | hyN
    · exact (hxy rfl).elim
    · exact hfar y hyN
    · rw [dist_comm]; exact hfar x hxN
    · exact hN_sep x hxN y hyN hxy
  have heq : insert p N ⊆ N := hN_max.le_of_ge hins (Set.subset_insert p N)
  exact hp_not (heq (Set.mem_insert p N))

/-- Volume packing bound: any finite subset of a `1/2`-separated net lying in `ball x R`
has cardinality at most `(4 * R + 1) ^ n`. -/
private lemma net_finset_card_le {n : ℕ} {N : Set (EuclideanSpace ℝ (Fin n))}
    (hsep : ∀ u ∈ N, ∀ v ∈ N, u ≠ v → (1 / 2 : ℝ) ≤ dist u v)
    (x : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    (F : Finset (EuclideanSpace ℝ (Fin n)))
    (hF : (F : Set (EuclideanSpace ℝ (Fin n))) ⊆ N ∩ Metric.ball x R) :
    (F.card : ℝ) ≤ (4 * R + 1) ^ n := by
  have hdisj : Set.PairwiseDisjoint (F : Set (EuclideanSpace ℝ (Fin n)))
      (fun y => Metric.ball y (1 / 4 : ℝ)) := by
    intro u hu v hv huv
    rw [Function.onFun, Set.disjoint_left]
    intro z hzu hzv
    rw [Metric.mem_ball] at hzu hzv
    have hdist : (1 / 2 : ℝ) ≤ dist u v := hsep u (hF hu).1 v (hF hv).1 huv
    have htri : dist u v ≤ dist u z + dist z v := dist_triangle u z v
    rw [dist_comm u z] at htri
    linarith
  have hsub : (⋃ y ∈ F, Metric.ball y (1 / 4 : ℝ)) ⊆ Metric.ball x (R + 1 / 4) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨y, hyF, hzy⟩ := hz
    rw [Metric.mem_ball] at hzy ⊢
    have hyx : dist y x < R := (hF hyF).2
    linarith [dist_triangle z y x]
  have hvol_le :
      ∑ y ∈ F, volume (Metric.ball y (1 / 4 : ℝ)) ≤ volume (Metric.ball x (R + 1 / 4)) := by
    rw [← measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
    exact measure_mono hsub
  have hball_eq : ∀ y : EuclideanSpace ℝ (Fin n),
      volume (Metric.ball y (1 / 4 : ℝ)) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4)) :=
    fun y => Measure.addHaar_ball_center volume y (1 / 4)
  have hbig_eq : volume (Metric.ball x (R + 1 / 4)) =
      ENNReal.ofReal ((4 * R + 1) ^ n) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4)) := by
    have hrad : R + 1 / 4 = (4 * R + 1) * (1 / 4 : ℝ) := by ring
    rw [hrad, Measure.addHaar_ball_mul_of_pos volume x (by linarith : 0 < 4 * R + 1) (1 / 4)]
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
      simp [finrank_euclideanSpace]
    rw [hdim]
  simp_rw [hball_eq] at hvol_le
  rw [Finset.sum_const, nsmul_eq_mul, hbig_eq] at hvol_le
  have hpos : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4)) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) (by norm_num)).ne'
  have hlt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hle_real := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlt) hvol_le
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at hle_real
  exact le_of_mul_le_mul_right hle_real (ENNReal.toReal_pos hpos hlt)

/-- Every bounded ball intersects a `1/2`-separated net in a finite set. -/
private lemma net_inter_ball_finite {n : ℕ} {N : Set (EuclideanSpace ℝ (Fin n))}
    (hsep : ∀ u ∈ N, ∀ v ∈ N, u ≠ v → (1 / 2 : ℝ) ≤ dist u v)
    (x : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    (N ∩ Metric.ball x R).Finite := by
  by_contra hinf
  have hInf : (N ∩ Metric.ball x R).Infinite := hinf
  obtain ⟨F, hFsub, hFcard⟩ := hInf.exists_subset_card_eq (Nat.floor ((4 * R + 1) ^ n) + 1)
  have hle := net_finset_card_le hsep x hR F hFsub
  rw [hFcard] at hle
  have hfloor : (4 * R + 1) ^ n < (Nat.floor ((4 * R + 1) ^ n) + 1 : ℝ) :=
    Nat.lt_floor_add_one _
  push_cast at hle
  linarith

/-- Any `1/2`-separated net in `ℝⁿ` is countable. -/
private lemma net_countable {n : ℕ} {N : Set (EuclideanSpace ℝ (Fin n))}
    (hsep : ∀ u ∈ N, ∀ v ∈ N, u ≠ v → (1 / 2 : ℝ) ≤ dist u v) :
    N.Countable := by
  have hunion : N = ⋃ m : ℕ, N ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (m + 1 : ℝ) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_ball]
    constructor
    · intro hx
      refine ⟨Nat.floor (dist x 0), hx, ?_⟩
      exact Nat.lt_floor_add_one (dist x 0)
    · rintro ⟨_, hx, _⟩
      exact hx
  rw [hunion]
  exact Set.countable_iUnion fun m => (net_inter_ball_finite hsep 0 (by positivity)).countable

/-- Each point of a `1/2`-separated net has strictly fewer than `9 ^ n` other net points within
distance `2`. -/
private lemma net_neighbors_finite_and_card_lt {n : ℕ} {N : Set (EuclideanSpace ℝ (Fin n))}
    (hsep : ∀ u ∈ N, ∀ v ∈ N, u ≠ v → (1 / 2 : ℝ) ≤ dist u v)
    (x : N) :
    let S : Set N := {y : N | y ≠ x ∧ dist x.1 y.1 < 2}
    S.Finite ∧ ∃ (F : Finset N), (∀ y, y ∈ F ↔ y ∈ S) ∧ F.card < 9 ^ n := by
  intro S
  have hfin_amb : (N ∩ Metric.ball x.1 2).Finite := net_inter_ball_finite hsep x.1 (by norm_num)
  let F_amb : Finset (EuclideanSpace ℝ (Fin n)) := hfin_amb.toFinset
  have hF_amb_sub : (F_amb : Set (EuclideanSpace ℝ (Fin n))) ⊆ N ∩ Metric.ball x.1 2 := by
    intro y hy
    exact hfin_amb.mem_toFinset.mp hy
  have hcard_amb_real : (F_amb.card : ℝ) ≤ (4 * 2 + 1 : ℝ) ^ n :=
    net_finset_card_le hsep x.1 (by norm_num) F_amb hF_amb_sub
  have hcard_amb : F_amb.card ≤ 9 ^ n := by
    have : (F_amb.card : ℝ) ≤ ((9 ^ n : ℕ) : ℝ) := by
      simpa [Nat.cast_pow] using (show (F_amb.card : ℝ) ≤ (9 : ℝ) ^ n by norm_num at hcard_amb_real; exact hcard_amb_real)
    exact_mod_cast this
  have hx_mem : x.1 ∈ F_amb := by
    rw [hfin_amb.mem_toFinset]
    exact ⟨x.2, Metric.mem_ball_self (by norm_num)⟩
  have hS_fin : S.Finite := by
    refine (hfin_amb.preimage (Subtype.val_injective.injOn)).subset ?_
    intro y hy
    exact ⟨y.2, by rw [Metric.mem_ball, dist_comm]; exact hy.2⟩
  refine ⟨hS_fin, hS_fin.toFinset, fun y => hS_fin.mem_toFinset, ?_⟩
  have hinj_sub : hS_fin.toFinset.image Subtype.val ⊆ F_amb.erase x.1 := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hS_fin.mem_toFinset] at hy
    rw [Finset.mem_erase]
    refine ⟨fun h => hy.1 (Subtype.ext h), ?_⟩
    rw [hfin_amb.mem_toFinset]
    exact ⟨y.2, by rw [Metric.mem_ball, dist_comm]; exact hy.2⟩
  have hcard_lt : hS_fin.toFinset.card ≤ F_amb.card - 1 := by
    have h1 := Finset.card_le_card hinj_sub
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_erase_of_mem hx_mem] at h1
    exact h1
  have hpos : 0 < F_amb.card := Finset.card_pos.mpr ⟨x.1, hx_mem⟩
  omega

/-- Greedy coloring of a countable graph where every vertex has fewer than `K` neighbors. -/
private lemma greedy_coloring_countable {α : Type*} [Countable α] {adj : α → α → Prop}
    (hsym : ∀ x y, adj x y → adj y x)
    (hirr : ∀ x, ¬ adj x x)
    {K : ℕ}
    (hnb : ∀ x : α, ∃ F : Finset α, (∀ y, y ∈ F ↔ adj x y) ∧ F.card < K) :
    ∃ c : α → Fin K, ∀ x y, adj x y → c x ≠ c y := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat α
  choose nb hnb_mem hnb_card using hnb
  -- Define coloring on natural numbers by strong recursion
  let recCol : ℕ → Option (Fin K) :=
    Nat.strongRec fun m prev =>
      if h : ∃ x : α, e x = m then
        let x := Classical.choose h
        let used : Finset (Fin K) :=
          (nb x).biUnion fun y =>
            if hy : e y < m then (prev (e y) hy).toFinset else ∅
        have hused_lt : used.card < (Finset.univ : Finset (Fin K)).card := by
          calc used.card
              ≤ ∑ y ∈ nb x, (if hy : e y < m then (prev (e y) hy).toFinset else ∅).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ _y ∈ nb x, 1 := by
                refine Finset.sum_le_sum fun y _ => ?_
                split_ifs with hy
                · cases prev (e y) hy <;> simp
                · simp
            _ = (nb x).card := by simp
            _ < K := hnb_card x
            _ = (Finset.univ : Finset (Fin K)).card := by simp
        have hne : (Finset.univ \ used).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          have hsub : Finset.univ ⊆ used := Finset.sdiff_eq_empty_iff_subset.mp hemp
          have := Finset.card_le_card hsub
          omega
        some hne.choose
      else none
  have hrecCol_spec : ∀ x : α,
      ∃ c : Fin K, recCol (e x) = some c ∧
        ∀ y ∈ nb x, e y < e x → recCol (e y) ≠ some c := by
    intro x
    have hdef : recCol (e x) =
        if h : ∃ z : α, e z = e x then
          let z := Classical.choose h
          let used : Finset (Fin K) :=
            (nb z).biUnion fun y =>
              if hy : e y < e x then (recCol (e y)).toFinset else ∅
          have hne : (Finset.univ \ used).Nonempty := by
            have hused_lt : used.card < (Finset.univ : Finset (Fin K)).card := by
              calc used.card
                  ≤ ∑ y ∈ nb z, (if hy : e y < e x then (recCol (e y)).toFinset else ∅).card :=
                    Finset.card_biUnion_le
                _ ≤ ∑ _y ∈ nb z, 1 := by
                    refine Finset.sum_le_sum fun y _ => ?_
                    split_ifs with hy
                    · cases recCol (e y) <;> simp
                    · simp
                _ = (nb z).card := by simp
                _ < K := hnb_card z
                _ = (Finset.univ : Finset (Fin K)).card := by simp
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            have := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
            omega
          some hne.choose
        else none := by
      dsimp only [recCol]
      rw [Nat.strongRec_eq]
    have hex : ∃ z : α, e z = e x := ⟨x, rfl⟩
    have hchoose_eq : Classical.choose hex = x := he (Classical.choose_spec hex)
    rw [dif_pos hex] at hdef
    set used : Finset (Fin K) :=
      (nb (Classical.choose hex)).biUnion fun y =>
        if hy : e y < e x then (recCol (e y)).toFinset else ∅
    have hne : (Finset.univ \ used).Nonempty := by
      have hused_lt : used.card < (Finset.univ : Finset (Fin K)).card := by
        calc used.card
            ≤ ∑ y ∈ nb (Classical.choose hex),
                (if hy : e y < e x then (recCol (e y)).toFinset else ∅).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _y ∈ nb (Classical.choose hex), 1 := by
              refine Finset.sum_le_sum fun y _ => ?_
              split_ifs with hy
              · cases recCol (e y) <;> simp
              · simp
          _ = (nb (Classical.choose hex)).card := by simp
          _ < K := hnb_card (Classical.choose hex)
          _ = (Finset.univ : Finset (Fin K)).card := by simp
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
      omega
    refine ⟨hne.choose, hdef, ?_⟩
    intro y hy hy_lt heq
    have hmem_sdiff := hne.choose_spec
    rw [Finset.mem_sdiff] at hmem_sdiff
    apply hmem_sdiff.2
    simp only [used, Finset.mem_biUnion]
    refine ⟨y, hchoose_eq.symm ▸ hy, ?_⟩
    rw [dif_pos hy_lt, heq]
    simp
  choose c hc_eq hc_avoid using hrecCol_spec
  refine ⟨c, fun x y hxy hceq => ?_⟩
  have hne : x ≠ y := fun h => hirr x (h ▸ hxy)
  have he_ne : e x ≠ e y := fun h => hne (he h)
  rcases lt_or_gt_of_ne he_ne with hlt | hgt
  · have hyx : adj y x := hsym x y hxy
    have h1 := hc_avoid y x ((hnb_mem y x).mpr hyx) hlt
    rw [hc_eq x, hceq] at h1
    exact h1 rfl
  · have h1 := hc_avoid x y ((hnb_mem x y).mpr hxy) hgt
    rw [hc_eq y, hceq] at h1
    exact h1 rfl

/-- **Exponential upper bound** for `χ(G_n)`: `unitDistanceGraph n` is `9 ^ n`-colorable for all `n`. -/
private lemma exponential_upper_bound :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ∃ k : ℕ, (Erdos704.unitDistanceGraph n).Colorable k ∧ (k : ℝ) ≤ C ^ n := by
  refine ⟨9, Filter.Eventually.of_forall fun n => ?_⟩
  refine ⟨9 ^ n, ?_, by push_cast; rfl⟩
  obtain ⟨N, hN_sep, hN_cov⟩ := exists_maximal_net n
  have : Countable N := (net_countable hN_sep).to_subtype
  have hnb : ∀ x : N, ∃ F : Finset N, (∀ y, y ∈ F ↔ (y ≠ x ∧ dist x.1 y.1 < 2)) ∧ F.card < 9 ^ n :=
    fun x => (net_neighbors_finite_and_card_lt hN_sep x).2
  obtain ⟨c, hc⟩ := greedy_coloring_countable
    (adj := fun x y : N => y ≠ x ∧ dist x.1 y.1 < 2)
    (fun x y ⟨hne, hdist⟩ => ⟨hne.symm, by rwa [dist_comm]⟩)
    (fun x ⟨hne, _⟩ => hne rfl)
    hnb
  choose π hπ_mem hπ_dist using hN_cov
  refine ⟨SimpleGraph.Coloring.mk (fun p => c ⟨π p, hπ_mem p⟩) ?_⟩
  intro p q hpq
  change dist p q = 1 at hpq
  have hne : (⟨π p, hπ_mem p⟩ : N) ≠ ⟨π q, hπ_mem q⟩ := by
    intro heq
    have hπeq : π p = π q := congr_arg Subtype.val heq
    have hp := hπ_dist p
    have hq := hπ_dist q
    rw [← hπeq, dist_comm q (π p)] at hq
    linarith [dist_triangle p (π p) q]
  have hdist : dist (π p) (π q) < 2 := by
    have hp := hπ_dist p
    have hq := hπ_dist q
    rw [dist_comm] at hp
    have h1 := dist_triangle (π p) p q
    have h2 := dist_triangle (π p) q (π q)
    linarith
  exact hc ⟨π p, hπ_mem p⟩ ⟨π q, hπ_mem q⟩ ⟨hne.symm, hdist⟩

end UpperBound

end OMAErdos704

theorem OMA.solution : type_of% @Erdos704.erdos_704.parts.i :=
  ⟨OMAErdos704.exponential_lower_bound, OMAErdos704.exponential_upper_bound⟩
