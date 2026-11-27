import FormalConjectures.GreensOpenProblems.«51»

/-!
# Green's Open Problem 51 — upper

We prove `Green51.green_51.upper`: there exists `α ∈ (0, 1]` such that for all sufficiently large
`n`, `guaranteedMaxCosetDim n α < n - √n`.

## Proof outline
1. For `x : 𝔽₂ n`, let `wt x` be its Hamming weight and `signedSum x = ∑ i, (±1) = n - 2 * wt x`.
2. By induction on `n`, the even moments `T k n = ∑ x : 𝔽₂ n, (signedSum x) ^ k` satisfy
   `T 2 n = n * 2^n`, `T 4 n = (3 n^2 - 2 n) * 2^n`, `T 6 n ≤ 15 n^3 * 2^n`, and
   `T 8 n ≤ 105 n^4 * 2^n`.
3. For `n ≥ 4` and threshold `t = (11 / 10) * √n`, Cauchy–Schwarz (Paley–Zygmund) on
   `B = {x | t^4 ≤ (signedSum x)^4}` together with sign-flip symmetry shows that
   `A = {x | t ≤ signedSum x}` has density `A.dens ≥ 1 / 210`.
4. Every `z ∈ A + A` satisfies `wt z ≤ n - (11 / 10) * √n`.
5. Conversely, every nonempty affine subspace `S ⊆ 𝔽₂ n` of dimension `d` contains a vector `z ∈ S`
   with `d ≤ wt z`, obtained from a minimal determining coordinate set `I ⊆ Fin n`.
6. Combining (3)–(5) yields `guaranteedMaxCosetDim n (1 / 210) ≤ n - (11 / 10) * √n < n - √n`
   for all `n ≥ 4`.
-/

-- Problem: Green's Open Problem 51 — upper
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/51.lean:68 (declaration Green51.green_51.upper)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Green51Proof

open Filter Real
open scoped Pointwise

private lemma zmod2_add_one_eq_zero_iff (a : ZMod 2) : a + 1 = 0 ↔ a ≠ 0 := by
  revert a; decide

private lemma zmod2_add_one_add_one (a : ZMod 2) : a + 1 + 1 = a := by
  revert a; decide

private lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl ha
  · rfl

private def wt {n : ℕ} (x : 𝔽₂ n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => x i ≠ 0).card

private lemma wt_add_le {n : ℕ} (x y : 𝔽₂ n) : wt (x + y) ≤ wt x + wt y := by
  calc
    wt (x + y) ≤ ((Finset.univ.filter fun i : Fin n => x i ≠ 0) ∪
        (Finset.univ.filter fun i : Fin n => y i ≠ 0)).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Pi.add_apply] at hi ⊢
      by_contra h
      push Not at h
      exact hi (by rw [h.1, h.2, add_zero])
    _ ≤ wt x + wt y := Finset.card_union_le _ _

private def signedSum {n : ℕ} (x : 𝔽₂ n) : ℝ :=
  ∑ i : Fin n, if x i = 0 then (1 : ℝ) else -1

private lemma signedSum_eq {n : ℕ} (x : 𝔽₂ n) :
    signedSum x = (n : ℝ) - 2 * (wt x : ℝ) := by
  have h : ∀ i : Fin n,
      (if x i = 0 then (1 : ℝ) else -1) =
        1 - 2 * (if x i ≠ 0 then (1 : ℝ) else 0) := by
    intro i
    by_cases hx : x i = 0
    · simp [hx]
    · simp [hx]
      norm_num
  simp only [signedSum, h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum, Finset.sum_boole, wt]

private def flip {n : ℕ} (x : 𝔽₂ n) : 𝔽₂ n := fun i => x i + 1

private lemma flip_flip {n : ℕ} (x : 𝔽₂ n) : flip (flip x) = x := by
  ext i
  exact zmod2_add_one_add_one (x i)

private lemma signedSum_flip {n : ℕ} (x : 𝔽₂ n) :
    signedSum (flip x) = - signedSum x := by
  simp only [signedSum, flip, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : x i = 0
  · simp [hx]
  · have h1 : x i + 1 = 0 := (zmod2_add_one_eq_zero_iff (x i)).mpr hx
    simp [hx, h1]

private lemma sum_succ {n : ℕ} (f : ℝ → ℝ) :
    ∑ x : 𝔽₂ (n + 1), f (signedSum x) =
      ∑ y : 𝔽₂ n, (f (signedSum y + 1) + f (signedSum y - 1)) := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => ZMod 2)]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun y _ => ?_
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
  have hcons : ∀ a : ZMod 2,
      signedSum (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod 2) (a, y)) =
        (if a = 0 then (1 : ℝ) else -1) + signedSum y := by
    intro a
    simp only [signedSum, Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [hcons 0, hcons 1]
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  simp only [↓reduceIte, h10]
  ring_nf

private def T (k n : ℕ) : ℝ := ∑ x : 𝔽₂ n, (signedSum x) ^ k

private lemma T_zero (n : ℕ) : T 0 n = (2 : ℝ) ^ n := by
  simp only [T, pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

private lemma T_base {k : ℕ} (hk : 1 ≤ k) : T k 0 = 0 := by
  simp only [T, signedSum, Finset.univ_eq_empty, Finset.sum_empty, zero_pow (by omega : k ≠ 0),
    Finset.sum_const_zero]

private lemma T_two (n : ℕ) : T 2 n = (n : ℝ) * (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [T_base]
  | succ n ih =>
    have hstep : T 2 (n + 1) = 2 * T 2 n + 2 * T 0 n := by
      simp only [T]
      rw [sum_succ (fun s => s ^ 2)]
      have halg : ∀ y : 𝔽₂ n,
          (signedSum y + 1) ^ 2 + (signedSum y - 1) ^ 2 =
            2 * (signedSum y) ^ 2 + 2 * (signedSum y) ^ 0 := by
        intro y; ring
      simp only [halg, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hstep, ih, T_zero, Nat.cast_succ, pow_succ]
    ring

private lemma T_four (n : ℕ) : T 4 n = (3 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) * (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [T_base]
  | succ n ih =>
    have hstep : T 4 (n + 1) = 2 * T 4 n + 12 * T 2 n + 2 * T 0 n := by
      simp only [T]
      rw [sum_succ (fun s => s ^ 4)]
      have halg : ∀ y : 𝔽₂ n,
          (signedSum y + 1) ^ 4 + (signedSum y - 1) ^ 4 =
            (2 * (signedSum y) ^ 4 + 12 * (signedSum y) ^ 2) + 2 * (signedSum y) ^ 0 := by
        intro y; ring
      simp only [halg, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hstep, ih, T_two, T_zero, Nat.cast_succ, pow_succ]
    ring

private lemma T_six_le (n : ℕ) : T 6 n ≤ 15 * (n : ℝ) ^ 3 * (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [T_base]
  | succ n ih =>
    have hstep : T 6 (n + 1) = 2 * T 6 n + 30 * T 4 n + 30 * T 2 n + 2 * T 0 n := by
      simp only [T]
      rw [sum_succ (fun s => s ^ 6)]
      have halg : ∀ y : 𝔽₂ n,
          (signedSum y + 1) ^ 6 + (signedSum y - 1) ^ 6 =
            ((2 * (signedSum y) ^ 6 + 30 * (signedSum y) ^ 4) + 30 * (signedSum y) ^ 2) +
              2 * (signedSum y) ^ 0 := by
        intro y; ring
      simp only [halg, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hstep, T_four, T_two, T_zero, Nat.cast_succ, pow_succ (2 : ℝ) n]
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpoly :
        (30 * (n : ℝ) ^ 3 + 90 * (n : ℝ) ^ 2 - 30 * (n : ℝ) + 2) ≤
          15 * ((n : ℝ) + 1) ^ 3 * 2 := by
      nlinarith
    calc
      2 * T 6 n + 30 * ((3 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) * (2 : ℝ) ^ n) +
          30 * ((n : ℝ) * (2 : ℝ) ^ n) + 2 * (2 : ℝ) ^ n
        ≤ 2 * (15 * (n : ℝ) ^ 3 * (2 : ℝ) ^ n) +
            30 * ((3 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) * (2 : ℝ) ^ n) +
            30 * ((n : ℝ) * (2 : ℝ) ^ n) + 2 * (2 : ℝ) ^ n := by linarith
      _ = (30 * (n : ℝ) ^ 3 + 90 * (n : ℝ) ^ 2 - 30 * (n : ℝ) + 2) * (2 : ℝ) ^ n := by ring
      _ ≤ (15 * ((n : ℝ) + 1) ^ 3 * 2) * (2 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right hpoly hpow
      _ = 15 * ((n : ℝ) + 1) ^ 3 * ((2 : ℝ) ^ n * 2) := by ring

private lemma T_eight_le (n : ℕ) : T 8 n ≤ 105 * (n : ℝ) ^ 4 * (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [T_base]
  | succ n ih =>
    have hstep : T 8 (n + 1) =
        2 * T 8 n + 56 * T 6 n + 140 * T 4 n + 56 * T 2 n + 2 * T 0 n := by
      simp only [T]
      rw [sum_succ (fun s => s ^ 8)]
      have halg : ∀ y : 𝔽₂ n,
          (signedSum y + 1) ^ 8 + (signedSum y - 1) ^ 8 =
            (((2 * (signedSum y) ^ 8 + 56 * (signedSum y) ^ 6) + 140 * (signedSum y) ^ 4) +
              56 * (signedSum y) ^ 2) + 2 * (signedSum y) ^ 0 := by
        intro y; ring
      simp only [halg, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h6 := T_six_le n
    rw [hstep, T_four, T_two, T_zero, Nat.cast_succ, pow_succ]
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpoly :
        (210 * (n : ℝ) ^ 4 + 840 * (n : ℝ) ^ 3 + 420 * (n : ℝ) ^ 2 - 224 * (n : ℝ) + 2) ≤
          105 * ((n : ℝ) + 1) ^ 4 * 2 := by
      nlinarith
    calc
      2 * T 8 n + 56 * T 6 n + 140 * ((3 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) * (2 : ℝ) ^ n) +
          56 * ((n : ℝ) * (2 : ℝ) ^ n) + 2 * (2 : ℝ) ^ n
        ≤ 2 * (105 * (n : ℝ) ^ 4 * (2 : ℝ) ^ n) + 56 * (15 * (n : ℝ) ^ 3 * (2 : ℝ) ^ n) +
            140 * ((3 * (n : ℝ) ^ 2 - 2 * (n : ℝ)) * (2 : ℝ) ^ n) +
            56 * ((n : ℝ) * (2 : ℝ) ^ n) + 2 * (2 : ℝ) ^ n := by linarith
      _ = (210 * (n : ℝ) ^ 4 + 840 * (n : ℝ) ^ 3 + 420 * (n : ℝ) ^ 2 - 224 * (n : ℝ) + 2) *
            (2 : ℝ) ^ n := by ring
      _ ≤ (105 * ((n : ℝ) + 1) ^ 4 * 2) * (2 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right hpoly hpow
      _ = 105 * ((n : ℝ) + 1) ^ 4 * ((2 : ℝ) ^ n * 2) := by ring

private lemma pow_four_ge_iff {t s : ℝ} (ht : 0 < t) :
    t ^ 4 ≤ s ^ 4 ↔ t ≤ s ∨ s ≤ -t := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have habs : |s| < t := abs_lt.mpr ⟨hlt.2, hlt.1⟩
    have h4 : |s| ^ 4 < t ^ 4 := pow_lt_pow_left₀ habs (abs_nonneg s) (by norm_num)
    have heq : |s| ^ 4 = s ^ 4 := by
      calc
        |s| ^ 4 = (|s| ^ 2) ^ 2 := by ring
        _ = (s ^ 2) ^ 2 := by rw [sq_abs]
        _ = s ^ 4 := by ring
    linarith
  · rintro (h | h)
    · exact pow_le_pow_left₀ ht.le h 4
    · have h' : t ≤ -s := by linarith
      have h4 : t ^ 4 ≤ (-s) ^ 4 := pow_le_pow_left₀ ht.le h' 4
      have heq : (-s) ^ 4 = s ^ 4 := by ring
      linarith

private lemma tail_dens_ge {n : ℕ} (hn : 4 ≤ n) :
    let t : ℝ := (11 / 10 : ℝ) * Real.sqrt (n : ℝ)
    let A : Finset (𝔽₂ n) := Finset.univ.filter fun x => t ≤ signedSum x
    (1 / 210 : ℝ) ≤ (A.dens : ℝ) := by
  intro t A
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have ht_pos : 0 < t := by positivity
  let B : Finset (𝔽₂ n) := Finset.univ.filter fun x => t ^ 4 ≤ (signedSum x) ^ 4
  let A' : Finset (𝔽₂ n) := Finset.univ.filter fun x => signedSum x ≤ -t
  have hB_eq : B = A ∪ A' := by
    ext x
    simp only [B, A, A', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact pow_four_ge_iff ht_pos
  have hdisj : Disjoint A A' := by
    rw [Finset.disjoint_left]
    intro x hxA hxA'
    simp only [A, A', Finset.mem_filter, Finset.mem_univ, true_and] at hxA hxA'
    linarith
  have hcard_eq : A'.card = A.card := by
    refine Finset.card_bij (fun x _ => flip x) ?_ ?_ ?_
    · intro x hx
      simp only [A, A', Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [signedSum_flip]
      linarith
    · intro x _ y _ hxy
      have := congr_arg flip hxy
      simpa [flip_flip] using this
    · intro y hy
      refine ⟨flip y, ?_, flip_flip y⟩
      simp only [A, A', Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [signedSum_flip]
      linarith
  have hB_card : B.card = 2 * A.card := by
    rw [hB_eq, Finset.card_union_of_disjoint hdisj, hcard_eq, two_mul]
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have ht4 : t ^ 4 ≤ (3 / 2 : ℝ) * (n : ℝ) ^ 2 := by
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
    have h4 : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
      calc
        Real.sqrt (n : ℝ) ^ 4 = (Real.sqrt (n : ℝ) ^ 2) ^ 2 := by ring
        _ = (n : ℝ) ^ 2 := by rw [hsq]
    calc
      t ^ 4 = (11 / 10 : ℝ) ^ 4 * Real.sqrt (n : ℝ) ^ 4 := by
        simp only [t, mul_pow]
      _ = (11 / 10 : ℝ) ^ 4 * (n : ℝ) ^ 2 := by rw [h4]
      _ ≤ (3 / 2 : ℝ) * (n : ℝ) ^ 2 := by
        have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
        nlinarith
  have hT4_lo : (5 / 2 : ℝ) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n ≤ T 4 n := by
    rw [T_four]
    have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hcoef : (5 / 2 : ℝ) * (n : ℝ) ^ 2 ≤ 3 * (n : ℝ) ^ 2 - 2 * (n : ℝ) := by nlinarith
    exact mul_le_mul_of_nonneg_right hcoef hpow_pos.le
  have hsplit : T 4 n = (∑ x ∈ B, (signedSum x) ^ 4) + ∑ x ∈ Bᶜ, (signedSum x) ^ 4 := by
    simpa [T] using (Finset.sum_add_sum_compl B (fun x : 𝔽₂ n => (signedSum x) ^ 4)).symm
  have hcompl_le : ∑ x ∈ Bᶜ, (signedSum x) ^ 4 ≤ (3 / 2 : ℝ) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n := by
    have hterm : ∀ x ∈ Bᶜ, (signedSum x) ^ 4 ≤ t ^ 4 := by
      intro x hx
      simp only [B, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx
      exact hx.le
    have hcard_le : (Bᶜ.card : ℝ) ≤ (2 : ℝ) ^ n := by
      have hle : Bᶜ.card ≤ Fintype.card (𝔽₂ n) := Finset.card_le_univ Bᶜ
      have hfc : Fintype.card (𝔽₂ n) = 2 ^ n := by
        simp [ZMod.card, Fintype.card_fin]
      rw [hfc] at hle
      exact_mod_cast hle
    calc
      ∑ x ∈ Bᶜ, (signedSum x) ^ 4 ≤ ∑ _x ∈ Bᶜ, t ^ 4 := Finset.sum_le_sum hterm
      _ = (Bᶜ.card : ℝ) * t ^ 4 := by simp
      _ ≤ (2 : ℝ) ^ n * ((3 / 2 : ℝ) * (n : ℝ) ^ 2) :=
            mul_le_mul hcard_le ht4 (pow_nonneg ht_pos.le 4) hpow_pos.le
      _ = (3 / 2 : ℝ) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n := by ring
  have hsumB_lo : (n : ℝ) ^ 2 * (2 : ℝ) ^ n ≤ ∑ x ∈ B, (signedSum x) ^ 4 := by linarith
  have hsumB_sq_le :
      (∑ x ∈ B, (signedSum x) ^ 4) ^ 2 ≤ (B.card : ℝ) * T 8 n := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := B) (f := fun x : 𝔽₂ n => (signedSum x) ^ 4)
    have hsub : ∑ x ∈ B, ((signedSum x) ^ 4) ^ 2 ≤ T 8 n := by
      have h8 : ∀ x : 𝔽₂ n, ((signedSum x) ^ 4) ^ 2 = (signedSum x) ^ 8 := fun x => by ring
      simp only [h8, T]
      exact Finset.sum_le_univ_sum_of_nonneg fun x => by positivity
    calc
      (∑ x ∈ B, (signedSum x) ^ 4) ^ 2 ≤ (B.card : ℝ) * ∑ x ∈ B, ((signedSum x) ^ 4) ^ 2 := hcs
      _ ≤ (B.card : ℝ) * T 8 n := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
  have hT8 := T_eight_le n
  have hkey : ((n : ℝ) ^ 2 * (2 : ℝ) ^ n) ^ 2 ≤
      (B.card : ℝ) * (105 * (n : ℝ) ^ 4 * (2 : ℝ) ^ n) := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ n := by positivity
    calc
      ((n : ℝ) ^ 2 * (2 : ℝ) ^ n) ^ 2 ≤ (∑ x ∈ B, (signedSum x) ^ 4) ^ 2 :=
            pow_le_pow_left₀ hnn hsumB_lo 2
      _ ≤ (B.card : ℝ) * T 8 n := hsumB_sq_le
      _ ≤ (B.card : ℝ) * (105 * (n : ℝ) ^ 4 * (2 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left hT8 (Nat.cast_nonneg _)
  have hfac_pos : (0 : ℝ) < (n : ℝ) ^ 4 * (2 : ℝ) ^ n := by positivity
  have hB_ge : (2 : ℝ) ^ n ≤ 105 * (B.card : ℝ) := by
    have hmul : (2 : ℝ) ^ n * ((n : ℝ) ^ 4 * (2 : ℝ) ^ n) ≤
        (105 * (B.card : ℝ)) * ((n : ℝ) ^ 4 * (2 : ℝ) ^ n) := by
      linarith [hkey]
    exact le_of_mul_le_mul_right hmul hfac_pos
  have hA_ge : (2 : ℝ) ^ n ≤ 210 * (A.card : ℝ) := by
    have hcast : (B.card : ℝ) = 2 * (A.card : ℝ) := by exact_mod_cast hB_card
    linarith
  have hdens : (A.dens : ℝ) = (A.card : ℝ) / (2 : ℝ) ^ n := by
    rw [Finset.dens_eq_card_div_card]
    have hfc : Fintype.card (𝔽₂ n) = 2 ^ n := by
      simp [ZMod.card, Fintype.card_fin]
    rw [hfc]
    push_cast
    rfl
  rw [hdens, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 210) hpow_pos]
  linarith

private lemma exists_weight_ge_finrank {n : ℕ}
    (S : AffineSubspace (ZMod 2) (𝔽₂ n)) (hne : (S : Set (𝔽₂ n)).Nonempty) :
    ∃ z ∈ S, Module.finrank (ZMod 2) S.direction ≤ wt z := by
  classical
  rcases hne with ⟨p, hp⟩
  let W : Submodule (ZMod 2) (𝔽₂ n) := S.direction
  let IsDet : Finset (Fin n) → Prop := fun I => ∀ w ∈ W, (∀ i ∈ I, w i = 0) → w = 0
  let F : Finset (Finset (Fin n)) := Finset.univ.filter IsDet
  have hFne : F.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro w _ hw
    ext i
    exact hw i (Finset.mem_univ i)
  rcases Finset.exists_min_image F Finset.card hFne with ⟨I, hIF, hImin⟩
  have hI : IsDet I := (Finset.mem_filter.mp hIF).2
  have hfinrank_le : Module.finrank (ZMod 2) W ≤ I.card := by
    let proj : W →ₗ[ZMod 2] (I → ZMod 2) :=
      { toFun := fun w i => w.1 i.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective proj := by
      intro w1 w2 h12
      apply Subtype.ext
      have hdiff : w1.1 - w2.1 ∈ W := W.sub_mem w1.2 w2.2
      have hzero : w1.1 - w2.1 = 0 := hI (w1.1 - w2.1) hdiff fun i hi => by
        have hi' := congr_fun h12 ⟨i, hi⟩
        simp only [proj, LinearMap.coe_mk, AddHom.coe_mk] at hi'
        simp [hi']
      exact sub_eq_zero.mp hzero
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    simpa [Module.finrank_pi, Fintype.card_coe] using hle
  have hex : ∀ i ∈ I, ∃ w ∈ W, w i = 1 ∧ ∀ j ∈ I, j ≠ i → w j = 0 := by
    intro i hi
    have hnot : ¬ IsDet (I.erase i) := by
      intro hdet
      have hmem : I.erase i ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdet⟩
      have hle := hImin (I.erase i) hmem
      have hlt := Finset.card_erase_lt_of_mem hi
      omega
    simp only [IsDet] at hnot
    push Not at hnot
    rcases hnot with ⟨w, hwW, hw_erase, hw_ne⟩
    have hwi_ne : w i ≠ 0 := by
      intro hwi0
      apply hw_ne
      apply hI w hwW
      intro j hj
      by_cases hji : j = i
      · subst hji; exact hwi0
      · exact hw_erase j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    refine ⟨w, hwW, zmod2_eq_one_of_ne_zero hwi_ne, fun j hj hji => ?_⟩
    exact hw_erase j (Finset.mem_erase.mpr ⟨hji, hj⟩)
  let b : Fin n → 𝔽₂ n := fun i =>
    if hi : i ∈ I then Classical.choose (hex i hi) else 0
  have hb_mem : ∀ i ∈ I, b i ∈ W := fun i hi => by
    simp only [b, dif_pos hi]
    exact (Classical.choose_spec (hex i hi)).1
  have hb_diag : ∀ i ∈ I, b i i = 1 := fun i hi => by
    simp only [b, dif_pos hi]
    exact (Classical.choose_spec (hex i hi)).2.1
  have hb_off : ∀ i ∈ I, ∀ j ∈ I, j ≠ i → b i j = 0 := fun i hi => by
    simp only [b, dif_pos hi]
    exact (Classical.choose_spec (hex i hi)).2.2
  let J : Finset (Fin n) := I.filter fun i => p i = 0
  let w : 𝔽₂ n := ∑ i ∈ J, b i
  have hwW : w ∈ W := Submodule.sum_mem W fun i hi =>
    hb_mem i (Finset.mem_of_mem_filter i hi)
  have hwp_mem : w + p ∈ S := by
    have hv := AffineSubspace.vadd_mem_of_mem_direction hwW hp
    simpa [vadd_eq_add] using hv
  have hI_sub : I ⊆ Finset.univ.filter fun j : Fin n => (w + p) j ≠ 0 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
    have hwj : w j = ∑ i ∈ J, b i j := by
      simp only [w, Finset.sum_apply]
    rw [hwj]
    by_cases hpj : p j = 0
    · have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨hj, hpj⟩
      have hsum : ∑ i ∈ J, b i j = b j j := by
        refine Finset.sum_eq_single_of_mem j hjJ fun i hi hij => ?_
        exact hb_off i (Finset.mem_of_mem_filter i hi) j hj hij.symm
      rw [hsum, hb_diag j hj, hpj, add_zero]
      decide
    · have hsum : ∑ i ∈ J, b i j = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hiI : i ∈ I := Finset.mem_of_mem_filter i hi
        have hpi : p i = 0 := (Finset.mem_filter.mp hi).2
        have hij : j ≠ i := fun h => hpj (h ▸ hpi)
        exact hb_off i hiI j hj hij
      rw [hsum, zero_add]
      exact hpj
  refine ⟨w + p, hwp_mem, le_trans hfinrank_le (Finset.card_le_card hI_sub)⟩

end Green51Proof

open Green51 Green51Proof Filter Real
open scoped Pointwise

theorem OMA.solution : type_of% @Green51.green_51.upper := by
  refine ⟨1 / 210, by norm_num, by norm_num, Filter.eventually_atTop.mpr ⟨4, fun n hn => ?_⟩⟩
  let t : ℝ := (11 / 10 : ℝ) * Real.sqrt (n : ℝ)
  let A : Finset (𝔽₂ n) := Finset.univ.filter fun x => t ≤ signedSum x
  have hAdens : (A.dens : ℝ) ≥ (1 / 210 : ℝ) := tail_dens_ge hn
  have hinf_le : guaranteedMaxCosetDim n (1 / 210) ≤
      maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A + A) := by
    rw [guaranteedMaxCosetDim]
    exact Nat.sInf_le ⟨A, hAdens, rfl⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrt_ge2 : (2 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : Real.sqrt 4 ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h4
    have hsq4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hbound_nonneg : 0 ≤ (n : ℝ) - t := by
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
    simp only [t]
    nlinarith
  have hwt_sumset : ∀ z ∈ (↑(A + A) : Set (𝔽₂ n)), (wt z : ℝ) ≤ (n : ℝ) - t := by
    intro z hz
    rw [Finset.mem_coe, Finset.mem_add] at hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rw [signedSum_eq] at hx hy
    have hle : (wt (x + y) : ℝ) ≤ (wt x : ℝ) + (wt y : ℝ) := by
      exact_mod_cast wt_add_le x y
    linarith
  let M : ℕ := Nat.floor ((n : ℝ) - t)
  have hmax_le : maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A + A) ≤ M := by
    rw [maxCosetDim]
    refine csSup_le ⟨0, ⊥, by simp, by simp⟩ ?_
    rintro d ⟨S, hS, rfl⟩
    by_cases hne : (S : Set (𝔽₂ n)).Nonempty
    · rcases exists_weight_ge_finrank S hne with ⟨z, hzS, hdz⟩
      have hzw : (wt z : ℝ) ≤ (n : ℝ) - t := hwt_sumset z (hS hzS)
      have hd_r : (Module.finrank (ZMod 2) S.direction : ℝ) ≤ (n : ℝ) - t :=
        le_trans (by exact_mod_cast hdz) hzw
      exact Nat.le_floor hd_r
    · have hbot : S = ⊥ := SetLike.ext'_iff.mpr (by
        simpa [Set.not_nonempty_iff_eq_empty] using hne)
      rw [hbot, AffineSubspace.direction_bot, finrank_bot]
      exact Nat.zero_le M
  have hfinal_le : (guaranteedMaxCosetDim n (1 / 210) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast le_trans hinf_le hmax_le
  have hM_le : (M : ℝ) ≤ (n : ℝ) - t := Nat.floor_le hbound_nonneg
  simp only [t] at hM_le
  linarith
