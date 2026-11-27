import FormalConjectures.ErdosProblems.«1028»

/-! The Erdős–Spencer imbalance bound via finite sign averages and a signed cut.
See https://users.renyi.hu/~p_erdos/1971-05.pdf. -/

open Filter Finset
open scoped BigOperators Asymptotics

private def OMA.realSign (b : Bool) : ℝ := if b then 1 else -1

private def OMA.signSum {k : ℕ} (s : Fin k → Bool) : ℝ := ∑ i, OMA.realSign (s i)

private lemma OMA.sumSignSumSucc (k : ℕ) (F : ℝ → ℝ) :
    (∑ s : Fin (k + 1) → Bool, F (OMA.signSum s)) =
      ∑ s : Fin k → Bool, (F (OMA.signSum s + 1) + F (OMA.signSum s - 1)) := by
  let e : ((Fin k → Bool) × Bool) ≃ (Fin (k + 1) → Bool) :=
    (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => Bool))
  calc
    _ = ∑ p : (Fin k → Bool) × Bool, F (OMA.signSum p.1 + OMA.realSign p.2) := by
      symm
      apply Fintype.sum_equiv e
      rintro ⟨s, b⟩
      change F (OMA.signSum s + OMA.realSign b) = F (OMA.signSum (Fin.cons b s))
      simp [OMA.signSum, Fin.sum_univ_succ, add_comm]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s _
      simp [OMA.realSign, sub_eq_add_neg, add_comm]

private lemma OMA.signSumMoments (k : ℕ) :
    (∑ s : Fin k → Bool, (OMA.signSum s) ^ 2) = (2 : ℝ) ^ k * k ∧
      (∑ s : Fin k → Bool, (OMA.signSum s) ^ 4) ≤ 3 * (2 : ℝ) ^ k * (k : ℝ) ^ 2 := by
  induction k with
  | zero =>
    simp [OMA.signSum]
  | succ k ih =>
    have hcard (a : ℝ) : (∑ _ : Fin k → Bool, a) = (2 : ℝ) ^ k * a := by
      simp
    constructor
    · rw [OMA.sumSignSumSucc k (fun t => t ^ 2)]
      simp_rw [show ∀ t : ℝ, (t + 1) ^ 2 + (t - 1) ^ 2 = 2 * t ^ 2 + 2 by
        intro t; ring]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih.1, hcard, pow_succ]
      push_cast
      ring
    · rw [OMA.sumSignSumSucc k (fun t => t ^ 4)]
      simp_rw [show ∀ t : ℝ, (t + 1) ^ 4 + (t - 1) ^ 4 = 2 * t ^ 4 + 12 * t ^ 2 + 2 by
        intro t; ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ih.1, hcard, pow_succ]
      push_cast
      have hp : (0 : ℝ) ≤ 2 ^ k := by positivity
      have hk : (0 : ℝ) ≤ k := by positivity
      nlinarith [mul_nonneg hp hk]

private lemma OMA.signSumAbsolute (k : ℕ) (hk : 0 < k) :
    (2 : ℝ) ^ k * Real.sqrt k ≤ 8 * ∑ s : Fin k → Bool, |OMA.signSum s| := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hr : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkr
  have hrsq := Real.sq_sqrt hkr.le
  have hpoint (t : ℝ) : 4 * (k : ℝ) * t ^ 2 ≤
      8 * (k : ℝ) * Real.sqrt k * |t| + t ^ 4 := by
    have ht := abs_nonneg t
    have heq := sq_abs t
    by_cases h : |t| ≤ 2 * Real.sqrt k
    · have hmul := mul_le_mul_of_nonneg_left h ht
      have hprod := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 4 * (k : ℝ) by positivity)
      nlinarith [pow_nonneg (abs_nonneg t) 4, sq_nonneg (t ^ 2)]
    · have hmul := mul_self_le_mul_self (by positivity : 0 ≤ 2 * Real.sqrt (k : ℝ)) (le_of_not_ge h)
      have hprod : 4 * (k : ℝ) * t ^ 2 ≤ t ^ 4 := by
        have hsq : 4 * (k : ℝ) ≤ t ^ 2 := by nlinarith
        have hq := mul_le_mul_of_nonneg_right hsq (sq_nonneg t)
        nlinarith
      exact hprod.trans (by linarith [show 0 ≤ 8 * (k : ℝ) * Real.sqrt k * |t| by positivity])
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hpoint (OMA.signSum (k := k) s))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  obtain ⟨h2, h4⟩ := OMA.signSumMoments k
  rw [h2] at hs
  have h := add_le_add_left h4 (8 * (k : ℝ) * Real.sqrt k *
    ∑ s : Fin k → Bool, |OMA.signSum s|)
  apply (mul_le_mul_iff_right₀ (mul_pos hkr hr)).mp
  calc
    _ = (2 : ℝ) ^ k * (k : ℝ) ^ 2 := by
      calc
        _ = (2 : ℝ) ^ k * k * (Real.sqrt k) ^ 2 := by ring
        _ = _ := by rw [hrsq]; ring
    _ ≤ _ := by linarith only [hs, h]

open scoped Classical in
private def OMA.signScore {k : ℕ} (f : ℕ → ℕ → ℝ) (s : Fin k → Bool) (y : ℕ) : ℝ :=
  ∑ i, OMA.realSign (s i) * f (i.val + 1) y

private lemma OMA.sumAbsSignScore (k : ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ x y, f x y = 1 ∨ f x y = -1) (y : ℕ) :
    (∑ s : Fin k → Bool, |OMA.signScore f s y|) = ∑ s : Fin k → Bool, |OMA.signSum s| := by
  classical
  let flip (s : Fin k → Bool) (i : Fin k) :=
    if f (i.val + 1) y = 1 then s i else !(s i)
  have hflip : Function.Involutive flip := by
    intro s
    funext i
    by_cases h : f (i.val + 1) y = 1 <;> simp [flip, h]
  let e : (Fin k → Bool) ≃ (Fin k → Bool) := ⟨flip, flip, hflip, hflip⟩
  apply Fintype.sum_equiv e
  intro s
  congr 1
  unfold OMA.signScore OMA.signSum
  refine Finset.sum_congr rfl fun i _ => ?_
  change OMA.realSign (s i) * f (i.val + 1) y = OMA.realSign (flip s i)
  rcases hf (i.val + 1) y with h | h <;> cases hsi : s i <;> norm_num [flip, OMA.realSign, h, hsi]

private lemma OMA.existsLargeScore (k : ℕ) (hk : 0 < k) (f : ℕ → ℕ → ℝ)
    (hf : ∀ x y, f x y = 1 ∨ f x y = -1) (B : Finset ℕ) :
    ∃ s : Fin k → Bool, (B.card : ℝ) * Real.sqrt k ≤ 8 * ∑ y ∈ B, |OMA.signScore f s y| := by
  classical
  have hsum : (∑ s : Fin k → Bool, ∑ y ∈ B, |OMA.signScore f s y|) =
      (B.card : ℝ) * ∑ s : Fin k → Bool, |OMA.signSum s| := by
    rw [Finset.sum_comm]
    simp_rw [OMA.sumAbsSignScore k f hf]
    simp [nsmul_eq_mul]
  by_contra! h
  have hlt := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty (fun s _ => h s)
  rw [← Finset.mul_sum, hsum] at hlt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hlt
  have hle := mul_le_mul_of_nonneg_left (OMA.signSumAbsolute k hk) (by positivity : (0 : ℝ) ≤ B.card)
  linarith only [hlt, hle]

namespace DiscrepancySpencer
private def signed (f : ℕ → ℕ → ℝ) (X : Finset ℕ) : ℝ :=
  ∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y

private def cross (f : ℕ → ℕ → ℝ) (A B : Finset ℕ) : ℝ :=
  ∑ y ∈ B, ∑ x ∈ A, f x y

/-- On separated sets, the cross term always uses the first set as its first coordinate. -/
private lemma signed_union (f : ℕ → ℕ → ℝ) (A B : Finset ℕ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x < y) :
    signed f (A ∪ B) = signed f A + signed f B + cross f A B := by
  have hdisj : Disjoint A B := Finset.disjoint_left.2 fun x hx hy => (hsep x hx x hy).false
  unfold signed
  rw [Finset.sum_union hdisj]
  have hA :
      (∑ x ∈ A, ∑ y ∈ (A ∪ B).filter (fun y => x < y), f x y) =
      (∑ x ∈ A, ∑ y ∈ A.filter (fun y => x < y), f x y) + cross f A B := by
    unfold cross
    rw [Finset.sum_comm (s := B) (t := A), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.filter_union, Finset.filter_eq_self.2 (hsep x hx)]
    exact Finset.sum_union (hdisj.mono_left (Finset.filter_subset _ _))
  have hB :
      (∑ x ∈ B, ∑ y ∈ (A ∪ B).filter (fun y => x < y), f x y) =
      (∑ x ∈ B, ∑ y ∈ B.filter (fun y => x < y), f x y) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have he : A.filter (fun y => x < y) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun y hy hxy => (hsep y hy x hx).not_gt hxy
    rw [Finset.filter_union, he, Finset.empty_union]
  rw [hA, hB]
  abel

private lemma largeDiscrepancy (f : ℕ → ℕ → ℝ)
    (hf : ∀ x y, f x y = 1 ∨ f x y = -1)
    (n : ℕ) (hn : 2 ≤ n) (m : ℝ)
    (hm : ∀ X ⊆ Finset.Icc 1 n, |signed f X| ≤ m) :
    (n : ℝ) * Real.sqrt n ≤ 128 * m := by
  classical
  let k := n / 2
  let B := Finset.Icc (k + 1) n
  have hk : 0 < k := by dsimp [k]; omega
  obtain ⟨s, hs⟩ := OMA.existsLargeScore k hk f hf B
  let e : Fin k ↪ ℕ := ⟨fun i => i.val + 1, by
    intro i j h
    apply Fin.ext
    change i.val + 1 = j.val + 1 at h
    omega⟩
  let Ap : Finset ℕ := (Finset.univ.filter fun i : Fin k => s i).map e
  let An : Finset ℕ := (Finset.univ.filter fun i : Fin k => ¬ s i).map e
  let Bp := B.filter fun y => 0 ≤ OMA.signScore f s y
  let Bn := B.filter fun y => ¬ 0 ≤ OMA.signScore f s y
  have hmap (I : Finset (Fin k)) : I.map e ⊆ Finset.Icc 1 k := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    have hi := i.isLt
    exact Finset.mem_Icc.mpr ⟨by change 1 ≤ i.val + 1; omega, by change i.val + 1 ≤ k; omega⟩
  have hAp : Ap ⊆ Finset.Icc 1 k := hmap _
  have hAn : An ⊆ Finset.Icc 1 k := hmap _
  have hBp : Bp ⊆ B := Finset.filter_subset _ _
  have hBn : Bn ⊆ B := Finset.filter_subset _ _
  have hsep {A C : Finset ℕ} (hA : A ⊆ Finset.Icc 1 k) (hC : C ⊆ B) :
      ∀ x ∈ A, ∀ y ∈ C, x < y := by
    intro x hx y hy
    exact ((Finset.mem_Icc.mp (hA hx)).2).trans_lt (Finset.mem_Icc.mp (hC hy)).1
  have hmem {A C : Finset ℕ} (hA : A ⊆ Finset.Icc 1 k) (hC : C ⊆ B) :
      A ∪ C ⊆ Finset.Icc 1 n := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (hA hx)
      exact Finset.mem_Icc.mpr ⟨hlo, hhi.trans (Nat.div_le_self n 2)⟩
    · obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (hC hx)
      exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  have hrows (C : Finset ℕ) :
      cross f Ap C - cross f An C = ∑ y ∈ C, OMA.signScore f s y := by
    unfold cross
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Ap, An, Finset.sum_map, Finset.sum_filter, ← Finset.sum_sub_distrib,
      OMA.signScore]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ((if s i then f (i.val + 1) y else 0) -
      (if ¬s i then f (i.val + 1) y else 0)) = OMA.realSign (s i) * f (i.val + 1) y
    cases s i <;> simp [OMA.realSign]
  have hcols :
      (∑ y ∈ Bp, OMA.signScore f s y) - (∑ y ∈ Bn, OMA.signScore f s y) =
        ∑ y ∈ B, |OMA.signScore f s y| := by
    simp only [Bp, Bn, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : 0 ≤ OMA.signScore f s y
    · simp [hy, abs_of_nonneg hy]
    · simp [hy, abs_of_neg (lt_of_not_ge hy)]
  have uPP := signed_union f Ap Bp (hsep hAp hBp)
  have uPN := signed_union f Ap Bn (hsep hAp hBn)
  have uNP := signed_union f An Bp (hsep hAn hBp)
  have uNN := signed_union f An Bn (hsep hAn hBn)
  have hId :
      signed f (Ap ∪ Bp) - signed f (Ap ∪ Bn) - signed f (An ∪ Bp) + signed f (An ∪ Bn) =
        ∑ y ∈ B, |OMA.signScore f s y| := by
    linarith only [uPP, uPN, uNP, uNN, hrows Bp, hrows Bn, hcols]
  have hPP := (abs_le.mp (hm _ (hmem hAp hBp))).2
  have hPN := (abs_le.mp (hm _ (hmem hAp hBn))).1
  have hNP := (abs_le.mp (hm _ (hmem hAn hBp))).1
  have hNN := (abs_le.mp (hm _ (hmem hAn hBn))).2
  have hcard : B.card = n - k := by
    dsimp [B]
    rw [Nat.card_Icc]
    omega
  have hsize : (n : ℝ) ≤ 2 * B.card := by
    exact_mod_cast (show n ≤ 2 * B.card by rw [hcard]; dsimp [k]; omega)
  have hsqrt : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt k := by
    have hlt : (n : ℝ) ≤ 4 * k := by
      exact_mod_cast (show n ≤ 4 * k by dsimp [k]; omega)
    calc
      _ ≤ Real.sqrt (4 * (k : ℝ)) := Real.sqrt_le_sqrt hlt
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  calc
    _ ≤ (2 * (B.card : ℝ)) * (2 * Real.sqrt k) :=
      mul_le_mul hsize hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = 4 * ((B.card : ℝ) * Real.sqrt k) := by ring
    _ ≤ 128 * m := by linarith only [hs, hId, hPP, hPN, hNP, hNN]

private lemma admissible_nonempty (n : ℕ) :
    {m : ℕ | ∃ f : ℕ → ℕ → ℤ, (∀ x y, f x y = 1 ∨ f x y = -1) ∧
      ∀ X ⊆ Finset.Icc 1 n, Erdos1028.imbalance f X ≤ (m : ℤ)}.Nonempty := by
  refine ⟨n * n, fun _ _ => 1, fun _ _ => Or.inl rfl, ?_⟩
  intro X hX
  have hcard : X.card ≤ n := by
    have h := Finset.card_le_card hX
    simpa [Nat.card_Icc] using h
  unfold Erdos1028.imbalance
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by norm_num)]
  calc
    _ ≤ ∑ _ ∈ X, (X.card : ℤ) := by
      refine Finset.sum_le_sum fun x _ => ?_
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast Finset.card_filter_le X (fun y => x < y)
    _ = (X.card : ℤ) * X.card := by simp
    _ ≤ ((n * n : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul hcard hcard

end DiscrepancySpencer

open DiscrepancySpencer in
theorem OMA.solution : type_of% @Erdos1028.erdos_1028.variants.erdos_spencer := by
  apply Asymptotics.IsBigO.of_bound 128
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  obtain ⟨f, hf, hm⟩ := Nat.sInf_mem (admissible_nonempty n)
  have hr (X : Finset ℕ) (hX : X ⊆ Finset.Icc 1 n) :
      |signed (fun x y => (f x y : ℝ)) X| ≤ (Erdos1028.H n : ℝ) := by
    change |∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), (f x y : ℝ)| ≤ _
    simp only [← Int.cast_sum, ← Int.cast_abs]
    exact_mod_cast hm X hX
  have hcast (x y : ℕ) : (f x y : ℝ) = 1 ∨ (f x y : ℝ) = -1 := by
    rcases hf x y with h | h <;> simp [h]
  have hlarge := largeDiscrepancy _ hcast n hn (Erdos1028.H n : ℝ) hr
  have hrpow : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity : 0 < (n : ℝ)), Real.rpow_one, Real.sqrt_eq_rpow]
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ (Erdos1028.H n : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ)), hrpow] using hlarge