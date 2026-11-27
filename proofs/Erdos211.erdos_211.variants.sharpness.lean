import FormalConjectures.ErdosProblems.«211»

-- Problem: Erdős Problem 211 — sharpness
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/211.lean:79 (declaration Erdos211.erdos_211.variants.sharpness)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Construction: the points (X t, t - X t) with X t = t / (1 + t ^ 2) lie on a nodal cubic;
-- three of them with distinct parameters a, b, c are collinear iff a + b + c = a * b * c.
-- With t = tan (k * π / n), k in [-m, m], n = 2 m + 1, this means n divides the sum of indices.

namespace OMA.O7

open EuclideanGeometry Filter Erdos211

open scoped Classical

noncomputable def X (t : ℝ) : ℝ := t / (1 + t ^ 2)

noncomputable def pt (t : ℝ) : ℝ² := WithLp.toLp 2 ![X t, t - X t]

lemma pt0 (t : ℝ) : pt t 0 = X t := rfl
lemma pt1 (t : ℝ) : pt t 1 = t - X t := rfl

lemma pt_inj {a b : ℝ} (h : pt a = pt b) : a = b := by
  have h0 := congrArg (fun p : ℝ² => p 0) h
  have h1 := congrArg (fun p : ℝ² => p 1) h
  simp only [pt0, pt1] at h0 h1
  linarith

lemma key (a b c : ℝ) :
    (X b - X a) * (c - a) - (X c - X a) * (b - a) =
      (b - a) * (c - a) * (c - b) * (a + b + c - a * b * c) /
        ((1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) := by
  have ha : (1 + a ^ 2) ≠ 0 := by positivity
  have hb : (1 + b ^ 2) ≠ 0 := by positivity
  have hc : (1 + c ^ 2) ≠ 0 := by positivity
  unfold X
  field_simp
  ring

lemma mem_line_iff {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    pt c ∈ line[ℝ, pt a, pt b] ↔ a + b + c = a * b * c := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hca : c - a ≠ 0 := sub_ne_zero.mpr hac.symm
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
  have hden : ((1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) ≠ 0 := by positivity
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, hr⟩
    have h0 := congrArg (fun p : ℝ² => p 0) hr
    have h1 := congrArg (fun p : ℝ² => p 1) hr
    simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      pt0, pt1] at h0 h1
    have hs : c - a = r * (b - a) := by linarith
    have hD : (X b - X a) * (c - a) - (X c - X a) * (b - a) = 0 := by
      rw [hs, ← h0]; ring
    rw [key, div_eq_zero_iff] at hD
    rcases hD with hD | hD
    · rcases mul_eq_zero.mp hD with hD | hD
      · exfalso
        rcases mul_eq_zero.mp hD with hD | hD
        · rcases mul_eq_zero.mp hD with hD | hD
          · exact hba hD
          · exact hca hD
        · exact hcb hD
      · linarith
    · exact absurd hD hden
  · intro h
    refine ⟨(c - a) / (b - a), ?_⟩
    have hD : (X b - X a) * (c - a) - (X c - X a) * (b - a) = 0 := by
      rw [key]
      have : a + b + c - a * b * c = 0 := by linarith
      rw [this]; simp
    set r := (c - a) / (b - a) with hrdef
    have hr : r * (b - a) = c - a := div_mul_cancel₀ _ hba
    have e0 : (1 - r) * X a + r * X b = X c := by
      have : (r * (X b - X a)) * (b - a) = (X c - X a) * (b - a) := by
        rw [mul_right_comm, hr]; linarith
      have := mul_right_cancel₀ hba this
      linarith
    ext i
    fin_cases i
    · simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      simp only [Fin.zero_eta, pt0]
      exact e0
    · simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      simp only [Fin.mk_one, pt1]
      linarith

lemma tan_identity {α β γ : ℝ} (ha : Real.cos α ≠ 0) (hb : Real.cos β ≠ 0)
    (hc : Real.cos γ ≠ 0) :
    Real.tan α + Real.tan β + Real.tan γ - Real.tan α * Real.tan β * Real.tan γ =
      Real.sin (α + β + γ) / (Real.cos α * Real.cos β * Real.cos γ) := by
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
    Real.sin_add, Real.sin_add, Real.cos_add]
  field_simp
  ring

/-- the parameter of index k -/
noncomputable def θ (m : ℕ) (k : ℤ) : ℝ := (k : ℝ) * Real.pi / (2 * m + 1)

noncomputable def P (m : ℕ) (k : ℤ) : ℝ² := pt (Real.tan (θ m k))

def I (m : ℕ) : Finset ℤ := Finset.Icc (-(m : ℤ)) m

noncomputable def S (m : ℕ) : Finset ℝ² := (I m).image (P m)

lemma θ_mem {m : ℕ} {k : ℤ} (hk : k ∈ I m) : θ m k ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  simp only [I, Finset.mem_Icc] at hk
  have hk1 : (-(m : ℝ)) ≤ k := by exact_mod_cast hk.1
  have hk2 : (k : ℝ) ≤ m := by exact_mod_cast hk.2
  have hpi := Real.pi_pos
  have hn : (0 : ℝ) < 2 * m + 1 := by positivity
  unfold θ
  constructor
  · rw [lt_div_iff₀ hn]; nlinarith
  · rw [div_lt_iff₀ hn]; nlinarith

lemma cos_ne {m : ℕ} {k : ℤ} (hk : k ∈ I m) : Real.cos (θ m k) ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo (θ_mem hk)).ne'

lemma tan_inj {m : ℕ} {k l : ℤ} (hk : k ∈ I m) (hl : l ∈ I m)
    (h : Real.tan (θ m k) = Real.tan (θ m l)) : k = l := by
  have := Real.injOn_tan (θ_mem hk) (θ_mem hl) h
  unfold θ at this
  have hn : (0 : ℝ) < 2 * m + 1 := by positivity
  have hpi := Real.pi_pos
  rw [div_left_inj' hn.ne'] at this
  have : (k : ℝ) = l := by
    have := mul_right_cancel₀ hpi.ne' this
    exact this
  exact_mod_cast this

lemma P_inj {m : ℕ} {k l : ℤ} (hk : k ∈ I m) (hl : l ∈ I m) (h : P m k = P m l) : k = l :=
  tan_inj hk hl (pt_inj h)

lemma uniq {m : ℕ} {a b : ℤ} (ha : a ∈ I m) (hb : b ∈ I m) (h : (2 * (m : ℤ) + 1) ∣ a - b) :
    a = b := by
  simp only [I, Finset.mem_Icc] at ha hb
  obtain ⟨u, hu⟩ := h
  push_cast at hu
  rcases lt_trichotomy u 0 with hu0 | hu0 | hu0
  · nlinarith
  · subst hu0; linarith
  · nlinarith

lemma sin_zero_iff (m : ℕ) (i j l : ℤ) :
    Real.sin (θ m i + θ m j + θ m l) = 0 ↔ (2 * (m : ℤ) + 1) ∣ i + j + l := by
  have hn : (0 : ℝ) < 2 * m + 1 := by positivity
  have hpi := Real.pi_pos
  have hsum : θ m i + θ m j + θ m l = ((i + j + l : ℤ) : ℝ) * Real.pi / (2 * m + 1) := by
    unfold θ; push_cast; ring
  rw [hsum, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [eq_div_iff hn.ne'] at hu
    have : ((u : ℝ) * (2 * m + 1)) * Real.pi = ((i + j + l : ℤ) : ℝ) * Real.pi := by
      linarith
    have := mul_right_cancel₀ hpi.ne' this
    have : (((i + j + l : ℤ)) : ℝ) = ((2 * (m : ℤ) + 1) * u : ℤ) := by
      push_cast at this ⊢; linarith
    exact_mod_cast this
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hu, eq_div_iff hn.ne']
    push_cast
    ring

lemma idx_line {m : ℕ} {i j l : ℤ} (hi : i ∈ I m) (hj : j ∈ I m) (hl : l ∈ I m)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    P m l ∈ line[ℝ, P m i, P m j] ↔ (2 * (m : ℤ) + 1) ∣ i + j + l := by
  unfold P
  rw [mem_line_iff (fun h => hij (tan_inj hi hj h)) (fun h => hil (tan_inj hi hl h))
    (fun h => hjl (tan_inj hj hl h)), ← sin_zero_iff]
  have e := tan_identity (cos_ne hi) (cos_ne hj) (cos_ne hl)
  have hc : Real.cos (θ m i) * Real.cos (θ m j) * Real.cos (θ m l) ≠ 0 := by
    have := cos_ne hi; have := cos_ne hj; have := cos_ne hl; positivity
  constructor
  · intro h
    have : Real.sin (θ m i + θ m j + θ m l) / (Real.cos (θ m i) * Real.cos (θ m j) *
        Real.cos (θ m l)) = 0 := by rw [← e]; linarith
    rcases div_eq_zero_iff.mp this with h' | h'
    · exact h'
    · exact absurd h' hc
  · intro h
    have : Real.tan (θ m i) + Real.tan (θ m j) + Real.tan (θ m l) -
        Real.tan (θ m i) * Real.tan (θ m j) * Real.tan (θ m l) = 0 := by rw [e, h]; simp
    linarith

/-- reduction into the window -/
def w (m : ℕ) (z : ℤ) : ℤ := (z + m) % (2 * (m : ℤ) + 1) - m

lemma w_mem (m : ℕ) (z : ℤ) : w m z ∈ I m := by
  have hn : (0 : ℤ) < (2 * (m : ℤ) + 1) := by positivity
  have h1 := Int.emod_nonneg (z + m) hn.ne'
  have h2 := Int.emod_lt_of_pos (z + m) hn
  simp only [I, Finset.mem_Icc, w]
  push_cast at h2 ⊢
  constructor <;> omega

lemma w_dvd (m : ℕ) (z : ℤ) : (2 * (m : ℤ) + 1) ∣ z - w m z := by
  unfold w
  rw [Int.emod_def]
  exact ⟨(z + m) / (2 * (m : ℤ) + 1), by ring⟩

lemma filter_card (m : ℕ) (L : AffineSubspace ℝ ℝ²) :
    ((S m).filter fun p => p ∈ L).card = ((I m).filter fun k => P m k ∈ L).card := by
  unfold S
  rw [Finset.filter_image]
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact P_inj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab

lemma card_S (m : ℕ) : (S m).card = 2 * m + 1 := by
  unfold S
  rw [Finset.card_image_of_injOn (fun a ha b hb hab => P_inj ha hb hab)]
  simp only [I, Int.card_Icc]
  omega

lemma le_three (m : ℕ) (L : AffineSubspace ℝ ℝ²) (hL : IsLine L) :
    ((S m).filter fun p => p ∈ L).card ≤ 3 := by
  rw [filter_card]
  by_contra hc
  push_neg at hc
  set J := (I m).filter fun k => P m k ∈ L with hJ
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
  have hc2 : 1 < ((J.erase i).erase j).card := by
    have h1 := Finset.card_erase_of_mem hi
    have h2 := Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)
    omega
  obtain ⟨l, hl, q, hq, hlq⟩ := Finset.one_lt_card.mp hc2
  simp only [Finset.mem_erase] at hl hq
  have hiJ := Finset.mem_filter.mp hi
  have hjJ := Finset.mem_filter.mp hj
  have hlJ := Finset.mem_filter.mp hl.2.2
  have hqJ := Finset.mem_filter.mp hq.2.2
  have hLeq : line[ℝ, P m i, P m j] = L :=
    line_pair_eq hL hiJ.2 hjJ.2 (fun h => hij (P_inj hiJ.1 hjJ.1 h))
  have d1 := (idx_line hiJ.1 hjJ.1 hlJ.1 hij (Ne.symm hl.2.1) (Ne.symm hl.1)).mp
    (hLeq ▸ hlJ.2)
  have d2 := (idx_line hiJ.1 hjJ.1 hqJ.1 hij (Ne.symm hq.2.1) (Ne.symm hq.1)).mp
    (hLeq ▸ hqJ.2)
  apply hlq
  apply uniq hlJ.1 hqJ.1
  have := dvd_sub d1 d2
  have e : i + j + l - (i + j + q) = l - q := by ring
  rwa [e] at this

lemma ge_two (m : ℕ) {L : AffineSubspace ℝ ℝ²} (hL : L ∈ determinedLines (S m)) :
    2 ≤ ((S m).filter fun p => p ∈ L).card := by
  have h := (determinedLines_eq.mp hL).2
  have hc : (((S m) : Set ℝ²) ∩ (L : Set ℝ²)).ncard = ((S m).filter fun p => p ∈ L).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp
  rw [hc] at h
  exact h

/-- the index set of the points of `S m` on `L` -/
noncomputable def g (m : ℕ) (L : AffineSubspace ℝ ℝ²) : Finset ℤ :=
  (I m).filter fun k => P m k ∈ L

lemma g_two {m : ℕ} {L : AffineSubspace ℝ ℝ²} (hL : L ∈ determinedLines (S m))
    (h3 : ((S m).filter fun p => p ∈ L).card ≠ 3) :
    ∃ i j, i ≠ j ∧ g m L = {i, j} := by
  have h2 := ge_two m hL
  have h3' := le_three m L (isLine_of_mem_determinedLines hL)
  rw [filter_card] at h2 h3 h3'
  have : (g m L).card = 2 := by unfold g; omega
  exact Finset.card_eq_two.mp this

lemma D2_le (m : ℕ) :
    ((determinedLines (S m)).filter fun L => ¬ ((S m).filter fun p => p ∈ L).card = 3).card ≤
      2 * m + 1 := by
  set T : Finset (Finset ℤ) := (I m).image (fun i => ({i, w m (-2 * i)} : Finset ℤ)) with hT
  have hTc : T.card ≤ 2 * m + 1 := by
    refine Finset.card_image_le.trans ?_
    simp only [I, Int.card_Icc]
    omega
  refine le_trans (Finset.card_le_card_of_injOn (g m) ?_ ?_) hTc
  · intro L hL
    have hL' := Finset.mem_filter.mp hL
    obtain ⟨i, j, hij, hg⟩ := g_two hL'.1 hL'.2
    have hi : i ∈ g m L := by rw [hg]; simp
    have hj : j ∈ g m L := by rw [hg]; simp
    have hiJ := Finset.mem_filter.mp hi
    have hjJ := Finset.mem_filter.mp hj
    have hLeq : line[ℝ, P m i, P m j] = L :=
      line_pair_eq (isLine_of_mem_determinedLines hL'.1) hiJ.2 hjJ.2
        (fun h => hij (P_inj hiJ.1 hjJ.1 h))
    set l := w m (-(i + j)) with hl
    have hlI : l ∈ I m := w_mem m _
    have hdl : (2 * (m : ℤ) + 1) ∣ i + j + l := by
      have := w_dvd m (-(i + j))
      have e : i + j + l = -(-(i + j) - w m (-(i + j))) := by rw [hl]; ring
      rw [e]
      exact (dvd_neg).mpr this
    have hlij : l = i ∨ l = j := by
      by_contra hne
      push_neg at hne
      have hmem := (idx_line hiJ.1 hjJ.1 hlI hij (Ne.symm hne.1) (Ne.symm hne.2)).mpr hdl
      rw [hLeq] at hmem
      have : l ∈ g m L := Finset.mem_filter.mpr ⟨hlI, hmem⟩
      rw [hg] at this
      simp at this
      tauto
    rw [hT, Finset.mem_coe, Finset.mem_image]
    rcases hlij with h | h
    · refine ⟨i, hiJ.1, ?_⟩
      rw [hg]
      have : j = w m (-2 * i) := by
        apply uniq hjJ.1 (w_mem m _)
        have := w_dvd m (-2 * i)
        have e : j - w m (-2 * i) = (i + j + l) + (-2 * i - w m (-2 * i)) := by rw [h]; ring
        rw [e]
        exact dvd_add hdl this
      rw [this]
    · refine ⟨j, hjJ.1, ?_⟩
      rw [hg]
      have : i = w m (-2 * j) := by
        apply uniq hiJ.1 (w_mem m _)
        have := w_dvd m (-2 * j)
        have e : i - w m (-2 * j) = (i + j + l) + (-2 * j - w m (-2 * j)) := by rw [h]; ring
        rw [e]
        exact dvd_add hdl this
      rw [this, Finset.pair_comm]
  · intro L hL L' hL' hgg
    have hL1 := Finset.mem_filter.mp hL
    have hL1' := Finset.mem_filter.mp hL'
    obtain ⟨i, j, hij, hg⟩ := g_two hL1.1 hL1.2
    have hi : i ∈ g m L := by rw [hg]; simp
    have hj : j ∈ g m L := by rw [hg]; simp
    have hi' : i ∈ g m L' := by rw [← hgg]; exact hi
    have hj' : j ∈ g m L' := by rw [← hgg]; exact hj
    have hiJ := Finset.mem_filter.mp hi
    have hjJ := Finset.mem_filter.mp hj
    have hiJ' := Finset.mem_filter.mp hi'
    have hjJ' := Finset.mem_filter.mp hj'
    have hne : P m i ≠ P m j := fun h => hij (P_inj hiJ.1 hjJ.1 h)
    rw [← line_pair_eq (isLine_of_mem_determinedLines hL1.1) hiJ.2 hjJ.2 hne,
      ← line_pair_eq (isLine_of_mem_determinedLines hL1'.1) hiJ'.2 hjJ'.2 hne]

lemma count (m : ℕ) :
    6 * ((determinedLines (S m)).filter fun L => ((S m).filter fun p => p ∈ L).card = 3).card +
      2 * ((determinedLines (S m)).filter
        fun L => ¬ ((S m).filter fun p => p ∈ L).card = 3).card = (2 * m + 1) * (2 * m) := by
  have h := ordered_pair_count (S m)
  rw [card_S, ← Finset.sum_filter_add_sum_filter_not _
    (fun L => ((S m).filter fun p => p ∈ L).card = 3)] at h
  have e1 : ∑ L ∈ (determinedLines (S m)).filter
      (fun L => ((S m).filter fun p => p ∈ L).card = 3),
      ((S m).filter fun p => p ∈ L).card * (((S m).filter fun p => p ∈ L).card - 1) =
      ∑ L ∈ (determinedLines (S m)).filter
      (fun L => ((S m).filter fun p => p ∈ L).card = 3), 6 := by
    apply Finset.sum_congr rfl
    intro L hL
    rw [(Finset.mem_filter.mp hL).2]
  have e2 : ∑ L ∈ (determinedLines (S m)).filter
      (fun L => ¬ ((S m).filter fun p => p ∈ L).card = 3),
      ((S m).filter fun p => p ∈ L).card * (((S m).filter fun p => p ∈ L).card - 1) =
      ∑ L ∈ (determinedLines (S m)).filter
      (fun L => ¬ ((S m).filter fun p => p ∈ L).card = 3), 2 := by
    apply Finset.sum_congr rfl
    intro L hL
    have hL' := Finset.mem_filter.mp hL
    have h2 := ge_two m hL'.1
    have h3 := le_three m L (isLine_of_mem_determinedLines hL'.1)
    have : ((S m).filter fun p => p ∈ L).card = 2 := by omega
    rw [this]
  rw [e1, e2, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul] at h
  have e3 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [e3] at h
  linarith

end OMA.O7

theorem OMA.solution : type_of% @Erdos211.erdos_211.variants.sharpness := by
  classical
  refine ⟨OMA.O7.S, ?_, fun m L hL => OMA.O7.le_three m L hL, ?_⟩
  · simp only [OMA.O7.card_S]
    exact Filter.tendsto_atTop_mono (fun m => show id m ≤ 2 * m + 1 by simp only [id]; omega)
      Filter.tendsto_id
  · simp only [OMA.O7.card_S]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun m : ℕ => 1 / 6 - 1 / ((m : ℝ) + 1))
      (h := fun _ => 1 / 6)
    · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := (tendsto_const_nhds (x := (1 / 6 : ℝ))).sub this
      rw [sub_zero] at h2
      exact h2
    · exact tendsto_const_nhds
    · intro m
      have hc := OMA.O7.count m
      have hd := OMA.O7.D2_le m
      set A := ((Erdos211.determinedLines (OMA.O7.S m)).filter
        fun L => ((OMA.O7.S m).filter fun p => p ∈ L).card = 3).card
      set B := ((Erdos211.determinedLines (OMA.O7.S m)).filter
        fun L => ¬ ((OMA.O7.S m).filter fun p => p ∈ L).card = 3).card
      have hcR : 6 * (A : ℝ) + 2 * B = (2 * m + 1) * (2 * m) := by exact_mod_cast hc
      have hdR : (B : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hd
      have hq : 1 / ((m : ℝ) + 1) * (2 * m + 1) ^ 2 = 4 * m + 1 / ((m : ℝ) + 1) := by
        field_simp; ring
      have hq0 : 0 < 1 / ((m : ℝ) + 1) := by positivity
      show 1 / 6 - 1 / ((m : ℝ) + 1) ≤ (A : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ 2
      rw [le_div_iff₀ (by positivity)]
      push_cast
      have hm : (0 : ℝ) ≤ m := by positivity
      have hqm : 1 / ((m : ℝ) + 1) * ((m : ℝ) + 1) = 1 := by field_simp
      have hqge : 1 - (m : ℝ) ≤ 1 / ((m : ℝ) + 1) := by nlinarith
      linarith
    · intro m
      have hc := OMA.O7.count m
      set A := ((Erdos211.determinedLines (OMA.O7.S m)).filter
        fun L => ((OMA.O7.S m).filter fun p => p ∈ L).card = 3).card
      set B := ((Erdos211.determinedLines (OMA.O7.S m)).filter
        fun L => ¬ ((OMA.O7.S m).filter fun p => p ∈ L).card = 3).card
      have hcR : 6 * (A : ℝ) + 2 * B = (2 * m + 1) * (2 * m) := by exact_mod_cast hc
      show (A : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 6
      rw [div_le_iff₀ (by positivity)]
      push_cast
      have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
      have hm : (0 : ℝ) ≤ m := by positivity
      linarith
