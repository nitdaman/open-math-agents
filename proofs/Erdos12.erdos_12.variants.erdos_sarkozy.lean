import FormalConjectures.ErdosProblems.«12»

-- Problem: Erdős Problem 12 — erdos sarkozy
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/12.lean:106 (declaration Erdos12.erdos_12.variants.erdos_sarkozy)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

section Erdos12Sarkozy

open Filter Set

private noncomputable def chooseM (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (P prevN : ℕ) : ℕ :=
  let C := Classical.choose (eventually_atTop.mp (tendsto_atTop.mp hf (4 * P + 1)))
  max 2 (max prevN C)

private lemma two_le_chooseM (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (P prevN : ℕ) :
    2 ≤ chooseM f hf P prevN :=
  le_max_left _ _

private lemma prevN_le_chooseM (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (P prevN : ℕ) :
    prevN ≤ chooseM f hf P prevN :=
  le_trans (le_max_left _ _) (le_max_right _ _)

private lemma lt_f_of_chooseM_le (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (P prevN n : ℕ)
    (hn : chooseM f hf P prevN ≤ n) : 4 * P < f n := by
  have hC := Classical.choose_spec (eventually_atTop.mp (tendsto_atTop.mp hf (4 * P + 1)))
  have hle : Classical.choose (eventually_atTop.mp (tendsto_atTop.mp hf (4 * P + 1))) ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hfn := hC n hle
  omega

private noncomputable def state (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 =>
    let (P, prevN) := state f hf k
    let m := chooseM f hf P prevN
    let blk := (Finset.Ico m (2 * m)).image (fun t => 1 + 2 * P * t)
    (P * ∏ a ∈ blk, a, 4 * P * m)

private noncomputable def P_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  (state f hf k).1

private noncomputable def prevN_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  (state f hf k).2

private noncomputable def m_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  chooseM f hf (P_seq f hf k) (prevN_seq f hf k)

private noncomputable def M_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  2 * P_seq f hf k * m_seq f hf k

private noncomputable def N_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  4 * P_seq f hf k * m_seq f hf k

private noncomputable def blk_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : Finset ℕ :=
  (Finset.Ico (m_seq f hf k) (2 * m_seq f hf k)).image (fun t => 1 + 2 * P_seq f hf k * t)

private lemma P_seq_pos (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) : ∀ k, 1 ≤ P_seq f hf k
  | 0 => le_rfl
  | k + 1 => by
    have hk := P_seq_pos f hf k
    have hprod : 1 ≤ ∏ a ∈ blk_seq f hf k, a := by
      apply Finset.one_le_prod'
      intro a ha
      rw [blk_seq, Finset.mem_image] at ha
      rcases ha with ⟨t, _, rfl⟩
      omega
    change 1 ≤ P_seq f hf k * ∏ a ∈ blk_seq f hf k, a
    nlinarith

private lemma P_seq_dvd_succ (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    P_seq f hf k ∣ P_seq f hf (k + 1) :=
  dvd_mul_right _ _

private lemma mem_blk_dvd_P_seq_succ (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k a : ℕ)
    (ha : a ∈ blk_seq f hf k) : a ∣ P_seq f hf (k + 1) := by
  have hd : a ∣ ∏ x ∈ blk_seq f hf k, x := Finset.dvd_prod_of_mem _ ha
  exact dvd_trans hd (dvd_mul_left _ _)

private lemma mem_blk_dvd_P_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {i k : ℕ}
    (hik : i < k) {a : ℕ} (ha : a ∈ blk_seq f hf i) : a ∣ P_seq f hf k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hik) with hlt | rfl
    · exact dvd_trans (ih hlt) (P_seq_dvd_succ f hf k)
    · exact mem_blk_dvd_P_seq_succ f hf i a ha

private lemma prevN_seq_succ (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    prevN_seq f hf (k + 1) = N_seq f hf k :=
  rfl

private lemma prevN_lt_M_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    prevN_seq f hf k < M_seq f hf k := by
  have hP := P_seq_pos f hf k
  have hm2 : 2 ≤ m_seq f hf k := two_le_chooseM f hf (P_seq f hf k) (prevN_seq f hf k)
  have hmN : prevN_seq f hf k ≤ m_seq f hf k := prevN_le_chooseM f hf (P_seq f hf k) (prevN_seq f hf k)
  change prevN_seq f hf k < 2 * P_seq f hf k * m_seq f hf k
  nlinarith

private lemma M_seq_lt_N_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    M_seq f hf k < N_seq f hf k := by
  have hP := P_seq_pos f hf k
  have hm2 : 2 ≤ m_seq f hf k := two_le_chooseM f hf (P_seq f hf k) (prevN_seq f hf k)
  change 2 * P_seq f hf k * m_seq f hf k < 4 * P_seq f hf k * m_seq f hf k
  nlinarith

private lemma N_seq_lt_M_seq_succ (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    N_seq f hf k < M_seq f hf (k + 1) := by
  rw [← prevN_seq_succ]
  exact prevN_lt_M_seq f hf (k + 1)

private lemma N_seq_lt_M_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {i j : ℕ}
    (hij : i < j) : N_seq f hf i < M_seq f hf j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hij) with hlt | rfl
    · exact lt_trans (ih hlt) (lt_trans (M_seq_lt_N_seq f hf j) (N_seq_lt_M_seq_succ f hf j))
    · exact N_seq_lt_M_seq_succ f hf i

private lemma N_seq_strictMono (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) :
    StrictMono (N_seq f hf) := by
  intro i j hij
  exact lt_trans (N_seq_lt_M_seq f hf hij) (M_seq_lt_N_seq f hf j)

private lemma le_M_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    k ≤ M_seq f hf k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h1 := lt_trans (M_seq_lt_N_seq f hf k) (N_seq_lt_M_seq_succ f hf k)
    omega

private lemma le_N_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    k ≤ N_seq f hf k :=
  le_trans (le_M_seq f hf k) (le_of_lt (M_seq_lt_N_seq f hf k))

private lemma mem_blk_bounds (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {k x : ℕ}
    (hx : x ∈ blk_seq f hf k) : M_seq f hf k < x ∧ x < N_seq f hf k := by
  rw [blk_seq, Finset.mem_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  rw [Finset.mem_Ico] at ht
  have hP := P_seq_pos f hf k
  unfold M_seq N_seq
  constructor <;> nlinarith

private lemma mem_blk_odd (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {k x : ℕ}
    (hx : x ∈ blk_seq f hf k) : x % 2 = 1 := by
  rw [blk_seq, Finset.mem_image] at hx
  rcases hx with ⟨t, _, rfl⟩
  rw [mul_assoc]
  omega

private lemma mem_blk_five_le (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {k x : ℕ}
    (hx : x ∈ blk_seq f hf k) : 5 ≤ x := by
  have hP := P_seq_pos f hf k
  have hm : 2 ≤ m_seq f hf k := two_le_chooseM f hf (P_seq f hf k) (prevN_seq f hf k)
  rw [blk_seq, Finset.mem_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  rw [Finset.mem_Ico] at ht
  nlinarith

private lemma mem_blk_mod_P (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {i k x : ℕ}
    (hik : i < k) {a : ℕ} (ha : a ∈ blk_seq f hf i) (hx : x ∈ blk_seq f hf k) :
    ∃ q : ℕ, x = 1 + a * q := by
  have hdvd : a ∣ P_seq f hf k := mem_blk_dvd_P_seq f hf hik ha
  rcases hdvd with ⟨r, hr⟩
  rw [blk_seq, Finset.mem_image] at hx
  rcases hx with ⟨t, _, rfl⟩
  refine ⟨2 * r * t, ?_⟩
  rw [hr]
  ring

private lemma blk_order (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {i j x y : ℕ}
    (hx : x ∈ blk_seq f hf i) (hy : y ∈ blk_seq f hf j) (hxy : x < y) : i ≤ j := by
  by_contra hji
  have hji' : j < i := Nat.lt_of_not_ge hji
  have hyN : y < N_seq f hf j := (mem_blk_bounds f hf hy).2
  have hMx : M_seq f hf i < x := (mem_blk_bounds f hf hx).1
  have hNM : N_seq f hf j < M_seq f hf i := N_seq_lt_M_seq f hf hji'
  omega

private lemma blk_card (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    (blk_seq f hf k).card = m_seq f hf k := by
  rw [blk_seq, Finset.card_image_of_injective]
  · rw [Nat.card_Ico]
    omega
  · intro t1 t2 ht
    have hP := P_seq_pos f hf k
    nlinarith

private noncomputable def A_set (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) : Set ℕ :=
  ⋃ k, (blk_seq f hf k : Set ℕ)

private lemma A_set_infinite (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) :
    (A_set f hf).Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro B
  refine ⟨1 + 2 * P_seq f hf B * m_seq f hf B, ?_, ?_⟩
  · rw [A_set, Set.mem_iUnion]
    refine ⟨B, ?_⟩
    rw [Finset.mem_coe, blk_seq, Finset.mem_image]
    refine ⟨m_seq f hf B, Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩, rfl⟩
    have hm : 2 ≤ m_seq f hf B := two_le_chooseM f hf (P_seq f hf B) (prevN_seq f hf B)
    omega
  · have hP := P_seq_pos f hf B
    have hm : 2 ≤ m_seq f hf B := two_le_chooseM f hf (P_seq f hf B) (prevN_seq f hf B)
    have hB := le_M_seq f hf B
    change B < 1 + 2 * P_seq f hf B * m_seq f hf B
    unfold M_seq at hB
    nlinarith

private lemma A_set_isGood (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) :
    Erdos12.IsGood (A_set f hf) := by
  refine ⟨A_set_infinite f hf, ?_⟩
  intro a ha b hb c hc hdvd hab hac
  rw [A_set, Set.mem_iUnion] at ha hb hc
  rcases ha with ⟨i, ha⟩
  rcases hb with ⟨j, hb⟩
  rcases hc with ⟨k, hc⟩
  rw [Finset.mem_coe] at ha hb hc
  have hij : i ≤ j := blk_order f hf ha hb hab
  have hik : i ≤ k := blk_order f hf ha hc hac
  suffices h : ∀ (j' k' : ℕ) (b' c' : ℕ),
      j' ≤ k' → i ≤ j' → b' ∈ blk_seq f hf j' → c' ∈ blk_seq f hf k' →
      a ∣ b' + c' → a < b' → a < c' → False by
    rcases le_total j k with hjk | hkj
    · exact False.elim (h j k b c hjk hij hb hc hdvd hab hac)
    · exact False.elim (h k j c b hkj hik hc hb (by simpa [add_comm] using hdvd) hac hab)
  intro j' k' b' c' hjk hij' hb' hc' hdvd' hab' hac'
  rcases lt_or_eq_of_le hij' with hij_lt | rfl
  · have hik_lt : i < k' := lt_of_lt_of_le hij_lt hjk
    rcases mem_blk_mod_P f hf hij_lt ha hb' with ⟨q1, hq1⟩
    rcases mem_blk_mod_P f hf hik_lt ha hc' with ⟨q2, hq2⟩
    have hsum : b' + c' = 2 + a * (q1 + q2) := by rw [hq1, hq2]; ring
    rw [hsum] at hdvd'
    have hdvd2 : a ∣ 2 := (Nat.dvd_add_left ⟨q1 + q2, rfl⟩).mp hdvd'
    have ha2 : a ≤ 2 := Nat.le_of_dvd (by decide) hdvd2
    have ha5 := mem_blk_five_le f hf ha
    omega
  · rcases lt_or_eq_of_le hjk with hjk_lt | rfl
    · rcases mem_blk_mod_P f hf hjk_lt ha hc' with ⟨q, hq⟩
      have hsum : b' + c' = (b' + 1) + a * q := by rw [hq]; ring
      rw [hsum] at hdvd'
      have hdvd1 : a ∣ b' + 1 := (Nat.dvd_add_left ⟨q, rfl⟩).mp hdvd'
      rcases hdvd1 with ⟨s, hs⟩
      have haM := (mem_blk_bounds f hf ha).1
      have hbN := (mem_blk_bounds f hf hb').2
      have hN : N_seq f hf i = 2 * M_seq f hf i := by unfold N_seq M_seq; ring
      have hs2 : 2 ≤ s := by nlinarith
      nlinarith
    · rcases hdvd' with ⟨s, hs⟩
      have haM := (mem_blk_bounds f hf ha).1
      have hbN := (mem_blk_bounds f hf hb').2
      have hcN := (mem_blk_bounds f hf hc').2
      have hN : N_seq f hf i = 2 * M_seq f hf i := by unfold N_seq M_seq; ring
      have hs3 : s = 3 := by nlinarith
      have ha_odd := mem_blk_odd f hf ha
      have hb_odd := mem_blk_odd f hf hb'
      have hc_odd := mem_blk_odd f hf hc'
      rw [hs3] at hs
      omega

end Erdos12Sarkozy

theorem OMA.solution : type_of% @Erdos12.erdos_12.variants.erdos_sarkozy := by
  intro f hf
  refine ⟨A_set f hf, A_set_isGood f hf, ?_⟩
  rw [Set.infinite_iff_exists_gt]
  intro B
  let k := B + 1
  let N := N_seq f hf k
  refine ⟨N, ?_, ?_⟩
  · change (N : ℝ) / f N < ((A_set f hf ∩ Set.Icc 1 N).ncard : ℝ)
    have hP := P_seq_pos f hf k
    have hm : 2 ≤ m_seq f hf k := two_le_chooseM f hf (P_seq f hf k) (prevN_seq f hf k)
    have hmN : m_seq f hf k ≤ N := by
      change m_seq f hf k ≤ 4 * P_seq f hf k * m_seq f hf k
      nlinarith
    have hfN : 4 * P_seq f hf k < f N := lt_f_of_chooseM_le f hf _ _ N hmN
    have hNpos : 0 < N := by
      change 0 < 4 * P_seq f hf k * m_seq f hf k
      nlinarith
    have hsub : (blk_seq f hf k : Set ℕ) ⊆ A_set f hf ∩ Set.Icc 1 N := by
      intro x hx
      rw [Finset.mem_coe] at hx
      refine ⟨?_, ?_, ?_⟩
      · rw [A_set, Set.mem_iUnion]
        exact ⟨k, hx⟩
      · have := mem_blk_five_le f hf hx
        omega
      · exact le_of_lt (mem_blk_bounds f hf hx).2
    have hfin : (A_set f hf ∩ Set.Icc 1 N).Finite :=
      (Set.finite_Icc 1 N).subset Set.inter_subset_right
    have hcard : m_seq f hf k ≤ (A_set f hf ∩ Set.Icc 1 N).ncard := by
      rw [← blk_card f hf k, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub hfin
    have h1 : (N : ℝ) / (f N : ℝ) < (N : ℝ) / ((4 * P_seq f hf k : ℕ) : ℝ) := by
      apply div_lt_div_of_pos_left
      · exact Nat.cast_pos.mpr hNpos
      · exact Nat.cast_pos.mpr (by nlinarith)
      · exact Nat.cast_lt.mpr hfN
    have h2 : (N : ℝ) / ((4 * P_seq f hf k : ℕ) : ℝ) = (m_seq f hf k : ℝ) := by
      have hNeq : N = 4 * P_seq f hf k * m_seq f hf k := rfl
      rw [hNeq]
      push_cast
      have hPne : (P_seq f hf k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    have h3 : (m_seq f hf k : ℝ) ≤ ((A_set f hf ∩ Set.Icc 1 N).ncard : ℝ) :=
      Nat.cast_le.mpr hcard
    linarith
  · have hN := le_N_seq f hf k
    omega
