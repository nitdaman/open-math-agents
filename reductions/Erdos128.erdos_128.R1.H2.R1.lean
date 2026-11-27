import OMAReductions.R_Erdos128_erdos_128_R1

-- Reduction Erdos128.erdos_128.R1.H2.R1 of step Erdos128.erdos_128.R1.H2
-- Credit: @ashnewmanjones
--
-- Step H2 asks for a sparse half (a set of at least (n - 1) / 2 vertices spanning at most
-- n^2 / 50 edges) in every triangle-free graph with 2 n^2 / 25 < e < n^2 / 5 edges.
-- Here the range e ≤ n^2 / 12 is PROVED (sparse12), formalizing Proposition 1.2 of Keevash and
-- Sudakov, Sparse halves in triangle-free graphs, JCTB 96 (2006): take the neighbourhood N of a
-- vertex of maximum degree (independent, of size at least 2e / n) and either a sparse n/2-subset of
-- its complement or N plus a sparse completion, both found by an exact averaging argument.
-- The remaining open range is split at 3 n^2 / 20, the density of the Petersen blow-up, which
-- Keevash and Sudakov single out as the hardest regime:
--   H1: n^2 / 12 < e ≤ 3 n^2 / 20,   H2: 3 n^2 / 20 < e < n^2 / 5.

namespace OMA.R_Erdos128_erdos_128_R1_H2_R1

open Finset OMA.R_Erdos128_erdos_128_R1

-- Lower middle range (open): between n^2 / 12 and 3 n^2 / 20 edges.
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    Fintype.card V ^ 2 < 12 * G.edgeSet.ncard →
    20 * G.edgeSet.ncard ≤ 3 * Fintype.card V ^ 2 →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

-- Upper middle range (open): between 3 n^2 / 20 and n^2 / 5 edges.
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    3 * Fintype.card V ^ 2 < 20 * G.edgeSet.ncard →
    5 * G.edgeSet.ncard < Fintype.card V ^ 2 →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2
/-! ## Polynomial endgame (real arithmetic) -/

lemma odd1 (k s : ℝ) (hs0 : 0 ≤ s) (h6 : 6 * s ≤ 2 * k + 1) (hsk : s + 1 ≤ k) :
    25 * s * (k - s) * (k * (k - 1)) ≤
      (2 * k + 1) * (2 * k + 1 - s) * (k * (k - 1) + (k - s) * (k + 1)) := by
  have hk : 1 ≤ k := by linarith
  have A : 0 ≤ (2 * k + 1 - 6 * s) := by linarith
  have B : 0 ≤ (4 * (2 * k + 1) - 9 * s) := by linarith
  nlinarith [mul_nonneg (mul_nonneg A B) (by linarith : (0:ℝ) ≤ k), mul_nonneg A B,
    mul_nonneg (mul_nonneg A hs0) (by linarith : (0:ℝ) ≤ k), mul_nonneg hs0 (by linarith : (0:ℝ) ≤ k - s),
    mul_nonneg (mul_nonneg hs0 (by linarith : (0:ℝ) ≤ k - s)) (by linarith : (0:ℝ) ≤ k),
    mul_nonneg (mul_nonneg A (by linarith : (0:ℝ) ≤ k)) (by linarith : (0:ℝ) ≤ k)]

lemma odd2 (k s : ℝ) (hs0 : 0 ≤ s) (h6 : 2 * k + 1 ≤ 6 * s) (hsk : s + 1 ≤ k) :
    50 * (k - s) * (k * (k - 1)) ≤
      12 * (2 * k + 1 - s) * (k * (k - 1) + (k - s) * (k + 1)) := by
  have hk : 1 ≤ k := by linarith
  have A : 0 ≤ 6 * s - (2 * k + 1) := by linarith
  have B : 0 ≤ 4 * s + 2 * k + 1 := by linarith
  nlinarith [mul_nonneg (mul_nonneg A B) (by linarith : (0:ℝ) ≤ k), mul_nonneg A B,
    mul_nonneg (mul_nonneg A (by linarith : (0:ℝ) ≤ k - s)) (by linarith : (0:ℝ) ≤ k),
    mul_nonneg (mul_nonneg A (by linarith : (0:ℝ) ≤ k)) (by linarith : (0:ℝ) ≤ k),
    mul_nonneg (by linarith : (0:ℝ) ≤ k - s) (by linarith : (0:ℝ) ≤ k)]

lemma even1 (k s : ℝ) (hs0 : 0 ≤ s) (h6 : 6 * s ≤ 2 * k) (hsk : s + 1 ≤ k) :
    25 * s * (k - s) * (k * (k - 1)) ≤
      (2 * k) * (2 * k - s) * (k * (k - 1) + (k - s) * k) := by
  have hk : 1 ≤ k := by linarith
  have A : 0 ≤ (2 * k - 6 * s) := by linarith
  have B : 0 ≤ (4 * (2 * k) - 9 * s) := by linarith
  nlinarith [mul_nonneg (mul_nonneg A B) (by linarith : (0:ℝ) ≤ k), mul_nonneg A B,
    mul_nonneg (mul_nonneg A hs0) (by linarith : (0:ℝ) ≤ k), mul_nonneg hs0 (by linarith : (0:ℝ) ≤ k - s),
    mul_nonneg (mul_nonneg hs0 (by linarith : (0:ℝ) ≤ k - s)) (by linarith : (0:ℝ) ≤ k),
    mul_nonneg (mul_nonneg A (by linarith : (0:ℝ) ≤ k)) (by linarith : (0:ℝ) ≤ k)]

lemma even2 (k s : ℝ) (hs0 : 0 ≤ s) (h6 : 2 * k ≤ 6 * s) (hsk : s + 1 ≤ k) :
    50 * (k - s) * (k * (k - 1)) ≤
      12 * (2 * k - s) * (k * (k - 1) + (k - s) * k) := by
  have hk : 1 ≤ k := by linarith
  have A : 0 ≤ 6 * s - 2 * k := by linarith
  have B : 0 ≤ 4 * s + 2 * k := by linarith
  nlinarith [mul_nonneg (mul_nonneg A B) (by linarith : (0:ℝ) ≤ k), mul_nonneg A B,
    mul_nonneg (mul_nonneg A (by linarith : (0:ℝ) ≤ k - s)) (by linarith : (0:ℝ) ≤ k),
    mul_nonneg (mul_nonneg A (by linarith : (0:ℝ) ≤ k)) (by linarith : (0:ℝ) ≤ k),
    mul_nonneg (by linarith : (0:ℝ) ≤ k - s) (by linarith : (0:ℝ) ≤ k)]

-- The key inequality 50 e y k(k-1) ≤ n² x (k(k-1) + y (n-k)), x = n - s, y = k - s.
lemma key_bound (n k s e : ℝ) (hpar : n = 2 * k ∨ n = 2 * k + 1) (hs0 : 0 ≤ s) (hsk : s + 1 ≤ k)
    (he : 0 ≤ e) (h1 : 2 * e ≤ n * s) (h2 : 12 * e ≤ n ^ 2) :
    50 * e * (k - s) * (k * (k - 1)) ≤ n ^ 2 * (n - s) * (k * (k - 1) + (k - s) * (n - k)) := by
  have hk : 1 ≤ k := by linarith
  have hP : 0 ≤ (k - s) * (k * (k - 1)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hn : 0 ≤ n := by rcases hpar with h | h <;> linarith
  rcases le_or_gt (6 * s) n with h6 | h6
  · -- 50 e ≤ 25 n s
    have a : 50 * e * ((k - s) * (k * (k - 1))) ≤ 25 * n * s * ((k - s) * (k * (k - 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) hP
    have b : 25 * s * (k - s) * (k * (k - 1)) ≤ n * (n - s) * (k * (k - 1) + (k - s) * (n - k)) := by
      rcases hpar with h | h
      · subst h; have := even1 k s hs0 (by linarith) hsk; nlinarith
      · subst h; have := odd1 k s hs0 (by linarith) hsk
        have e1 : (2 * k + 1 - k) = k + 1 := by ring
        rw [e1]; exact this
    have c := mul_le_mul_of_nonneg_left b hn
    nlinarith
  · have a : 50 * e * ((k - s) * (k * (k - 1))) ≤ 50 * (n ^ 2 / 12) * ((k - s) * (k * (k - 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) hP
    have b : 50 * (k - s) * (k * (k - 1)) ≤ 12 * (n - s) * (k * (k - 1) + (k - s) * (n - k)) := by
      rcases hpar with h | h
      · subst h; have := even2 k s hs0 (by linarith) hsk
        have e1 : (2 * k - k) = k := by ring
        rw [e1]; exact this
      · subst h; have := odd2 k s hs0 (by linarith) hsk
        have e1 : (2 * k + 1 - k) = k + 1 := by ring
        rw [e1]; exact this
    have c := mul_le_mul_of_nonneg_left b (sq_nonneg n)
    nlinarith

-- Real endgame: one of the two candidate halves is sparse.
lemma endgameR (n k s e DX aX DA T : ℝ) (hpar : n = 2 * k ∨ n = 2 * k + 1) (hs0 : 0 ≤ s)
    (hsk : s + 1 ≤ k) (hDX : 0 ≤ DX) (haX : 0 ≤ aX) (hDA : 0 ≤ DA) (hT : 0 ≤ T)
    (he : 2 * e = DX + 2 * aX) (hmax : 2 * e ≤ n * s) (h12 : 12 * e ≤ n ^ 2)
    (hA : DA * ((n - s) * (n - s - 1)) ≤ k * (k - 1) * DX)
    (hB : T * ((n - s) * (n - s - 1)) ≤ 2 * (k - s) * (n - s - 1) * aX + (k - s) * (k - s - 1) * DX) :
    25 * DA ≤ n ^ 2 ∨ 25 * T ≤ n ^ 2 := by
  have hk : 1 ≤ k := by linarith
  have hnk : k ≤ n - k := by rcases hpar with h | h <;> linarith
  have hx1 : 1 ≤ n - s - 1 := by linarith
  have hN : 0 < (n - s) * (n - s - 1) := by nlinarith
  have he0 : 0 ≤ e := by linarith
  by_cases hc : 25 * (k * (k - 1)) * DX ≤ n ^ 2 * ((n - s) * (n - s - 1))
  · left
    have : 25 * DA * ((n - s) * (n - s - 1)) ≤ n ^ 2 * ((n - s) * (n - s - 1)) := by nlinarith
    exact le_of_mul_le_mul_right this hN
  · right
    rw [not_le] at hc
    have hkk : 0 < k * (k - 1) := by
      by_contra hneg
      rw [not_lt] at hneg
      have : 25 * (k * (k - 1)) * DX ≤ 0 := by
        have := mul_le_mul_of_nonneg_right hneg hDX
        nlinarith
      nlinarith [mul_pos (by positivity : (0:ℝ) < n ^ 2 + 1) hN, sq_nonneg n]
    have G := key_bound n k s e hpar hs0 hsk he0 hmax h12
    have hy : 0 ≤ (k - s) * ((n - s) - (k - s)) := mul_nonneg (by linarith) (by linarith)
    -- 25 T x(x-1) ≤ 25 (y (x-1) 2e - y (x - y) DX)
    have h3 : 25 * T * ((n - s) * (n - s - 1)) ≤
        25 * ((k - s) * (n - s - 1) * (2 * e) - (k - s) * ((n - s) - (k - s)) * DX) := by
      rw [he]; nlinarith
    have h4 : (k * (k - 1)) * (25 * T * ((n - s) * (n - s - 1))) ≤
        (k * (k - 1)) * (n ^ 2 * ((n - s) * (n - s - 1))) := by
      have := mul_le_mul_of_nonneg_left h3 hkk.le
      have h5 : (k - s) * ((n - s) - (k - s)) * (n ^ 2 * ((n - s) * (n - s - 1))) ≤
          (k - s) * ((n - s) - (k - s)) * (25 * (k * (k - 1)) * DX) :=
        mul_le_mul_of_nonneg_left hc.le hy
      have h6 := mul_le_mul_of_nonneg_right G (by linarith : (0:ℝ) ≤ n - s - 1)
      nlinarith
    have h7 : 25 * T * ((n - s) * (n - s - 1)) ≤ n ^ 2 * ((n - s) * (n - s - 1)) :=
      le_of_mul_le_mul_left h4 hkk
    have h8 : 25 * T * ((n - s) * (n - s - 1)) = (25 * T) * ((n - s) * (n - s - 1)) := by ring
    exact le_of_mul_le_mul_right (h8 ▸ h7) hN

/-! ## Graph lemmas -/

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma sum_sum_erase (S : Finset V) (c : V → ℕ) :
    ∑ v ∈ S, ∑ u ∈ S.erase v, c u + ∑ u ∈ S, c u = S.card * ∑ u ∈ S, c u := by
  calc ∑ v ∈ S, ∑ u ∈ S.erase v, c u + ∑ u ∈ S, c u
      = ∑ v ∈ S, (∑ u ∈ S.erase v, c u + c v) := by rw [Finset.sum_add_distrib]
    _ = ∑ _v ∈ S, ∑ u ∈ S, c u := Finset.sum_congr rfl fun v hv => Finset.sum_erase_add S c hv
    _ = S.card * ∑ u ∈ S, c u := by rw [Finset.sum_const, smul_eq_mul]

-- One deletion step of the weighted potential 2 y m' a + y (y-1) D.
lemma avg_step (Z Y : Finset V) (y m : ℕ) (hY : Y.card = m + 2) :
    ∃ v ∈ Y, (m + 2) * (2 * y * m * ∑ u ∈ Y.erase v, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y.erase v, ((Y.erase v).filter (G.Adj u)).card) ≤
      m * (2 * y * (m + 1) * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y, (Y.filter (G.Adj u)).card) := by
  have hne : Y.Nonempty := by rw [← Finset.card_pos, hY]; omega
  apply Finset.exists_le_of_sum_le hne
  have ha := sum_sum_erase Y (fun u => (Z.filter (G.Adj u)).card)
  have hD := deg_sum_erase_total G Y
  rw [hY] at ha hD
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, hY, smul_eq_mul]
  generalize ∑ v ∈ Y, ∑ u ∈ Y.erase v, (Z.filter (G.Adj u)).card = A at ha ⊢
  generalize ∑ u ∈ Y, (Z.filter (G.Adj u)).card = a at ha ⊢
  generalize ∑ v ∈ Y, ∑ u ∈ Y.erase v, ((Y.erase v).filter (G.Adj u)).card = B at hD ⊢
  generalize ∑ u ∈ Y, (Y.filter (G.Adj u)).card = D at hD ⊢
  have hA : A = (m + 1) * a := by nlinarith
  have hB : B = m * D := by nlinarith
  subst hA hB
  apply le_of_eq
  ring

-- Repeated deletion keeps the potential below its proportional share.
lemma avg_descend (X Z : Finset V) (y : ℕ) (hy : 1 ≤ y) : ∀ d, d + y ≤ X.card →
    ∃ Y ⊆ X, Y.card = X.card - d ∧
      (2 * y * (X.card - d - 1) * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y, (Y.filter (G.Adj u)).card) * (X.card * (X.card - 1)) ≤
      (X.card - d) * (X.card - d - 1) * (2 * y * (X.card - 1) * ∑ u ∈ X, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ X, (X.filter (G.Adj u)).card) := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨X, subset_refl _, by simp, ?_⟩
    simp only [Nat.sub_zero]
    exact le_of_eq (by ring)
  | succ d ih =>
    intro hd
    obtain ⟨Y, hYX, hY, hb⟩ := ih (by omega)
    obtain ⟨m, hm⟩ : ∃ m, X.card - d = m + 2 := ⟨X.card - d - 2, by omega⟩
    obtain ⟨v, hv, hstep⟩ := avg_step G Z Y y m (by rw [hY, hm])
    refine ⟨Y.erase v, (Finset.erase_subset v Y).trans hYX, by
      rw [Finset.card_erase_of_mem hv, hY]; omega, ?_⟩
    have e1 : X.card - d - 1 = m + 1 := by omega
    have e2 : X.card - (d + 1) = m + 1 := by omega
    have e3 : X.card - (d + 1) - 1 = m := by omega
    rw [e1, hm] at hb
    rw [e3, e2]
    generalize (2 * y * m * ∑ u ∈ Y.erase v, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y.erase v, ((Y.erase v).filter (G.Adj u)).card) = P at hstep ⊢
    generalize (2 * y * (m + 1) * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y, (Y.filter (G.Adj u)).card) = Q at hstep hb
    generalize (X.card * (X.card - 1)) = N at hb ⊢
    generalize (2 * y * (X.card - 1) * ∑ u ∈ X, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ X, (X.filter (G.Adj u)).card) = C at hb ⊢
    have h1 : (m + 2) * (P * N) ≤ (m + 2) * ((m + 1) * m * C) := by
      calc (m + 2) * (P * N) = ((m + 2) * P) * N := by ring
        _ ≤ (m * Q) * N := Nat.mul_le_mul_right _ hstep
        _ = m * (Q * N) := by ring
        _ ≤ m * ((m + 2) * (m + 1) * C) := Nat.mul_le_mul_left _ hb
        _ = (m + 2) * ((m + 1) * m * C) := by ring
    exact Nat.le_of_mul_le_mul_left h1 (by omega)

-- Averaging fact (ii) of Keevash and Sudakov, with exact weights: for 1 ≤ y ≤ |X| some
-- y-subset Y of X has 2 e(Y, Z) + 2 e(Y) ≤ (2 y (x-1) e(X, Z) + y (y-1) 2 e(X)) / (x (x-1)).
lemma avg_two (X Z : Finset V) (y : ℕ) (hy : 1 ≤ y) (hyx : y ≤ X.card) :
    ∃ Y ⊆ X, Y.card = y ∧
      (2 * ∑ u ∈ Y, (Z.filter (G.Adj u)).card + ∑ u ∈ Y, (Y.filter (G.Adj u)).card) *
          (X.card * (X.card - 1)) ≤
        2 * y * (X.card - 1) * ∑ u ∈ X, (Z.filter (G.Adj u)).card +
          y * (y - 1) * ∑ u ∈ X, (X.filter (G.Adj u)).card := by
  rcases Nat.lt_or_ge y 2 with hy2 | hy2
  · -- y = 1: a single vertex with few neighbours in Z
    have hy1 : y = 1 := by omega
    subst hy1
    have hne : X.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨u, hu, hle⟩ := Finset.exists_le_of_sum_le hne
      (f := fun u => X.card * (Z.filter (G.Adj u)).card)
      (g := fun _ => ∑ w ∈ X, (Z.filter (G.Adj w)).card) (by rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul])
    refine ⟨{u}, Finset.singleton_subset_iff.mpr hu, by simp, ?_⟩
    simp only [Finset.sum_singleton, Nat.sub_self, mul_zero, zero_mul, add_zero]
    have h0 : (({u} : Finset V).filter (G.Adj u)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w hw; rw [Finset.mem_singleton] at hw; subst hw; exact G.loopless.irrefl _
    rw [h0, add_zero]
    calc 2 * (Z.filter (G.Adj u)).card * (X.card * (X.card - 1))
        = 2 * (X.card - 1) * (X.card * (Z.filter (G.Adj u)).card) := by ring
      _ ≤ 2 * (X.card - 1) * ∑ w ∈ X, (Z.filter (G.Adj w)).card := Nat.mul_le_mul_left _ hle
      _ = 2 * 1 * (X.card - 1) * ∑ w ∈ X, (Z.filter (G.Adj w)).card := by ring
  · obtain ⟨Y, hYX, hY, hb⟩ := avg_descend G X Z y hy (X.card - y) (by omega)
    have e1 : X.card - (X.card - y) = y := by omega
    rw [e1] at hY hb
    refine ⟨Y, hYX, hY, ?_⟩
    have hyy : 0 < y * (y - 1) := Nat.mul_pos (by omega) (by omega)
    apply Nat.le_of_mul_le_mul_left _ hyy
    calc y * (y - 1) * ((2 * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
          ∑ u ∈ Y, (Y.filter (G.Adj u)).card) * (X.card * (X.card - 1)))
        = (2 * y * (y - 1) * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
          y * (y - 1) * ∑ u ∈ Y, (Y.filter (G.Adj u)).card) * (X.card * (X.card - 1)) := by ring
      _ ≤ _ := hb

-- Degree sum of a union with an independent set.
lemma D_union (I Y : Finset V) (hdisj : Disjoint I Y) (hI : ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) :
    ∑ u ∈ I ∪ Y, ((I ∪ Y).filter (G.Adj u)).card =
      ∑ u ∈ Y, (Y.filter (G.Adj u)).card + 2 * ∑ u ∈ Y, (I.filter (G.Adj u)).card := by
  have hsplit : ∀ u, ((I ∪ Y).filter (G.Adj u)).card =
      (I.filter (G.Adj u)).card + (Y.filter (G.Adj u)).card := by
    intro u
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj)]
  simp_rw [hsplit]
  rw [Finset.sum_union hdisj, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hII : ∑ u ∈ I, (I.filter (G.Adj u)).card = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw; exact hI u hu w hw
  have hswap : ∑ u ∈ I, (Y.filter (G.Adj u)).card = ∑ u ∈ Y, (I.filter (G.Adj u)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    simp only [G.adj_comm]
  rw [hII, hswap]
  ring

lemma nbhd_indep (h : G.CliqueFree 3) (v : V) :
    ∀ u ∈ (univ : Finset V).filter (G.Adj v), ∀ w ∈ (univ : Finset V).filter (G.Adj v),
      ¬ G.Adj u w := by
  intro u hu w hw huw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
  exact h {v, u, w} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hu, hw, huw⟩)

lemma D_indep (S : Finset V) (hS : ∀ u ∈ S, ∀ w ∈ S, ¬ G.Adj u w) :
    ∑ u ∈ S, (S.filter (G.Adj u)).card = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw; exact hS u hu w hw

-- Keevash and Sudakov, Proposition 1.2: at most n²/12 edges gives a sparse half.
lemma sparse12 (hcf : G.CliqueFree 3) (h : 12 * G.edgeSet.ncard ≤ Fintype.card V ^ 2) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  set n := Fintype.card V with hn
  have finish : ∀ S : Finset V, S.card = n / 2 → 25 * ∑ u ∈ S, (S.filter (G.Adj u)).card ≤ n ^ 2 →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ n ∧ 50 * (G.induce V').edgeSet.ncard ≤ n ^ 2 := by
    intro S hS hD
    refine ⟨(S : Set V), by rw [Set.ncard_coe_finset, hS]; omega, ?_⟩
    have := two_mul_induce G S
    omega
  rcases isEmpty_or_nonempty V with hV | hV
  · refine finish ∅ ?_ (by simp)
    simp [n, Fintype.card_eq_zero]
  obtain ⟨v, -, hvmax⟩ := Finset.exists_max_image (univ : Finset V)
    (fun v => ((univ : Finset V).filter (G.Adj v)).card) Finset.univ_nonempty
  set N := (univ : Finset V).filter (G.Adj v) with hN
  have hNind := nbhd_indep G hcf v
  have hmax : ∑ u ∈ (univ : Finset V), ((univ : Finset V).filter (G.Adj u)).card ≤ n * N.card := by
    calc _ ≤ ∑ _u ∈ (univ : Finset V), N.card := Finset.sum_le_sum fun u hu => hvmax u hu
      _ = n * N.card := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hD2e := deg_sum_univ G
  rcases le_or_gt (n / 2) N.card with hk | hk
  · obtain ⟨S, hSN, hS⟩ := Finset.exists_subset_card_eq hk
    refine finish S hS ?_
    rw [D_indep G S fun u hu w hw => hNind u (hSN hu) w (hSN hw)]
    simp
  · set X := (univ : Finset V) \ N with hX
    have hNn : N.card ≤ n := by rw [hn, ← Finset.card_univ]; exact Finset.card_le_univ N
    have hXc : X.card = n - N.card := by
      rw [hX, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hdisj : Disjoint N X := Finset.disjoint_sdiff
    have hunion : N ∪ X = univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
    have hDU := D_union G N X hdisj hNind
    rw [hunion] at hDU
    obtain ⟨YA, -, hYA, hA⟩ := avg_two G X ∅ (n / 2) (by omega) (by omega)
    simp only [Finset.filter_empty, Finset.card_empty, Finset.sum_const_zero, mul_zero,
      zero_add] at hA
    obtain ⟨YB, hYBX, hYB, hB⟩ := avg_two G X N (n / 2 - N.card) (by omega) (by omega)
    have hdisjB : Disjoint N YB := Finset.disjoint_of_subset_right hYBX hdisj
    have hDB := D_union G N YB hdisjB hNind
    have hcardB : (N ∪ YB).card = n / 2 := by
      rw [Finset.card_union_of_disjoint hdisjB, hYB]; omega
    -- name the quantities
    generalize hDXd : ∑ u ∈ X, (X.filter (G.Adj u)).card = DX at hA hB hDU
    generalize haXd : ∑ u ∈ X, (N.filter (G.Adj u)).card = aX at hB hDU
    generalize hDAd : ∑ u ∈ YA, (YA.filter (G.Adj u)).card = DA at hA
    generalize hTd : 2 * ∑ u ∈ YB, (N.filter (G.Adj u)).card +
      ∑ u ∈ YB, (YB.filter (G.Adj u)).card = T at hB
    have hT : ∑ u ∈ N ∪ YB, ((N ∪ YB).filter (G.Adj u)).card = T := by rw [hDB, ← hTd]; ring
    generalize hs : N.card = s at hk hmax hXc hNn hYB hcardB hB
    generalize hk' : n / 2 = k at hk hA hB hYA hcardB hYB finish
    rw [hXc] at hA hB
    have hpar : n = 2 * k ∨ n = 2 * k + 1 := by omega
    -- cast to ℝ
    have hA' : (DA : ℝ) * (((n : ℝ) - s) * ((n : ℝ) - s - 1)) ≤ (k : ℝ) * ((k : ℝ) - 1) * DX := by
      have := (Nat.cast_le (α := ℝ)).mpr hA
      push_cast [Nat.cast_sub hNn, Nat.cast_sub (show 1 ≤ n - s by omega),
        Nat.cast_sub (show 1 ≤ k by omega)] at this
      linarith
    have hB' : (T : ℝ) * (((n : ℝ) - s) * ((n : ℝ) - s - 1)) ≤
        2 * ((k : ℝ) - s) * ((n : ℝ) - s - 1) * aX + ((k : ℝ) - s) * ((k : ℝ) - s - 1) * DX := by
      have := (Nat.cast_le (α := ℝ)).mpr hB
      push_cast [Nat.cast_sub hNn, Nat.cast_sub (show 1 ≤ n - s by omega),
        Nat.cast_sub (show s ≤ k by omega), Nat.cast_sub (show 1 ≤ k - s by omega)] at this
      linarith
    have hpar' : (n : ℝ) = 2 * k ∨ (n : ℝ) = 2 * k + 1 := by
      rcases hpar with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    have he' : 2 * (G.edgeSet.ncard : ℝ) = DX + 2 * aX := by
      have : 2 * G.edgeSet.ncard = DX + 2 * aX := by rw [← hD2e, hDU]
      exact_mod_cast this
    have hmax' : 2 * (G.edgeSet.ncard : ℝ) ≤ n * s := by
      have : 2 * G.edgeSet.ncard ≤ n * s := by rw [← hD2e]; exact hmax
      exact_mod_cast this
    have h12' : 12 * (G.edgeSet.ncard : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h
    have hsk : (s : ℝ) + 1 ≤ k := by exact_mod_cast (show s + 1 ≤ k by omega)
    rcases endgameR (n : ℝ) k s (G.edgeSet.ncard) DX aX DA T hpar' (by positivity) hsk
        (by positivity) (by positivity) (by positivity) (by positivity) he' hmax' h12' hA' hB'
      with hfin | hfin
    · refine finish YA hYA ?_
      rw [hDAd]; exact_mod_cast hfin
    · refine finish (N ∪ YB) hcardB ?_
      rw [hT]; exact_mod_cast hfin

theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R1.H2 := by
  intro h1 h2 V _ G hcf _ hhigh
  classical
  rcases le_or_gt (12 * G.edgeSet.ncard) (Fintype.card V ^ 2) with hs | hs
  · exact sparse12 G hcf hs
  · rcases le_or_gt (20 * G.edgeSet.ncard) (3 * Fintype.card V ^ 2) with hm | hm
    · exact h1 V G hcf hs hm
    · exact h2 V G hcf hm hhigh

end OMA.R_Erdos128_erdos_128_R1_H2_R1
