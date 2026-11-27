import FormalConjectures.ErdosProblems.«887»

-- Problem: Erdős Problem 887 — rosenfeld infinite
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/887.lean:58 (declaration Erdos887.erdos_887.variants.rosenfeld_infinite)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset Real

namespace OMA

def f (k : ℕ) : ℕ := (k+63)*(k+65)*(k+62)*(k+66)*(k+60)*(k+68)*(k+57)*(k+71)

lemma Qy (y : ℝ) (hy : 4096 ≤ y) :
    (y^2-35*y-57)^2 ≤ (y-1)*(y-4)*(y-16)*(y-49) ∧
    (y-20)^4 ≤ (y-1)*(y-4)*(y-16)*(y-49) := by
  have h0 : (0:ℝ) ≤ y - 4096 := by linarith
  constructor
  · nlinarith [mul_nonneg h0 h0, mul_nonneg h0 (by linarith : (0:ℝ) ≤ y)]
  · nlinarith [mul_nonneg h0 h0, mul_nonneg h0 (by linarith : (0:ℝ) ≤ y),
      mul_nonneg (mul_nonneg h0 h0) (by linarith : (0:ℝ) ≤ y)]

lemma Qbounds (x : ℝ) (hx : 64 ≤ x) :
    ((x^2)^2-35*x^2-57)^2 ≤ (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49) ∧
    (x^2-20)^4 ≤ (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49) := by
  have hy : (4096:ℝ) ≤ x^2 := by nlinarith
  exact Qy (x^2) hy

lemma dA_bounds (x : ℝ) (hx : 64 ≤ x) :
    (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49) < ((x^2-1)*(x^2-4))^2 ∧
    (x^2-1)*(x^2-4) < ((x^2)^2-35*x^2-57) + 40*(x^2-20) := by
  have hy : (4096:ℝ) ≤ x^2 := by nlinarith
  have h1 : (0:ℝ) < x^2 - 13 := by linarith
  have h2 : (0:ℝ) < 60*x^2 - 780 := by linarith
  constructor
  · have e : ((x^2-1)*(x^2-4))^2 - (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49)
        = ((x^2-1)*(x^2-4)) * (60*x^2-780) := by ring
    have : 0 < ((x^2-1)*(x^2-4)) * (60*x^2-780) := mul_pos (by nlinarith) h2
    linarith
  · nlinarith

lemma dB_bounds (x : ℝ) (hx : 64 ≤ x) :
    (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49) < ((x^2-1)*(x^2-16))^2 ∧
    (x^2-1)*(x^2-16) < ((x^2)^2-35*x^2-57) + 40*(x^2-20) := by
  have hy : (4096:ℝ) ≤ x^2 := by nlinarith
  constructor
  · have e : ((x^2-1)*(x^2-16))^2 - (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49)
        = ((x^2-1)*(x^2-16)) * (36*x^2-180) := by ring
    have : 0 < ((x^2-1)*(x^2-16)) * (36*x^2-180) := mul_pos (by nlinarith) (by linarith)
    linarith
  · nlinarith

lemma dC_bounds (x : ℝ) (hx : 64 ≤ x) :
    (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49) < ((x^2-4)*(x^2-16))^2 ∧
    (x^2-4)*(x^2-16) < ((x^2)^2-35*x^2-57) + 40*(x^2-20) := by
  have hy : (4096:ℝ) ≤ x^2 := by nlinarith
  constructor
  · have e : ((x^2-4)*(x^2-16))^2 - (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49)
        = ((x^2-4)*(x^2-16)) * (30*x^2+15) := by ring
    have : 0 < ((x^2-4)*(x^2-16)) * (30*x^2+15) := mul_pos (by nlinarith) (by linarith)
    linarith
  · nlinarith

lemma dD_bounds (x : ℝ) (hx : 64 ≤ x) :
    (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49) < ((x^2)^2-35*x^2+90*x-56)^2 ∧
    (x^2)^2-35*x^2+90*x-56 < ((x^2)^2-35*x^2-57) + 40*(x^2-20) := by
  have hy : (4096:ℝ) ≤ x^2 := by nlinarith
  constructor
  · -- dD = L + c with L = y^2-35y-57, c = 90x+1; Q = L^2 + R, R = 2y^2-8170y-113
    have hL2 : (x^2)^2 / 2 ≤ (x^2)^2-35*x^2-57 := by nlinarith
    have hc : (0:ℝ) ≤ 90*x+1 := by linarith
    have hLc : (x^2)^2 / 2 * (90*x+1) ≤ ((x^2)^2-35*x^2-57) * (90*x+1) :=
      mul_le_mul_of_nonneg_right hL2 hc
    have hy2 : 0 ≤ (x^2)^2 := by positivity
    have hR : (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49)
        = ((x^2)^2-35*x^2-57)^2 + (2*(x^2)^2-8170*x^2-113) := by ring
    have hRle : 2*(x^2)^2-8170*x^2-113 ≤ 2*(x^2)^2 := by nlinarith
    have hcpos : (0:ℝ) < (90*x+1)^2 := by positivity
    have hkey : (x^2)^2 * 2 ≤ (x^2)^2 * (90*x+1) := by nlinarith
    have e : ((x^2)^2-35*x^2+90*x-56)^2
        = ((x^2)^2-35*x^2-57)^2 + 2*((x^2)^2-35*x^2-57)*(90*x+1) + (90*x+1)^2 := by ring
    rw [hR, e]
    nlinarith
  · nlinarith

lemma sqrt_window (N d L M : ℝ) (hN : 0 ≤ N) (hd : N < d^2) (hd0 : 0 ≤ d)
    (hL : L^2 ≤ N) (hLd : d < L + 40*M) (hM4 : M^4 ≤ N) :
    √N < d ∧ d < √N + 40 * N^((1:ℝ)/4) := by
  have hpos : 0 < d := by
    rcases lt_or_eq_of_le hd0 with h | h
    · exact h
    · rw [← h] at hd; norm_num at hd; linarith
  refine ⟨?_, ?_⟩
  · rw [Real.sqrt_lt' hpos]; exact hd
  · have h1 : L ≤ √N := le_trans (le_abs_self L) (Real.abs_le_sqrt hL)
    have ht0 : 0 ≤ N^((1:ℝ)/4) := Real.rpow_nonneg hN _
    have ht4 : (N^((1:ℝ)/4))^4 = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN]; norm_num
    have h2 : M ≤ N^((1:ℝ)/4) := by
      by_contra h
      push_neg at h
      have : (N^((1:ℝ)/4))^4 < M^4 := pow_lt_pow_left₀ h ht0 (by norm_num)
      linarith
    linarith

lemma mem_win (N d : ℕ) (L M : ℝ) (hdvd : d ∣ N) (h1 : (N:ℝ) < (d:ℝ)^2)
    (hL : L^2 ≤ (N:ℝ)) (hLd : (d:ℝ) < L + 40*M) (hM4 : M^4 ≤ (N:ℝ)) :
    d ∈ Finset.filter (fun e => e ∣ N) (Finset.Ioo ⌊√(N:ℝ)⌋₊ ⌈√(N:ℝ) + 40 * (N:ℝ)^((1:ℝ)/4)⌉₊) := by
  obtain ⟨a, b⟩ := sqrt_window (N:ℝ) (d:ℝ) L M (Nat.cast_nonneg N) h1 (Nat.cast_nonneg d) hL hLd hM4
  exact Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨(Nat.floor_lt (Real.sqrt_nonneg _)).2 a, Nat.lt_ceil.2 b⟩, hdvd⟩

lemma card_four (a b c e : ℕ) (h1 : a < b) (h2 : b < c) (h3 : c < e) :
    ({a, b, c, e} : Finset ℕ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.card_pair (by omega)]

lemma f_ge (B : ℕ) : B + 63 ≤ f B := by
  have hpos : 0 < (B+65)*(B+62)*(B+66)*(B+60)*(B+68)*(B+57)*(B+71) := by positivity
  have e : f B = (B+63) * ((B+65)*(B+62)*(B+66)*(B+60)*(B+68)*(B+57)*(B+71)) := by
    unfold f; ring
  rw [e]; exact Nat.le_mul_of_pos_right _ hpos

lemma key (k : ℕ) : 4 ≤ #{ d ∈ Ioo ⌊√((f k : ℕ) : ℝ)⌋₊ ⌈√((f k : ℕ) : ℝ) + 40 * ((f k : ℕ) : ℝ)^((1 : ℝ) / 4)⌉₊ | d ∣ f k } := by
  obtain ⟨x, hxk⟩ : ∃ x : ℝ, x = (k:ℝ) + 64 := ⟨_, rfl⟩
  have hx : (64:ℝ) ≤ x := by
    rw [hxk]; have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith
  have hy : (4096:ℝ) ≤ x^2 := by nlinarith
  have hN : ((f k : ℕ) : ℝ) = (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49) := by
    unfold f; push_cast; rw [hxk]; ring
  obtain ⟨hL, hM4⟩ := Qbounds x hx
  have hdA : (((k+63)*(k+65)*(k+62)*(k+66) : ℕ) : ℝ) = (x^2-1)*(x^2-4) := by
    push_cast; rw [hxk]; ring
  have hdB : (((k+63)*(k+65)*(k+60)*(k+68) : ℕ) : ℝ) = (x^2-1)*(x^2-16) := by
    push_cast; rw [hxk]; ring
  have hdC : (((k+62)*(k+66)*(k+60)*(k+68) : ℕ) : ℝ) = (x^2-4)*(x^2-16) := by
    push_cast; rw [hxk]; ring
  have hdD : (((k+63)*(k+62)*(k+60)*(k+71) : ℕ) : ℝ) = (x^2)^2-35*x^2+90*x-56 := by
    push_cast; rw [hxk]; ring
  have vA : (k+63)*(k+65)*(k+62)*(k+66) ∣ f k :=
    ⟨(k+60)*(k+68)*(k+57)*(k+71), by unfold f; ring⟩
  have vB : (k+63)*(k+65)*(k+60)*(k+68) ∣ f k :=
    ⟨(k+62)*(k+66)*(k+57)*(k+71), by unfold f; ring⟩
  have vC : (k+62)*(k+66)*(k+60)*(k+68) ∣ f k :=
    ⟨(k+63)*(k+65)*(k+57)*(k+71), by unfold f; ring⟩
  have vD : (k+63)*(k+62)*(k+60)*(k+71) ∣ f k :=
    ⟨(k+65)*(k+66)*(k+68)*(k+57), by unfold f; ring⟩
  obtain ⟨hA1, hA2⟩ := dA_bounds x hx
  obtain ⟨hB1, hB2⟩ := dB_bounds x hx
  obtain ⟨hC1, hC2⟩ := dC_bounds x hx
  obtain ⟨hD1, hD2⟩ := dD_bounds x hx
  have mA := mem_win (f k) _ ((x^2)^2-35*x^2-57) (x^2-20) vA (by rw [hN, hdA]; exact hA1)
    (by rw [hN]; exact hL) (by rw [hdA]; exact hA2) (by rw [hN]; exact hM4)
  have mB := mem_win (f k) _ ((x^2)^2-35*x^2-57) (x^2-20) vB (by rw [hN, hdB]; exact hB1)
    (by rw [hN]; exact hL) (by rw [hdB]; exact hB2) (by rw [hN]; exact hM4)
  have mC := mem_win (f k) _ ((x^2)^2-35*x^2-57) (x^2-20) vC (by rw [hN, hdC]; exact hC1)
    (by rw [hN]; exact hL) (by rw [hdC]; exact hC2) (by rw [hN]; exact hM4)
  have mD := mem_win (f k) _ ((x^2)^2-35*x^2-57) (x^2-20) vD (by rw [hN, hdD]; exact hD1)
    (by rw [hN]; exact hL) (by rw [hdD]; exact hD2) (by rw [hN]; exact hM4)
  have r1R : (x^2)^2-35*x^2+90*x-56 < (x^2-4)*(x^2-16) := by nlinarith
  have r2R : (x^2-4)*(x^2-16) < (x^2-1)*(x^2-16) := by nlinarith
  have r3R : (x^2-1)*(x^2-16) < (x^2-1)*(x^2-4) := by nlinarith
  have r1 : (k+63)*(k+62)*(k+60)*(k+71) < (k+62)*(k+66)*(k+60)*(k+68) := by
    have : (((k+63)*(k+62)*(k+60)*(k+71) : ℕ) : ℝ) < (((k+62)*(k+66)*(k+60)*(k+68) : ℕ) : ℝ) := by
      rw [hdD, hdC]; exact r1R
    exact_mod_cast this
  have r2 : (k+62)*(k+66)*(k+60)*(k+68) < (k+63)*(k+65)*(k+60)*(k+68) := by
    have : (((k+62)*(k+66)*(k+60)*(k+68) : ℕ) : ℝ) < (((k+63)*(k+65)*(k+60)*(k+68) : ℕ) : ℝ) := by
      rw [hdC, hdB]; exact r2R
    exact_mod_cast this
  have r3 : (k+63)*(k+65)*(k+60)*(k+68) < (k+63)*(k+65)*(k+62)*(k+66) := by
    have : (((k+63)*(k+65)*(k+60)*(k+68) : ℕ) : ℝ) < (((k+63)*(k+65)*(k+62)*(k+66) : ℕ) : ℝ) := by
      rw [hdB, hdA]; exact r3R
    exact_mod_cast this
  refine le_trans (le_of_eq (card_four _ _ _ _ r1 r2 r3).symm) (Finset.card_le_card ?_)
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact mD
  · exact mC
  · exact mB
  · exact mA

end OMA


theorem OMA.solution : type_of% @Erdos887.erdos_887.variants.rosenfeld_infinite := by
  refine ⟨40, by norm_num, ?_⟩
  rw [Set.infinite_coe_iff]
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hmem : OMA.f B ∈ {n : ℕ | 4 ≤ #{ d ∈ Ioo ⌊√(n:ℝ)⌋₊ ⌈√(n:ℝ) + 40 * (n:ℝ)^((1 : ℝ) / 4)⌉₊ | d ∣ n }} :=
    OMA.key B
  have h1 := hB hmem
  have h2 := OMA.f_ge B
  omega
