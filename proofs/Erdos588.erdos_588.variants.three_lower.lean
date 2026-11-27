import FormalConjectures.ErdosProblems.«588»

/-!
# Erdős Problem 588 — three lower

We prove `Erdos588.erdos_588.variants.three_lower`, i.e., for every `ε > 0` and all sufficiently
large `n`, `numLinesWithPointsMax 3 n ≥ (1 / 6 - ε) * n ^ 2`.

Using the rational cubic curve `P(t) = (t / (t^2 + 1), t^3 / (t^2 + 1))`, three distinct points
`P(t₁), P(t₂), P(t₃)` are collinear if and only if `t₁ + t₂ + t₃ = t₁ * t₂ * t₃`, which automatically
forbids any four collinear points on the curve. Choosing `t_k = tan(k * π / m)` for odd
`m ∈ {n, n - 1}` (plus one extra point on the curve when `n` is even) yields at least
`(m^2 - 3 * m) / 6` 3-point lines from zero-sum triples `m ∣ i + j + k`, establishing
`n ^ 2 / 6 - n ≤ numLinesWithPointsMax 3 n` for all `n ≥ 4`.
-/

-- Problem: Erdős Problem 588 — three lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/588.lean:100 (declaration Erdos588.erdos_588.variants.three_lower)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos588Proof

open Erdos588 EuclideanGeometry Filter Asymptotics
open scoped EuclideanGeometry

private noncomputable def mkPt (x y : ℝ) : ℝ² :=
  WithLp.toLp 2 ![x, y]

private lemma mkPt_zero (x y : ℝ) : mkPt x y 0 = x := rfl
private lemma mkPt_one (x y : ℝ) : mkPt x y 1 = y := rfl

private def det3 (p q r : ℝ²) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

private lemma mem_affineSpan_pair_iff {a b x : ℝ²} (hab : a ≠ b) :
    x ∈ affineSpan ℝ ({a, b} : Set ℝ²) ↔ ∃ t : ℝ, x = (1 - t) • a + t • b := by
  constructor
  · intro hx
    have hcol : Collinear ℝ ({x, a, b} : Set ℝ²) :=
      (collinear_insert_iff_of_mem_affineSpan hx).mpr (collinear_pair ℝ a b)
    rcases (collinear_iff_of_mem (show a ∈ ({x, a, b} : Set ℝ²) by simp)).mp hcol with ⟨v, hv⟩
    rcases hv x (by simp) with ⟨rx, hrx⟩
    rcases hv b (by simp) with ⟨rb, hrb⟩
    have hrb_ne : rb ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_vadd] at hrb
      exact hab hrb.symm
    refine ⟨rx / rb, ?_⟩
    ext k
    have hx' := congr_arg (fun p : ℝ² => p k) hrx
    have hb' := congr_arg (fun p : ℝ² => p k) hrb
    simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx' hb' ⊢
    field_simp
    linear_combination rb * hx' - rx * hb'
  · rintro ⟨t, rfl⟩
    have h := AffineMap.lineMap_mem_affineSpan_pair t a b
    rwa [AffineMap.lineMap_apply_module] at h

private lemma affineSpan_pair_eq_of_mem {a b p q : ℝ²} (hab : a ≠ b) (hpq : p ≠ q)
    (hp : p ∈ affineSpan ℝ ({a, b} : Set ℝ²)) (hq : q ∈ affineSpan ℝ ({a, b} : Set ℝ²)) :
    affineSpan ℝ ({p, q} : Set ℝ²) = affineSpan ℝ ({a, b} : Set ℝ²) := by
  apply le_antisymm
  · rw [affineSpan_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq
  · rcases (mem_affineSpan_pair_iff hab).mp hp with ⟨t1, rfl⟩
    rcases (mem_affineSpan_pair_iff hab).mp hq with ⟨t2, rfl⟩
    have ht12 : t2 - t1 ≠ 0 := by
      intro h0
      have hEq : t1 = t2 := by linarith
      exact hpq (by rw [hEq])
    have ha_mem : a ∈ affineSpan ℝ ({(1 - t1) • a + t1 • b, (1 - t2) • a + t2 • b} : Set ℝ²) := by
      rw [mem_affineSpan_pair_iff hpq]
      refine ⟨-t1 / (t2 - t1), ?_⟩
      ext k
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
    have hb_mem : b ∈ affineSpan ℝ ({(1 - t1) • a + t1 • b, (1 - t2) • a + t2 • b} : Set ℝ²) := by
      rw [mem_affineSpan_pair_iff hpq]
      refine ⟨(1 - t1) / (t2 - t1), ?_⟩
      ext k
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [affineSpan_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ha_mem
    · exact hb_mem

private lemma mem_affineSpan_pair_iff_det3 {a b c : ℝ²} (hab : a ≠ b) :
    c ∈ affineSpan ℝ ({a, b} : Set ℝ²) ↔ det3 a b c = 0 := by
  rw [mem_affineSpan_pair_iff hab]
  constructor
  · rintro ⟨t, rfl⟩
    simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · intro hdet
    have hne : 0 < (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 := by
      by_contra hle
      have h0 : (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 = 0 := le_antisymm (not_lt.mp hle) (by positivity)
      have h00 : b 0 = a 0 := by nlinarith
      have h11 : b 1 = a 1 := by nlinarith
      apply hab
      ext k; fin_cases k <;> simp [h00, h11]
    set t : ℝ := ((c 0 - a 0) * (b 0 - a 0) + (c 1 - a 1) * (b 1 - a 1)) /
      ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2)
    refine ⟨t, ?_⟩
    have ht_mul : t * ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2) =
        (c 0 - a 0) * (b 0 - a 0) + (c 1 - a 1) * (b 1 - a 1) :=
      div_mul_cancel₀ _ hne.ne'
    ext k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hmul : ((1 - t) * a 0 + t * b 0) * ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2) =
          c 0 * ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2) := by
        dsimp only [det3] at hdet
        linear_combination (b 0 - a 0) * ht_mul + (b 1 - a 1) * hdet
      exact (mul_right_cancel₀ hne.ne' hmul).symm
    · simp only [Fin.mk_one, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hmul : ((1 - t) * a 1 + t * b 1) * ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2) =
          c 1 * ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2) := by
        dsimp only [det3] at hdet
        linear_combination (b 1 - a 1) * ht_mul - (b 0 - a 0) * hdet
      exact (mul_right_cancel₀ hne.ne' hmul).symm

private lemma collinear_triple_iff_det3 {a b c : ℝ²} (hab : a ≠ b) :
    Collinear ℝ ({a, b, c} : Set ℝ²) ↔ det3 a b c = 0 := by
  rw [← mem_affineSpan_pair_iff_det3 hab]
  constructor
  · intro hcol
    rcases (collinear_iff_of_mem (show a ∈ ({a, b, c} : Set ℝ²) by simp)).mp hcol with ⟨v, hv⟩
    rcases hv b (by simp) with ⟨rb, hrb⟩
    rcases hv c (by simp) with ⟨rc, hrc⟩
    have hrb_ne : rb ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_vadd] at hrb
      exact hab hrb.symm
    rw [mem_affineSpan_pair_iff hab]
    refine ⟨rc / rb, ?_⟩
    ext k
    have hb' := congr_arg (fun p : ℝ² => p k) hrb
    have hc' := congr_arg (fun p : ℝ² => p k) hrc
    simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hb' hc' ⊢
    field_simp
    linear_combination rb * hc' - rc * hb'
  · intro hc
    have h := (collinear_insert_iff_of_mem_affineSpan hc).mpr (collinear_pair ℝ a b)
    have hset : insert c ({a, b} : Set ℝ²) = {a, b, c} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor <;> (rintro (rfl | rfl | rfl) <;> simp)
    rwa [hset] at h

private lemma linesWithPointsFor_three_upper {S : Set ℝ²} (hS : S.Finite) :
    (linesWithPointsFor 3 S).Finite ∧ (linesWithPointsFor 3 S).ncard * 6 ≤ S.ncard * (S.ncard - 1) := by
  classical
  let Sf : Finset ℝ² := hS.toFinset
  have hSf_coe : (Sf : Set ℝ²) = S := hS.coe_toFinset
  have hSf_card : Sf.card = S.ncard := by
    rw [← hSf_coe, Set.ncard_coe_finset]
  let detLines : Finset (AffineSubspace ℝ ℝ²) :=
    Sf.offDiag.image (fun pq => affineSpan ℝ ({pq.1, pq.2} : Set ℝ²))
  have hsub_det : linesWithPointsFor 3 S ⊆ (detLines : Set (AffineSubspace ℝ ℝ²)) := by
    rintro L ⟨⟨p, hp, q, hq, hpq, rfl⟩, _⟩
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨(p, q), Finset.mem_offDiag.mpr ⟨?_, ?_, hpq⟩, rfl⟩
    · rwa [← Finset.mem_coe, hSf_coe]
    · rwa [← Finset.mem_coe, hSf_coe]
  have hL_fin : (linesWithPointsFor 3 S).Finite := detLines.finite_toSet.subset hsub_det
  refine ⟨hL_fin, ?_⟩
  let Lf : Finset (AffineSubspace ℝ ℝ²) := hL_fin.toFinset
  have hLf_card : Lf.card = (linesWithPointsFor 3 S).ncard := by
    rw [← Set.ncard_coe_finset, hL_fin.coe_toFinset]
  let pairs : AffineSubspace ℝ ℝ² → Finset (ℝ² × ℝ²) :=
    fun L => (Sf.filter (fun p => p ∈ L)).offDiag
  have hpairs_card : ∀ L ∈ Lf, (pairs L).card = 6 := by
    intro L hL
    have hL_mem : L ∈ linesWithPointsFor 3 S := hL_fin.mem_toFinset.mp hL
    have hncard : ((L : Set ℝ²) ∩ S).ncard = 3 := hL_mem.2
    have hfilt_coe : ((Sf.filter (fun p => p ∈ L) : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ S := by
      ext p
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff, Sf, Set.Finite.mem_toFinset]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have hcard3 : (Sf.filter (fun p => p ∈ L)).card = 3 := by
      rw [← Set.ncard_coe_finset, hfilt_coe, hncard]
    simp [pairs, Finset.offDiag_card, hcard3]
  have hpairs_disj : (Lf : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint pairs := by
    intro L1 hL1 L2 hL2 hne
    refine Finset.disjoint_left.mpr ?_
    intro pq hpq1 hpq2
    rcases Finset.mem_offDiag.mp hpq1 with ⟨hp1, hq1, hpq_ne⟩
    rcases Finset.mem_offDiag.mp hpq2 with ⟨hp2, hq2, _⟩
    have hpL1 : pq.1 ∈ L1 := (Finset.mem_filter.mp hp1).2
    have hqL1 : pq.2 ∈ L1 := (Finset.mem_filter.mp hq1).2
    have hpL2 : pq.1 ∈ L2 := (Finset.mem_filter.mp hp2).2
    have hqL2 : pq.2 ∈ L2 := (Finset.mem_filter.mp hq2).2
    rcases (hL_fin.mem_toFinset.mp hL1).1 with ⟨a1, _, b1, _, hab1, rfl⟩
    rcases (hL_fin.mem_toFinset.mp hL2).1 with ⟨a2, _, b2, _, hab2, rfl⟩
    have h1 := affineSpan_pair_eq_of_mem hab1 hpq_ne hpL1 hqL1
    have h2 := affineSpan_pair_eq_of_mem hab2 hpq_ne hpL2 hqL2
    exact hne (h1.symm.trans h2)
  have hpairs_sub : Lf.biUnion pairs ⊆ Sf.offDiag := by
    intro pq hpq
    rcases Finset.mem_biUnion.mp hpq with ⟨L, _, hmem⟩
    rcases Finset.mem_offDiag.mp hmem with ⟨hp, hq, hne⟩
    exact Finset.mem_offDiag.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hq).1, hne⟩
  have hcount : Lf.card * 6 ≤ Sf.offDiag.card := by
    calc
      Lf.card * 6 = ∑ _L ∈ Lf, 6 := by simp
      _ = ∑ L ∈ Lf, (pairs L).card := (Finset.sum_congr rfl hpairs_card).symm
      _ = (Lf.biUnion pairs).card := (Finset.card_biUnion hpairs_disj).symm
      _ ≤ Sf.offDiag.card := Finset.card_le_card hpairs_sub
  rw [Finset.offDiag_card, hSf_card, hLf_card] at hcount
  have hmul_sub : S.ncard * S.ncard - S.ncard = S.ncard * (S.ncard - 1) := by
    rcases Nat.eq_zero_or_pos S.ncard with h0 | hpos
    · simp [h0]
    · rw [Nat.mul_sub_one]
  rwa [hmul_sub] at hcount

private lemma numLinesWithPointsMax_three_bddAbove (n : ℕ) :
    BddAbove {((linesWithPointsFor 3 S).ncard) | (S : Set ℝ²)
      (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor 4 S)} := by
  refine ⟨n * (n - 1) / 6, ?_⟩
  rintro _ ⟨S, rfl, hfin, -, rfl⟩
  exact Nat.le_div_iff_mul_le (by omega) |>.mpr (linesWithPointsFor_three_upper hfin).2

private lemma numLinesWithPointsMax_three_upper (n : ℕ) :
    numLinesWithPointsMax 3 n * 6 ≤ n * (n - 1) := by
  rw [numLinesWithPointsMax]
  set T : Set ℕ := {((linesWithPointsFor 3 S).ncard) | (S : Set ℝ²)
    (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor 4 S)}
  have hle : sSup T ≤ n * (n - 1) / 6 := by
    by_cases hne : T.Nonempty
    · refine csSup_le hne ?_
      rintro _ ⟨S, rfl, hfin, -, rfl⟩
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (linesWithPointsFor_three_upper hfin).2
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
      exact Nat.zero_le _
  exact le_trans (Nat.mul_le_mul_right 6 hle) (Nat.div_mul_le_self _ 6)

private noncomputable def curvePt (t : ℝ) : ℝ² :=
  mkPt (t / (t ^ 2 + 1)) (t ^ 3 / (t ^ 2 + 1))

private lemma curvePt_injective : Function.Injective curvePt := by
  intro s t hst
  have h0 := congr_arg (fun p : ℝ² => p 0) hst
  have h1 := congr_arg (fun p : ℝ² => p 1) hst
  simp only [curvePt, mkPt_zero, mkPt_one] at h0 h1
  have hs_pos : 0 < s ^ 2 + 1 := by positivity
  have ht_pos : 0 < t ^ 2 + 1 := by positivity
  by_cases hs : s = 0
  · subst hs
    simp only [zero_div] at h0
    have : t = 0 := by
      rcases div_eq_zero_iff.mp h0.symm with h | h
      · exact h
      · linarith
    exact this.symm
  · have h0_ne : s / (s ^ 2 + 1) ≠ 0 := div_ne_zero hs hs_pos.ne'
    have hsq : s ^ 2 = t ^ 2 := by
      have h1' : s ^ 2 * (s / (s ^ 2 + 1)) = t ^ 2 * (t / (t ^ 2 + 1)) := by
        field_simp at h1 ⊢
        linarith
      rw [h0] at h1'
      exact mul_right_cancel₀ (h0 ▸ h0_ne) h1'
    rw [hsq] at h0
    exact (div_left_inj' ht_pos.ne').mp h0

private lemma det3_curvePt (t1 t2 t3 : ℝ) :
    (t1 ^ 2 + 1) * (t2 ^ 2 + 1) * (t3 ^ 2 + 1) * det3 (curvePt t1) (curvePt t2) (curvePt t3) =
      (t2 - t1) * (t3 - t1) * (t3 - t2) * (t1 + t2 + t3 - t1 * t2 * t3) := by
  simp only [det3, curvePt, mkPt_zero, mkPt_one]
  have h1 : t1 ^ 2 + 1 ≠ 0 := by positivity
  have h2 : t2 ^ 2 + 1 ≠ 0 := by positivity
  have h3 : t3 ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

private lemma collinear_curvePt_iff {t1 t2 t3 : ℝ} (h12 : t1 ≠ t2) (h13 : t1 ≠ t3) (h23 : t2 ≠ t3) :
    Collinear ℝ ({curvePt t1, curvePt t2, curvePt t3} : Set ℝ²) ↔ t1 + t2 + t3 = t1 * t2 * t3 := by
  have hp12 : curvePt t1 ≠ curvePt t2 := fun h => h12 (curvePt_injective h)
  rw [collinear_triple_iff_det3 hp12]
  have hpos : (t1 ^ 2 + 1) * (t2 ^ 2 + 1) * (t3 ^ 2 + 1) ≠ 0 := by positivity
  have hdiff : (t2 - t1) * (t3 - t1) * (t3 - t2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h12.symm) (sub_ne_zero.mpr h13.symm))
      (sub_ne_zero.mpr h23.symm)
  have hid := det3_curvePt t1 t2 t3
  constructor
  · intro hdet
    rw [hdet, mul_zero] at hid
    have := (mul_eq_zero.mp hid.symm).resolve_left hdiff
    linarith
  · intro hsum
    have hzero : t1 + t2 + t3 - t1 * t2 * t3 = 0 := by linarith
    rw [hzero, mul_zero] at hid
    exact (mul_eq_zero.mp hid).resolve_left hpos

private lemma nonCollinearFor_four_curvePt {S : Set ℝ²} (hS : S ⊆ Set.range curvePt) :
    NonCollinearFor 4 S := by
  intro A hAS hAfin hAcard hcol
  classical
  have hAf_card : hAfin.toFinset.card = 4 := by
    rw [← Set.ncard_coe_finset, hAfin.coe_toFinset, hAcard]
  rcases Finset.card_eq_succ.mp hAf_card with ⟨p1, A1, hp1, hA_eq, h1⟩
  rcases Finset.card_eq_succ.mp h1 with ⟨p2, A2, hp2, rfl, h2⟩
  rcases Finset.card_eq_succ.mp h2 with ⟨p3, A3, hp3, rfl, h3⟩
  rcases Finset.card_eq_one.mp h3 with ⟨p4, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp1 hp2 hp3
  have hmem : ∀ p ∈ ({p1, p2, p3, p4} : Set ℝ²), p ∈ A := by
    intro p hp
    rw [← hAfin.coe_toFinset, ← hA_eq]
    simpa using hp
  rcases hS (hAS (hmem p1 (by simp))) with ⟨t1, rfl⟩
  rcases hS (hAS (hmem p2 (by simp))) with ⟨t2, rfl⟩
  rcases hS (hAS (hmem p3 (by simp))) with ⟨t3, rfl⟩
  rcases hS (hAS (hmem p4 (by simp))) with ⟨t4, rfl⟩
  have ht12 : t1 ≠ t2 := fun h => hp1.1 (by rw [h])
  have ht13 : t1 ≠ t3 := fun h => hp1.2.1 (by rw [h])
  have ht14 : t1 ≠ t4 := fun h => hp1.2.2 (by rw [h])
  have ht23 : t2 ≠ t3 := fun h => hp2.1 (by rw [h])
  have ht24 : t2 ≠ t4 := fun h => hp2.2 (by rw [h])
  have ht34 : t3 ≠ t4 := fun h => hp3 (by rw [h])
  have hc123 : t1 + t2 + t3 = t1 * t2 * t3 :=
    (collinear_curvePt_iff ht12 ht13 ht23).mp (hcol.subset fun x hx =>
      hmem x (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
  have hc124 : t1 + t2 + t4 = t1 * t2 * t4 :=
    (collinear_curvePt_iff ht12 ht14 ht24).mp (hcol.subset fun x hx =>
      hmem x (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
  have hc134 : t1 + t3 + t4 = t1 * t3 * t4 :=
    (collinear_curvePt_iff ht13 ht14 ht34).mp (hcol.subset fun x hx =>
      hmem x (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
  have h12 : t1 * t2 = 1 := by
    have : (t3 - t4) * (1 - t1 * t2) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht34)
    linarith
  have h13 : t1 * t3 = 1 := by
    have : (t2 - t4) * (1 - t1 * t3) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht24)
    linarith
  have ht1_ne : t1 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h12; norm_num at h12
  exact ht23 (mul_left_cancel₀ ht1_ne (h12.trans h13.symm))

private lemma cos_nat_mul_pi_div_odd_ne_zero {m : ℕ} (hm : Odd m) (k : ℕ) :
    Real.cos ((k : ℝ) * Real.pi / (m : ℝ)) ≠ 0 := by
  rcases hm with ⟨r, rfl⟩
  intro h0
  rcases Real.cos_eq_zero_iff.mp h0 with ⟨z, hz⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hm_ne : (2 * r + 1 : ℝ) ≠ 0 := by positivity
  have hz' : (k : ℝ) * Real.pi / (2 * (r : ℝ) + 1) = (2 * (z : ℝ) + 1) * Real.pi / 2 := by
    simpa using hz
  field_simp at hz'
  have heq_z : (k : ℤ) * 2 = (2 * (r : ℤ) + 1) * (2 * z + 1) := by
    exact_mod_cast hz'
  have hodd : (2 * (r : ℤ) + 1) * (2 * z + 1) = 2 * (2 * (r : ℤ) * z + (r : ℤ) + z) + 1 := by
    ring
  omega

private lemma tan_nat_mul_pi_div_odd_inj {m : ℕ} (hm : Odd m) :
    Function.Injective (fun k : Fin m => Real.tan ((k.val : ℝ) * Real.pi / (m : ℝ))) := by
  intro i j hij
  by_contra hne
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    rcases hm with ⟨r, rfl⟩; positivity
  have haux : ∀ {a b : Fin m}, a.val < b.val →
      Real.tan ((a.val : ℝ) * Real.pi / (m : ℝ)) ≠
        Real.tan ((b.val : ℝ) * Real.pi / (m : ℝ)) := by
    intro a b hab heq
    have hca : Real.cos ((a.val : ℝ) * Real.pi / (m : ℝ)) ≠ 0 :=
      cos_nat_mul_pi_div_odd_ne_zero hm a.val
    have hcb : Real.cos ((b.val : ℝ) * Real.pi / (m : ℝ)) ≠ 0 :=
      cos_nat_mul_pi_div_odd_ne_zero hm b.val
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos] at heq
    have hsin_sub : Real.sin (((b.val : ℝ) - (a.val : ℝ)) * Real.pi / (m : ℝ)) = 0 := by
      have harg : ((b.val : ℝ) - (a.val : ℝ)) * Real.pi / (m : ℝ) =
          (b.val : ℝ) * Real.pi / (m : ℝ) - (a.val : ℝ) * Real.pi / (m : ℝ) := by ring
      rw [harg, Real.sin_sub]
      have hmul : Real.sin ((a.val : ℝ) * Real.pi / (m : ℝ)) *
          Real.cos ((b.val : ℝ) * Real.pi / (m : ℝ)) =
          Real.sin ((b.val : ℝ) * Real.pi / (m : ℝ)) *
          Real.cos ((a.val : ℝ) * Real.pi / (m : ℝ)) := (div_eq_div_iff hca hcb).mp heq
      linarith
    have hpos : 0 < ((b.val : ℝ) - (a.val : ℝ)) * Real.pi / (m : ℝ) := by
      have hba : (0 : ℝ) < (b.val : ℝ) - (a.val : ℝ) := by
        have : (a.val : ℝ) < (b.val : ℝ) := Nat.cast_lt.mpr hab
        linarith
      exact div_pos (mul_pos hba Real.pi_pos) hm_pos
    have hlt_pi : ((b.val : ℝ) - (a.val : ℝ)) * Real.pi / (m : ℝ) < Real.pi := by
      rw [div_lt_iff₀ hm_pos]
      have hbm : (b.val : ℝ) < (m : ℝ) := Nat.cast_lt.mpr b.isLt
      have ha0 : (0 : ℝ) ≤ (a.val : ℝ) := Nat.cast_nonneg _
      nlinarith [Real.pi_pos]
    exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt_pi).ne' hsin_sub
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact haux hlt hij
  · exact haux hgt hij.symm

private lemma tan_triple_sum_eq_mul {m : ℕ} (hm : Odd m) {i j k : ℕ} (hdvd : m ∣ i + j + k) :
    let ti := Real.tan ((i : ℝ) * Real.pi / (m : ℝ))
    let tj := Real.tan ((j : ℝ) * Real.pi / (m : ℝ))
    let tk := Real.tan ((k : ℝ) * Real.pi / (m : ℝ))
    ti + tj + tk = ti * tj * tk := by
  dsimp only
  have hm_pos : (0 : ℝ) < (m : ℝ) := by rcases hm with ⟨r, rfl⟩; positivity
  set α := (i : ℝ) * Real.pi / (m : ℝ)
  set β := (j : ℝ) * Real.pi / (m : ℝ)
  set γ := (k : ℝ) * Real.pi / (m : ℝ)
  have hca : Real.cos α ≠ 0 := cos_nat_mul_pi_div_odd_ne_zero hm i
  have hcb : Real.cos β ≠ 0 := cos_nat_mul_pi_div_odd_ne_zero hm j
  have hcg : Real.cos γ ≠ 0 := cos_nat_mul_pi_div_odd_ne_zero hm k
  rcases hdvd with ⟨q, hq⟩
  have hsum_ang : α + β + γ = (q : ℝ) * Real.pi := by
    have hqr : (i : ℝ) + (j : ℝ) + (k : ℝ) = (m : ℝ) * (q : ℝ) := by exact_mod_cast hq
    dsimp only [α, β, γ]
    field_simp
    linear_combination hqr
  have hsin0 : Real.sin (α + β + γ) = 0 := by
    rw [hsum_ang, Real.sin_nat_mul_pi]
  rw [Real.sin_add, Real.sin_add, Real.cos_add] at hsin0
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp
  linarith

private lemma card_zeroSum_triples_ge (m : ℕ) (hm : 3 ≤ m) :
    m ^ 2 ≤ 6 * ((Finset.powersetCard 3 (Finset.univ : Finset (Fin m))).filter
      (fun T => m ∣ ∑ x ∈ T, x.val)).card + 3 * m := by
  classical
  have hm0 : 0 < m := by omega
  let Triples : Finset (Finset (Fin m)) :=
    (Finset.powersetCard 3 (Finset.univ : Finset (Fin m))).filter (fun T => m ∣ ∑ x ∈ T, x.val)
  let third : Fin m × Fin m → Fin m := fun p =>
    ⟨(2 * m - p.1.val - p.2.val) % m, Nat.mod_lt _ hm0⟩
  have hthird_dvd : ∀ p : Fin m × Fin m, m ∣ p.1.val + p.2.val + (third p).val := by
    intro ⟨i, j⟩
    have hi : i.val < m := i.isLt
    have hj : j.val < m := j.isLt
    have hadd : i.val + j.val + (2 * m - i.val - j.val) = 2 * m := by omega
    have hmod : i.val + j.val + (2 * m - i.val - j.val) % m ≡ 2 * m [MOD m] := by
      calc
        i.val + j.val + (2 * m - i.val - j.val) % m
            ≡ i.val + j.val + (2 * m - i.val - j.val) [MOD m] :=
              Nat.ModEq.add_left _ (Nat.mod_modEq _ m)
        _ = 2 * m := hadd
    exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr ⟨2, by ring⟩))
  let bad1 : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 = p.2)
  let bad2 : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 = third p)
  let bad3 : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.2 = third p)
  have hbad1_card : bad1.card ≤ m := by
    have hsub : bad1 ⊆ Finset.univ.image (fun i : Fin m => (i, i)) := by
      intro p hp
      have heq : p.1 = p.2 := (Finset.mem_filter.mp hp).2
      exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl heq⟩
    exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (by simp))
  have hbad2_card : bad2.card ≤ m := by
    let f2 : Fin m → Fin m × Fin m := fun i => (i, ⟨(2 * m - 2 * i.val) % m, Nat.mod_lt _ hm0⟩)
    have hsub : bad2 ⊆ Finset.univ.image f2 := by
      intro p hp
      have heq : p.1 = third p := (Finset.mem_filter.mp hp).2
      refine Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl ?_⟩
      apply Fin.ext
      have hdvd := hthird_dvd p
      rw [← heq] at hdvd
      have h2i : 2 * p.1.val ≤ 2 * m := by have := p.1.isLt; omega
      have hmod1 : (2 * m - 2 * p.1.val) % m ≡ 2 * m - 2 * p.1.val [MOD m] := Nat.mod_modEq _ m
      have hmod2 : 2 * p.1.val + (2 * m - 2 * p.1.val) % m ≡ 0 [MOD m] := by
        calc
          2 * p.1.val + (2 * m - 2 * p.1.val) % m
              ≡ 2 * p.1.val + (2 * m - 2 * p.1.val) [MOD m] := Nat.ModEq.add_left _ hmod1
          _ = 2 * m := by omega
          _ ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.mpr ⟨2, by ring⟩
      have hmod3 : 2 * p.1.val + p.2.val ≡ 0 [MOD m] :=
        Nat.modEq_zero_iff_dvd.mpr (by convert hdvd using 1; ring)
      have hsame : (2 * m - 2 * p.1.val) % m ≡ p.2.val [MOD m] :=
        Nat.ModEq.add_left_cancel' (2 * p.1.val) (hmod2.trans hmod3.symm)
      have hlt1 : (2 * m - 2 * p.1.val) % m < m := Nat.mod_lt _ hm0
      have hlt2 : p.2.val < m := p.2.isLt
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hsame
    exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (by simp))
  have hbad3_card : bad3.card ≤ m := by
    let f3 : Fin m → Fin m × Fin m := fun j => (⟨(2 * m - 2 * j.val) % m, Nat.mod_lt _ hm0⟩, j)
    have hsub : bad3 ⊆ Finset.univ.image f3 := by
      intro p hp
      have heq : p.2 = third p := (Finset.mem_filter.mp hp).2
      refine Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, Prod.ext ?_ rfl⟩
      apply Fin.ext
      have hdvd := hthird_dvd p
      rw [← heq] at hdvd
      have h2j : 2 * p.2.val ≤ 2 * m := by have := p.2.isLt; omega
      have hmod1 : (2 * m - 2 * p.2.val) % m ≡ 2 * m - 2 * p.2.val [MOD m] := Nat.mod_modEq _ m
      have hmod2 : 2 * p.2.val + (2 * m - 2 * p.2.val) % m ≡ 0 [MOD m] := by
        calc
          2 * p.2.val + (2 * m - 2 * p.2.val) % m
              ≡ 2 * p.2.val + (2 * m - 2 * p.2.val) [MOD m] := Nat.ModEq.add_left _ hmod1
          _ = 2 * m := by omega
          _ ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.mpr ⟨2, by ring⟩
      have hmod3 : 2 * p.2.val + p.1.val ≡ 0 [MOD m] :=
        Nat.modEq_zero_iff_dvd.mpr (by convert hdvd using 1; ring)
      have hsame : (2 * m - 2 * p.2.val) % m ≡ p.1.val [MOD m] :=
        Nat.ModEq.add_left_cancel' (2 * p.2.val) (hmod2.trans hmod3.symm)
      have hlt1 : (2 * m - 2 * p.2.val) % m < m := Nat.mod_lt _ hm0
      have hlt2 : p.1.val < m := p.1.isLt
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hsame
    exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (by simp))
  let Good : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ third p ∧ p.2 ≠ third p)
  have hcover : (Finset.univ : Finset (Fin m × Fin m)) ⊆ Good ∪ bad1 ∪ bad2 ∪ bad3 := by
    intro p _
    by_cases h1 : p.1 = p.2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h1⟩)))
    by_cases h2 : p.1 = third p
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h2⟩))
    by_cases h3 : p.2 = third p
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h3⟩)
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h1, h2, h3⟩)))
  have hGood_card : m ^ 2 ≤ Good.card + 3 * m := by
    have huniv : m ^ 2 = (Finset.univ : Finset (Fin m × Fin m)).card := by simp [sq]
    have hle := Finset.card_le_card hcover
    have hu1 := Finset.card_union_le (Good ∪ bad1 ∪ bad2) bad3
    have hu2 := Finset.card_union_le (Good ∪ bad1) bad2
    have hu3 := Finset.card_union_le Good bad1
    omega
  let toTriple : Fin m × Fin m → Finset (Fin m) := fun p => {p.1, p.2, third p}
  have hmaps : ∀ p ∈ Good, toTriple p ∈ Triples := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨h12, h13, h23⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · simp [toTriple, h12, h13, h23]
    · simp only [toTriple]
      rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
        Finset.sum_singleton, ← add_assoc]
      exact hthird_dvd p
  have hfiber : ∀ T ∈ Triples, (Good.filter (fun p => toTriple p = T)).card ≤ 6 := by
    intro T hT
    have hT3 : T.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    have hsub : Good.filter (fun p => toTriple p = T) ⊆ T.offDiag := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpG, hEq⟩
      have h12 : p.1 ≠ p.2 := (Finset.mem_filter.mp hpG).2.1
      have hp1 : p.1 ∈ T := hEq ▸ by simp [toTriple]
      have hp2 : p.2 ∈ T := hEq ▸ by simp [toTriple]
      exact Finset.mem_offDiag.mpr ⟨hp1, hp2, h12⟩
    calc
      (Good.filter (fun p => toTriple p = T)).card ≤ T.offDiag.card := Finset.card_le_card hsub
      _ = 6 := by simp [Finset.offDiag_card, hT3]
  have hGood_le : Good.card ≤ 6 * Triples.card := by
    have hfib := Finset.card_eq_sum_card_fiberwise hmaps
    calc
      Good.card = ∑ T ∈ Triples, (Good.filter (fun p => toTriple p = T)).card := hfib
      _ ≤ ∑ _T ∈ Triples, 6 := Finset.sum_le_sum hfiber
      _ = 6 * Triples.card := by simp [mul_comm]
  dsimp only [Triples] at hGood_le
  omega

private lemma numLinesWithPointsMax_three_lower_nat {n : ℕ} (hn : 4 ≤ n) :
    (if Odd n then n else n - 1) ^ 2 ≤ 6 * numLinesWithPointsMax 3 n + 3 * (if Odd n then n else n - 1) := by
  classical
  set m : ℕ := if Odd n then n else n - 1
  have hm_odd : Odd m := by
    by_cases hodd : Odd n
    · simp [m, hodd]
    · simp only [m, if_neg hodd]
      rcases Nat.not_odd_iff_even.mp hodd with ⟨k, hk⟩
      exact ⟨k - 1, by omega⟩
  have hm_ge3 : 3 ≤ m := by
    by_cases hodd : Odd n <;> simp only [m, hodd, ↓reduceIte] <;> omega
  let tval : Fin m → ℝ := fun k => Real.tan ((k.val : ℝ) * Real.pi / (m : ℝ))
  let pt : Fin m → ℝ² := fun k => curvePt (tval k)
  have hpt_inj : Function.Injective pt :=
    curvePt_injective.comp (tan_nat_mul_pi_div_odd_inj hm_odd)
  let S0 : Finset ℝ² := Finset.univ.image pt
  have hS0_card : S0.card = m := by
    rw [Finset.card_image_of_injective _ hpt_inj, Finset.card_fin]
  have hex_S : ∃ S : Finset ℝ², S.card = n ∧ (S0 : Set ℝ²) ⊆ (S : Set ℝ²) ∧
      (S : Set ℝ²) ⊆ Set.range curvePt := by
    by_cases hodd : Odd n
    · have hmn : m = n := by simp [m, hodd]
      refine ⟨S0, by rw [hS0_card, hmn], Set.Subset.rfl, ?_⟩
      rintro _ h
      rcases Finset.mem_image.mp (Finset.mem_coe.mp h) with ⟨k, _, rfl⟩
      exact ⟨tval k, rfl⟩
    · have hmn : m + 1 = n := by simp only [m, if_neg hodd]; omega
      have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      let tstar : ℝ := (Finset.univ.image tval).max' (hne.image tval) + 1
      have hnot_mem : curvePt tstar ∉ S0 := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
        have ht : tval k = tstar := curvePt_injective hk
        have hle : tval k ≤ (Finset.univ.image tval).max' (hne.image tval) :=
          Finset.le_max' _ _ (Finset.mem_image_of_mem tval (Finset.mem_univ k))
        linarith
      refine ⟨insert (curvePt tstar) S0, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hnot_mem, hS0_card, hmn]
      · exact Finset.coe_subset.mpr (Finset.subset_insert _ _)
      · intro p hp
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hp) with rfl | h0
        · exact ⟨tstar, rfl⟩
        · rcases Finset.mem_image.mp h0 with ⟨k, _, rfl⟩
          exact ⟨tval k, rfl⟩
  rcases hex_S with ⟨S, hS_card, hS0_sub, hS_range⟩
  have hS_nc : NonCollinearFor 4 (S : Set ℝ²) := nonCollinearFor_four_curvePt hS_range
  let Triples : Finset (Finset (Fin m)) :=
    (Finset.powersetCard 3 (Finset.univ : Finset (Fin m))).filter (fun T => m ∣ ∑ x ∈ T, x.val)
  have hline_of_triple : ∀ T ∈ Triples,
      ∃ L ∈ linesWithPointsFor 3 (S : Set ℝ²), (L : Set ℝ²) ∩ (S : Set ℝ²) = (T.image pt : Set ℝ²) := by
    intro T hT
    rcases Finset.mem_filter.mp hT with ⟨hTpow, hTdvd⟩
    have hT3 : T.card = 3 := (Finset.mem_powersetCard.mp hTpow).2
    rcases Finset.card_eq_succ.mp hT3 with ⟨i, T1, hi1, rfl, h1⟩
    rcases Finset.card_eq_succ.mp h1 with ⟨j, T2, hj2, rfl, h2⟩
    rcases Finset.card_eq_one.mp h2 with ⟨k, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi1 hj2
    have hij : i ≠ j := hi1.1
    have hik : i ≠ k := hi1.2
    have hjk : j ≠ k := hj2
    rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
      Finset.sum_singleton, ← add_assoc] at hTdvd
    have htan_eq : tval i + tval j + tval k = tval i * tval j * tval k :=
      tan_triple_sum_eq_mul hm_odd hTdvd
    have hti_ne_tj : tval i ≠ tval j := fun h => hij (tan_nat_mul_pi_div_odd_inj hm_odd h)
    have hti_ne_tk : tval i ≠ tval k := fun h => hik (tan_nat_mul_pi_div_odd_inj hm_odd h)
    have htj_ne_tk : tval j ≠ tval k := fun h => hjk (tan_nat_mul_pi_div_odd_inj hm_odd h)
    have hcol : Collinear ℝ ({pt i, pt j, pt k} : Set ℝ²) :=
      (collinear_curvePt_iff hti_ne_tj hti_ne_tk htj_ne_tk).mpr htan_eq
    have hpi_ne_pj : pt i ≠ pt j := fun h => hij (hpt_inj h)
    let L : AffineSubspace ℝ ℝ² := affineSpan ℝ ({pt i, pt j} : Set ℝ²)
    have hpi_L : pt i ∈ L := subset_affineSpan ℝ _ (by simp)
    have hpj_L : pt j ∈ L := subset_affineSpan ℝ _ (by simp)
    have hpk_L : pt k ∈ L :=
      (mem_affineSpan_pair_iff_det3 hpi_ne_pj).mpr ((collinear_triple_iff_det3 hpi_ne_pj).mp hcol)
    have hpi_S : pt i ∈ (S : Set ℝ²) := hS0_sub (Finset.mem_coe.mpr (Finset.mem_image_of_mem pt (Finset.mem_univ i)))
    have hpj_S : pt j ∈ (S : Set ℝ²) := hS0_sub (Finset.mem_coe.mpr (Finset.mem_image_of_mem pt (Finset.mem_univ j)))
    have hpk_S : pt k ∈ (S : Set ℝ²) := hS0_sub (Finset.mem_coe.mpr (Finset.mem_image_of_mem pt (Finset.mem_univ k)))
    have hinter_eq : (L : Set ℝ²) ∩ (S : Set ℝ²) = ((({i, j, k} : Finset (Fin m)).image pt) : Set ℝ²) := by
      ext p
      constructor
      · rintro ⟨hpL, hpS⟩
        by_contra hnot
        have hnot3 : p ≠ pt i ∧ p ≠ pt j ∧ p ≠ pt k := by
          simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
            Set.image_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
          exact ⟨hnot.1, hnot.2.1, hnot.2.2⟩
        let A : Finset ℝ² := {p, pt i, pt j, pt k}
        have hA_card : (A : Set ℝ²).ncard = 4 := by
          rw [Set.ncard_coe_finset]
          have hpi_ne_pk : pt i ≠ pt k := fun h => hik (hpt_inj h)
          have hpj_ne_pk : pt j ≠ pt k := fun h => hjk (hpt_inj h)
          simp [A, hnot3.1, hnot3.2.1, hnot3.2.2, hpi_ne_pj, hpi_ne_pk, hpj_ne_pk]
        have hA_sub_S : (A : Set ℝ²) ⊆ (S : Set ℝ²) := by
          intro x hx
          simp only [A, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hpS
          · exact hpi_S
          · exact hpj_S
          · exact hpk_S
        have hA_col : Collinear ℝ (A : Set ℝ²) := by
          have hA_sub_L : (A : Set ℝ²) ⊆ (L : Set ℝ²) := by
            intro x hx
            simp only [A, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
              Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact hpL
            · exact hpi_L
            · exact hpj_L
            · exact hpk_L
          have hcol_L : Collinear ℝ (L : Set ℝ²) := by
            rw [collinear_iff_of_mem hpi_L]
            refine ⟨pt j - pt i, fun x hx => ?_⟩
            rcases (mem_affineSpan_pair_iff hpi_ne_pj).mp hx with ⟨t, rfl⟩
            refine ⟨t, ?_⟩
            ext r
            simp only [vadd_eq_add, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
            ring
          exact hcol_L.subset hA_sub_L
        exact hS_nc (A : Set ℝ²) hA_sub_S A.finite_toSet hA_card hA_col
      · intro hp
        simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
          Set.image_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨hpi_L, hpi_S⟩
        · exact ⟨hpj_L, hpj_S⟩
        · exact ⟨hpk_L, hpk_S⟩
    refine ⟨L, ⟨⟨pt i, hpi_S, pt j, hpj_S, hpi_ne_pj, rfl⟩, ?_⟩, hinter_eq⟩
    rw [hinter_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hpt_inj]
    simp [hij, hik, hjk]
  choose fL hfL_mem hfL_inter using hline_of_triple
  have hTriples_le : Triples.card ≤ (linesWithPointsFor 3 (S : Set ℝ²)).ncard := by
    have hL_fin : (linesWithPointsFor 3 (S : Set ℝ²)).Finite :=
      (linesWithPointsFor_three_upper S.finite_toSet).1
    let g : Finset (Fin m) → AffineSubspace ℝ ℝ² :=
      fun T => if hT : T ∈ Triples then fL T hT else ⊤
    have hmaps : ∀ T ∈ Triples, g T ∈ hL_fin.toFinset := by
      intro T hT
      rw [Set.Finite.mem_toFinset]
      simp only [g, dif_pos hT]
      exact hfL_mem T hT
    have hinj : Set.InjOn g (Triples : Set (Finset (Fin m))) := by
      intro T1 hT1 T2 hT2 hEq
      have hT1' : T1 ∈ Triples := Finset.mem_coe.mp hT1
      have hT2' : T2 ∈ Triples := Finset.mem_coe.mp hT2
      simp only [g, dif_pos hT1', dif_pos hT2'] at hEq
      have himg : (T1.image pt : Set ℝ²) = (T2.image pt : Set ℝ²) := by
        rw [← hfL_inter T1 hT1', hEq, hfL_inter T2 hT2']
      have himg_fin : T1.image pt = T2.image pt := Finset.coe_injective himg
      ext x
      have hx : pt x ∈ T1.image pt ↔ pt x ∈ T2.image pt := by rw [himg_fin]
      simpa [Finset.mem_image, hpt_inj.eq_iff] using hx
    calc
      Triples.card = (Triples.image g).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ hL_fin.toFinset.card := Finset.card_le_card fun L hL => by
            rcases Finset.mem_image.mp hL with ⟨T, hT, rfl⟩
            exact hmaps T hT
      _ = (linesWithPointsFor 3 (S : Set ℝ²)).ncard := by
            rw [← Set.ncard_coe_finset, hL_fin.coe_toFinset]
  have hS_le_max : (linesWithPointsFor 3 (S : Set ℝ²)).ncard ≤ numLinesWithPointsMax 3 n := by
    rw [numLinesWithPointsMax]
    exact le_csSup (numLinesWithPointsMax_three_bddAbove n)
      ⟨(S : Set ℝ²), by rw [Set.ncard_coe_finset, hS_card], S.finite_toSet, hS_nc, rfl⟩
  have hcard_ge := card_zeroSum_triples_ge m hm_ge3
  have hle : Triples.card ≤ numLinesWithPointsMax 3 n := le_trans hTriples_le hS_le_max
  dsimp only [Triples] at hle
  change m ^ 2 ≤ 6 * numLinesWithPointsMax 3 n + 3 * m
  omega

private lemma numLinesWithPointsMax_three_bounds {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) ^ 2 / 6 - (n : ℝ) ≤ (numLinesWithPointsMax 3 n : ℝ) ∧
      (numLinesWithPointsMax 3 n : ℝ) ≤ (n : ℝ) ^ 2 / 6 := by
  constructor
  · have hlow := numLinesWithPointsMax_three_lower_nat hn
    by_cases hodd : Odd n
    · simp only [if_pos hodd] at hlow
      have hlow_r : (n : ℝ) ^ 2 ≤ 6 * (numLinesWithPointsMax 3 n : ℝ) + 3 * (n : ℝ) := by
        exact_mod_cast hlow
      have hn_r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    · simp only [if_neg hodd] at hlow
      have hlow_r : ((n - 1 : ℕ) : ℝ) ^ 2 ≤
          6 * (numLinesWithPointsMax 3 n : ℝ) + 3 * ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast hlow
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hlow_r
      have hn_r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
  · have hup := numLinesWithPointsMax_three_upper n
    have hup_r : (numLinesWithPointsMax 3 n : ℝ) * 6 ≤ (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hup
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hup_r
    have hn_r : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith

end Erdos588Proof

open Erdos588 Erdos588Proof Filter

theorem OMA.solution : type_of% @Erdos588.erdos_588.variants.three_lower := by
  intro ε hε
  refine Filter.eventually_atTop.mpr ⟨max 4 (Nat.ceil (1 / ε) + 1), fun n hn => ?_⟩
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnc : Nat.ceil (1 / ε) + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hlo : (n : ℝ) ^ 2 / 6 - (n : ℝ) ≤ (numLinesWithPointsMax 3 n : ℝ) :=
    (numLinesWithPointsMax_three_bounds hn4).1
  have h1 : 1 / ε ≤ (n : ℝ) := by
    have hceil : 1 / ε ≤ (Nat.ceil (1 / ε) : ℝ) := Nat.le_ceil (1 / ε)
    have hcast : (Nat.ceil (1 / ε) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (1 / ε) ≤ n)
    linarith
  have h2 : (1 : ℝ) ≤ ε * (n : ℝ) := by
    have := mul_le_mul_of_nonneg_left h1 hε.le
    rwa [mul_one_div_cancel hε.ne'] at this
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h3 : (n : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
    calc
      (n : ℝ) = 1 * (n : ℝ) := (one_mul _).symm
      _ ≤ (ε * (n : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right h2 hn_nonneg
      _ = ε * (n : ℝ) ^ 2 := by ring
  have h4 : (1 / 6 - ε) * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 / 6 - ε * (n : ℝ) ^ 2 := by ring
  linarith
