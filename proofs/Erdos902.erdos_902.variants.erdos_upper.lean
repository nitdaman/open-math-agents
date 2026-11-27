import FormalConjectures.ErdosProblems.«902»
import Mathlib.Tactic

/-!
# Proof of Erdos 902 upper bound
-/

section OMA902Upper

open Erdos902

abbrev omaUpperPairs (m : ℕ) := { p : Fin m × Fin m // p.1 < p.2 }

def omaTourOf {m : ℕ} (ω : omaUpperPairs m → Bool) : Digraph (Fin m) where
  Adj u v :=
    if h : u < v then ω ⟨(u, v), h⟩ = true
    else if h' : v < u then ω ⟨(v, u), h'⟩ = false
    else False

lemma omaTourOf_isTournament {m : ℕ} (ω : omaUpperPairs m → Bool) :
    (omaTourOf ω).IsTournament := by
  refine ⟨fun v => by simp [omaTourOf], fun u v huv => ?_⟩
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · have hnot : ¬ v < u := asymm hlt
    simp [omaTourOf, hlt, hnot]
  · have hnot : ¬ u < v := asymm hgt
    simp [omaTourOf, hgt, hnot]

def omaEdgeOf {m : ℕ} {u v : Fin m} (huv : u ≠ v) : omaUpperPairs m :=
  if h : u < v then ⟨(u, v), h⟩
  else ⟨(v, u), lt_of_le_of_ne (le_of_not_gt h) huv.symm⟩

def omaWinBit {m : ℕ} (u v : Fin m) : Bool := decide (u < v)

lemma omaEdgeOf_eq_or {m : ℕ} {u₁ v₁ u₂ v₂ : Fin m} (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂)
    (heq : omaEdgeOf h1 = omaEdgeOf h2) :
    (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂) := by
  dsimp [omaEdgeOf] at heq
  by_cases c1 : u₁ < v₁ <;> by_cases c2 : u₂ < v₂
  · rw [dif_pos c1, dif_pos c2] at heq
    have hv := congrArg Subtype.val heq
    exact Or.inl ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
  · rw [dif_pos c1, dif_neg c2] at heq
    have hv := congrArg Subtype.val heq
    exact Or.inr ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
  · rw [dif_neg c1, dif_pos c2] at heq
    have hv := congrArg Subtype.val heq
    exact Or.inr ⟨congrArg Prod.snd hv, congrArg Prod.fst hv⟩
  · rw [dif_neg c1, dif_neg c2] at heq
    have hv := congrArg Subtype.val heq
    exact Or.inl ⟨congrArg Prod.snd hv, congrArg Prod.fst hv⟩

lemma omaTourOf_adj_iff {m : ℕ} (ω : omaUpperPairs m → Bool) {u v : Fin m} (huv : u ≠ v) :
    (omaTourOf ω).Adj u v ↔ ω (omaEdgeOf huv) = omaWinBit u v := by
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · simp [omaTourOf, omaEdgeOf, omaWinBit, hlt]
  · have hnot : ¬ u < v := asymm hgt
    simp [omaTourOf, omaEdgeOf, omaWinBit, hgt, hnot]

lemma oma_exists_tournament_of_ineq {m n : ℕ}
    (hineq : m.choose n * (2 ^ n - 1) ^ (m - n) < (2 ^ n) ^ (m - n)) :
    ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n := by
  classical
  let AllSub := (Finset.univ : Finset (Fin m)).powersetCard n
  let BadFor (E : Finset (Fin m)) : Finset (omaUpperPairs m → Bool) :=
    Finset.univ.filter (fun ω => ∀ x ∈ Finset.univ \ E, ¬ (∀ e ∈ E, (omaTourOf ω).Adj x e))
  have hBad_card : ∀ E ∈ AllSub,
      (BadFor E).card * (2 ^ n) ^ (m - n) =
        (2 ^ n - 1) ^ (m - n) * Fintype.card (omaUpperPairs m → Bool) := by
    intro E hE
    have hE_card : E.card = n := (Finset.mem_powersetCard.1 hE).2
    have hEc_card : (Finset.univ \ E).card = m - n := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.subset_univ E),
        Finset.card_univ, Fintype.card_fin, hE_card]
    let XE := ↥(Finset.univ \ E)
    let EE := ↥E
    have hXE_card : Fintype.card XE = m - n := by
      rw [Fintype.card_coe, hEc_card]
    have hEE_card : Fintype.card EE = n := by
      rw [Fintype.card_coe, hE_card]
    let crossEmb : XE × EE ↪ omaUpperPairs m :=
      ⟨fun p => omaEdgeOf (u := p.1.1) (v := p.2.1)
          (fun heq => (Finset.mem_sdiff.1 p.1.2).2 (by rw [heq]; exact p.2.2)),
       fun p₁ p₂ heq => by
        rcases omaEdgeOf_eq_or _ _ heq with ⟨h1, h2⟩ | ⟨h1, _⟩
        · exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
        · exact ((Finset.mem_sdiff.1 p₁.1.2).2 (by rw [h1]; exact p₂.2.2)).elim⟩
    let CrossSet : Finset (omaUpperPairs m) := Finset.univ.map crossEmb
    let Rest := { q : omaUpperPairs m // q ∉ CrossSet }
    let splitEquiv : (omaUpperPairs m → Bool) ≃ ((XE → (EE → Bool)) × (Rest → Bool)) :=
      { toFun := fun ω => (fun x e => ω (crossEmb (x, e)), fun q => ω q.1)
        invFun := fun fg p =>
          if hp : p ∈ CrossSet then
            let xe := Classical.choose (Finset.mem_map.1 hp)
            fg.1 xe.1 xe.2
          else fg.2 ⟨p, hp⟩
        left_inv := fun ω => by
          ext p
          by_cases hp : p ∈ CrossSet
          · simp only [dif_pos hp]
            have hspec := (Classical.choose_spec (Finset.mem_map.1 hp)).2
            rw [hspec]
          · simp only [dif_neg hp]
        right_inv := fun ⟨f, g⟩ => by
          ext1
          · ext x e
            have hp : crossEmb (x, e) ∈ CrossSet :=
              Finset.mem_map.2 ⟨(x, e), Finset.mem_univ _, rfl⟩
            simp only [dif_pos hp]
            have hspec := (Classical.choose_spec (Finset.mem_map.1 hp)).2
            have heq := crossEmb.injective hspec
            rw [heq]
          · ext ⟨q, hq⟩
            simp only [dif_neg hq] }
    let GoodX (x : XE) : Finset (EE → Bool) :=
      Finset.univ.erase (fun e : EE => omaWinBit x.1 e.1)
    have hGoodX_card : ∀ x : XE, (GoodX x).card = 2 ^ n - 1 := by
      intro x
      dsimp [GoodX]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, hEE_card]
    let GoodF : Finset (XE → (EE → Bool)) :=
      Finset.univ.filter (fun f => ∀ x : XE, f x ∈ GoodX x)
    have hGoodF_card : GoodF.card = (2 ^ n - 1) ^ (m - n) := by
      have hpi : GoodF = Fintype.piFinset GoodX := by
        ext f
        simp [GoodF, Fintype.mem_piFinset]
      rw [hpi, Fintype.card_piFinset, Finset.prod_congr rfl (fun x _ => hGoodX_card x),
        Finset.prod_const, Finset.card_univ, hXE_card]
    have hBad_equiv : (BadFor E).card = GoodF.card * Fintype.card (Rest → Bool) := by
      rw [← Finset.card_univ (α := Rest → Bool), ← Finset.card_product]
      refine Finset.card_bij (fun ω _ => splitEquiv ω) ?_ ?_ ?_
      · intro ω hω
        have hbad := (Finset.mem_filter.1 hω).2
        refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => ?_⟩,
          Finset.mem_univ _⟩
        dsimp [GoodX]
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro heq_fn
        apply hbad x.1 x.2
        intro e he
        have hx_ne_e : x.1 ≠ e := fun h => (Finset.mem_sdiff.1 x.2).2 (h ▸ he)
        rw [omaTourOf_adj_iff ω hx_ne_e]
        have hedge : omaEdgeOf hx_ne_e = crossEmb (x, ⟨e, he⟩) := rfl
        rw [hedge]
        exact congr_fun heq_fn ⟨e, he⟩
      · intro ω₁ _ ω₂ _ heq
        exact splitEquiv.injective heq
      · intro fg hfg
        rcases Finset.mem_product.1 hfg with ⟨hf, _⟩
        have hf_good := (Finset.mem_filter.1 hf).2
        refine ⟨splitEquiv.symm fg, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
          splitEquiv.apply_symm_apply fg⟩
        intro x hx hall
        have hx_good := hf_good ⟨x, hx⟩
        dsimp [GoodX] at hx_good
        have hne_fn := (Finset.mem_erase.1 hx_good).1
        apply hne_fn
        ext ⟨e, he⟩
        have hx_ne_e : x ≠ e := fun h => (Finset.mem_sdiff.1 hx).2 (h ▸ he)
        have hadj := hall e he
        rw [omaTourOf_adj_iff _ hx_ne_e] at hadj
        have hedge : omaEdgeOf hx_ne_e = crossEmb (⟨x, hx⟩, ⟨e, he⟩) := rfl
        rw [hedge] at hadj
        have hsymm : splitEquiv (splitEquiv.symm fg) = fg := splitEquiv.apply_symm_apply fg
        have h1 : splitEquiv.symm fg (crossEmb (⟨x, hx⟩, ⟨e, he⟩)) = fg.1 ⟨x, hx⟩ ⟨e, he⟩ :=
          congr_fun (congr_fun (congrArg Prod.fst hsymm) ⟨x, hx⟩) ⟨e, he⟩
        exact h1.symm.trans hadj
    have hTotal_equiv : Fintype.card (omaUpperPairs m → Bool) =
        (2 ^ n) ^ (m - n) * Fintype.card (Rest → Bool) := by
      rw [Fintype.card_congr splitEquiv, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fun, Fintype.card_bool, hEE_card, hXE_card]
    rw [hBad_equiv, hGoodF_card, hTotal_equiv]
    ring
  have hUnion_lt : (AllSub.biUnion BadFor).card < Fintype.card (omaUpperPairs m → Bool) := by
    have hmul_lt : (AllSub.biUnion BadFor).card * (2 ^ n) ^ (m - n) <
        Fintype.card (omaUpperPairs m → Bool) * (2 ^ n) ^ (m - n) := by
      calc (AllSub.biUnion BadFor).card * (2 ^ n) ^ (m - n)
        _ ≤ (∑ E ∈ AllSub, (BadFor E).card) * (2 ^ n) ^ (m - n) :=
            Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ E ∈ AllSub, (BadFor E).card * (2 ^ n) ^ (m - n) := Finset.sum_mul _ _ _
        _ = ∑ E ∈ AllSub, (2 ^ n - 1) ^ (m - n) * Fintype.card (omaUpperPairs m → Bool) :=
            Finset.sum_congr rfl hBad_card
        _ = AllSub.card * ((2 ^ n - 1) ^ (m - n) * Fintype.card (omaUpperPairs m → Bool)) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = (m.choose n * (2 ^ n - 1) ^ (m - n)) * Fintype.card (omaUpperPairs m → Bool) := by
            have hAll_card : AllSub.card = m.choose n := by
              dsimp [AllSub]; rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
            rw [hAll_card]; ring
        _ < (2 ^ n) ^ (m - n) * Fintype.card (omaUpperPairs m → Bool) :=
            Nat.mul_lt_mul_of_pos_right hineq Fintype.card_pos
        _ = Fintype.card (omaUpperPairs m → Bool) * (2 ^ n) ^ (m - n) := mul_comm _ _
    exact lt_of_mul_lt_mul_right hmul_lt (Nat.zero_le _)
  have hNotUniv : AllSub.biUnion BadFor ≠ Finset.univ := by
    intro heq
    rw [heq, Finset.card_univ] at hUnion_lt
    exact lt_irrefl _ hUnion_lt
  obtain ⟨ω, hω_not⟩ : ∃ ω : omaUpperPairs m → Bool, ω ∉ AllSub.biUnion BadFor := by
    by_contra hall
    push Not at hall
    exact hNotUniv (Finset.eq_univ_iff_forall.2 hall)
  refine ⟨omaTourOf ω, omaTourOf_isTournament ω, ?_⟩
  intro E hE_card
  have hE_mem : E ∈ AllSub := Finset.mem_powersetCard.2 ⟨Finset.subset_univ E, hE_card⟩
  have hω_not_E : ω ∉ BadFor E := fun h => hω_not (Finset.mem_biUnion.2 ⟨E, hE_mem, h⟩)
  dsimp [BadFor] at hω_not_E
  rw [Finset.mem_filter] at hω_not_E
  push Not at hω_not_E
  obtain ⟨x, hx, hdom⟩ := hω_not_E (Finset.mem_univ ω)
  exact ⟨x, (Finset.mem_sdiff.1 hx).2, hdom⟩

lemma oma_choose_le_pow : ∀ (m n : ℕ), m.choose n ≤ m ^ n
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | m + 1, n + 1 => by
    rw [Nat.choose_succ_succ, pow_succ]
    have ih1 := oma_choose_le_pow m n
    have ih2 := oma_choose_le_pow m (n + 1)
    have hmono : m ^ n ≤ (m + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ m) n
    calc m.choose n + m.choose (n + 1)
      _ ≤ m ^ n + m ^ (n + 1) := Nat.add_le_add ih1 ih2
      _ = m ^ n * (m + 1) := by rw [pow_succ]; ring
      _ ≤ (m + 1) ^ n * (m + 1) := Nat.mul_le_mul_right (m + 1) hmono

end OMA902Upper

theorem OMA.solution : type_of% @Erdos902.erdos_902.variants.erdos_upper := by
  intro ε hε
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc_pos : 0 < Real.log 2 + ε := by linarith
  set δ := ε / 8
  have hδ_pos : 0 < δ := by positivity
  set C_const := |Real.log (Real.log 2 + ε)| + 2 * |Real.log δ| + 1
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max 2 (8 / ε)) (4 * C_const / ε))
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hN_lt_n : max (max 2 (8 / ε)) (4 * C_const / ε) < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hn_gt2 : (2 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN_lt_n
  have hn_pos_nat : 2 ≤ n := by exact_mod_cast (le_of_lt hn_gt2)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_eps1 : 8 / ε < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN_lt_n
  have hn_eps2 : 4 * C_const / ε < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hN_lt_n
  set M_real : ℝ := (Real.log 2 + ε) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n
  have h2n_ge4 : (4 : ℝ) ≤ (2 : ℝ) ^ n := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn_pos_nat
    exact_mod_cast h4
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hM_nonneg : 0 ≤ M_real := by positivity
  set m : ℕ := Nat.floor M_real
  have hm_le_M : (m : ℝ) ≤ M_real := Nat.floor_le hM_nonneg
  have hM_lt_m1 : M_real - 1 < (m : ℝ) := Nat.sub_one_lt_floor M_real
  have heps_n : 8 < (n : ℝ) * ε := (div_lt_iff₀ hε).1 hn_eps1
  have hquarter_margin : (n : ℝ) + 2 ≤ (ε / 4) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n := by
    have h1 : 2 * (n : ℝ) ≤ (ε / 4) * (n : ℝ) ^ 2 := by nlinarith
    have h2 : (ε / 4) * (n : ℝ) ^ 2 * 1 ≤ (ε / 4) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hm_gt_n1 : (n : ℝ) + 1 < (m : ℝ) := by
    have hbase : 0 ≤ Real.log 2 * (n : ℝ) ^ 2 * (2 : ℝ) ^ n := by positivity
    dsimp [M_real] at hM_lt_m1
    nlinarith
  have hnm : n ≤ m := by
    have hlt_nat : n < m := by exact_mod_cast (by linarith : (n : ℝ) < (m : ℝ))
    omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmn_lower : (Real.log 2 + 3 * ε / 4) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n < ((m - n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hnm]
    dsimp [M_real] at hM_lt_m1
    nlinarith
  have hlog_m_le : Real.log (m : ℝ) ≤ (Real.log 2 + ε / 2) * (n : ℝ) := by
    have hl1 : Real.log (m : ℝ) ≤ Real.log M_real := Real.log_le_log hm_pos hm_le_M
    have hM_split : Real.log M_real =
        Real.log (Real.log 2 + ε) + 2 * Real.log (n : ℝ) + (n : ℝ) * Real.log 2 := by
      dsimp [M_real]
      rw [Real.log_mul (by positivity) (ne_of_gt h2n_pos),
        Real.log_mul (ne_of_gt hc_pos) (by positivity),
        Real.log_pow, Real.log_pow]
      ring
    have hlog_n : Real.log (n : ℝ) ≤ δ * (n : ℝ) - Real.log δ := by
      have hprod_pos : 0 < δ * (n : ℝ) := by positivity
      have h := Real.log_le_sub_one_of_pos hprod_pos
      rw [Real.log_mul (ne_of_gt hδ_pos) (ne_of_gt hn_pos)] at h
      linarith
    have hC1 : Real.log (Real.log 2 + ε) ≤ |Real.log (Real.log 2 + ε)| := le_abs_self _
    have hC2 : -Real.log δ ≤ |Real.log δ| := neg_le_abs _
    have hC_bound : 4 * C_const < (n : ℝ) * ε := (div_lt_iff₀ hε).1 hn_eps2
    dsimp [C_const, δ] at hC_bound hlog_n hC2
    linarith
  set b := 2 ^ n - 1
  have hb_pos : 1 ≤ b := by
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hb_eq : (b : ℝ) = (2 : ℝ) ^ n - 1 := by
    have h1 : 1 ≤ 2 ^ n := by omega
    dsimp [b]
    rw [Nat.cast_sub h1]
    simp
  set u : ℝ := (b : ℝ) / (2 : ℝ) ^ n
  have hu_pos : 0 < u := by positivity
  have hlog_u : Real.log u ≤ -(1 / (2 : ℝ) ^ n) := by
    have h := Real.log_le_sub_one_of_pos hu_pos
    have hu_sub : u - 1 = -(1 / (2 : ℝ) ^ n) := by
      dsimp [u]
      rw [hb_eq]
      field_simp [ne_of_gt h2n_pos]
      ring
    linarith
  have hlog_tot_neg : Real.log ((m : ℝ) ^ n * u ^ (m - n)) < 0 := by
    rw [Real.log_mul (ne_of_gt (pow_pos hm_pos n)) (ne_of_gt (pow_pos hu_pos (m - n))),
      Real.log_pow, Real.log_pow]
    have hterm1 : (n : ℝ) * Real.log (m : ℝ) ≤ (Real.log 2 + ε / 2) * (n : ℝ) ^ 2 := by
      have hm1 := mul_le_mul_of_nonneg_left hlog_m_le (le_of_lt hn_pos)
      linarith [show (n : ℝ) * ((Real.log 2 + ε / 2) * (n : ℝ)) =
        (Real.log 2 + ε / 2) * (n : ℝ) ^ 2 by ring]
    have hterm2_a : ((m - n : ℕ) : ℝ) * Real.log u ≤
        ((m - n : ℕ) : ℝ) * (-(1 / (2 : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left hlog_u (Nat.cast_nonneg _)
    have hterm2_b : ((m - n : ℕ) : ℝ) * (-(1 / (2 : ℝ) ^ n)) <
        -(Real.log 2 + 3 * ε / 4) * (n : ℝ) ^ 2 := by
      have hdiv_lt : (Real.log 2 + 3 * ε / 4) * (n : ℝ) ^ 2 <
          ((m - n : ℕ) : ℝ) * (1 / (2 : ℝ) ^ n) := by
        have hm2 := mul_lt_mul_of_pos_right hmn_lower (one_div_pos.2 h2n_pos)
        rwa [mul_assoc, mul_one_div_cancel (ne_of_gt h2n_pos), mul_one] at hm2
      linarith
    have hn2_pos : 0 < (n : ℝ) ^ 2 := by positivity
    nlinarith
  have hprod_lt_one : (m : ℝ) ^ n * u ^ (m - n) < 1 := by
    have hprod_pos : 0 < (m : ℝ) ^ n * u ^ (m - n) := by positivity
    have hexp := Real.exp_lt_exp.2 hlog_tot_neg
    rwa [Real.exp_log hprod_pos, Real.exp_zero] at hexp
  have hineq : m.choose n * (2 ^ n - 1) ^ (m - n) < (2 ^ n) ^ (m - n) := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (oma_choose_le_pow m n)) ?_
    have hmul_2n := mul_lt_mul_of_pos_right hprod_lt_one (pow_pos h2n_pos (m - n))
    rw [one_mul, mul_assoc] at hmul_2n
    have hu_cancel : u ^ (m - n) * ((2 : ℝ) ^ n) ^ (m - n) = (b : ℝ) ^ (m - n) := by
      dsimp [u]
      rw [div_pow, div_mul_cancel₀ _ (ne_of_gt (pow_pos h2n_pos (m - n)))]
    rw [hu_cancel] at hmul_2n
    have hcast_goal : (((m ^ n * b ^ (m - n) : ℕ) : ℝ)) < (((2 ^ n) ^ (m - n) : ℕ) : ℝ) := by
      push_cast
      exact hmul_2n
    exact_mod_cast hcast_goal
  have hfn_le_m : Erdos902.f n ≤ m :=
    Nat.sInf_le ⟨hnm, oma_exists_tournament_of_ineq hineq⟩
  exact le_trans (by exact_mod_cast hfn_le_m) hm_le_M
