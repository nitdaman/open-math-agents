import FormalConjectures.ErdosProblems.«823»

/-!
# Equal totients and dense ratios

The tail products of p/(p−1) give dense ratios P/φ(P). For a prime q ≡ 1 modulo φ(P), put t=(q−1)/φ(P) and take k to be the product of primes dividing t but not P. The two numbers Pkt and qk have equal totients and ratio (P/φ(P))(1−1/q).

Formalization by @Halldon.
-/

/- Ratios of a squarefree integer to its totient approximate every real number at least one. -/

namespace TotientRatioDensity

open Filter Finset

private lemma ratio_of_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ((∏ p ∈ s, p : ℕ) : ℝ) / (∏ p ∈ s, p : ℕ).totient =
      ∏ p ∈ s, (1 + 1 / ((p : ℝ) - 1)) := by
  let a : ℕ := ∏ p ∈ s, p
  have ha : 0 < a := Finset.prod_pos fun p hp => (hs p hp).pos
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hpf : a.primeFactors = s := Nat.primeFactors_prod hs
  have heq := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors a)
  push_cast at heq
  change (a : ℝ) / a.totient = _
  rw [heq, hpf, div_mul_cancel_left₀ ha', ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have h1 : (1 : ℝ) < p := by exact_mod_cast (hs p hp).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hsub : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by
    field_simp
  rw [hsub, inv_div]
  field_simp
  ring

theorem approximate (α ε : ℝ) (hα : 1 ≤ α) (hε : 0 < ε) :
    ∃ P : ℕ, 0 < P ∧ |(P : ℝ) / P.totient - α| < ε := by
  classical
  by_cases hunit : α = 1
  · exact ⟨1, by decide, by simpa [hunit] using hε⟩
  have hgt : 1 < α := lt_of_le_of_ne hα (Ne.symm hunit)
  have hpos : 0 < α := by linarith
  obtain ⟨K,hK⟩ := exists_nat_gt (1 + α / ε)
  let u (p : ℕ) : ℝ := if K ≤ p ∧ p.Prime then 1 / (p : ℝ) else 0
  let F (p : ℕ) : ℝ := if K ≤ p ∧ p.Prime then 1 + 1 / ((p : ℝ) - 1) else 1
  let R (n : ℕ) : ℝ := ∏ p ∈ range n, F p
  have hu (p : ℕ) : 0 ≤ u p := by dsimp [u]; split <;> positivity
  have hdiv : ¬Summable u := by
    intro h
    apply not_summable_one_div_on_primes
    apply h.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop K] with p hp
    simp [u, hp, Set.indicator_apply]
  have hlim := (not_summable_iff_tendsto_nat_atTop_of_nonneg hu).mp hdiv
  have hstep (p : ℕ) : 1 + u p ≤ F p ∧ F p < 1 + ε / α := by
    by_cases h : K ≤ p ∧ p.Prime
    · have hp1 : (1 : ℝ) < p := by exact_mod_cast h.2.one_lt
      have hkp : (K : ℝ) ≤ p := by exact_mod_cast h.1
      have hlarge : α < ((p : ℝ) - 1) * ε :=
        (div_lt_iff₀ hε).mp (by linarith)
      have hlow : (1 : ℝ) / p ≤ 1 / ((p : ℝ) - 1) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      have hupp : (1 : ℝ) / ((p : ℝ) - 1) < ε / α :=
        (div_lt_div_iff₀ (by linarith : 0 < (p : ℝ) - 1) hpos).mpr (by nlinarith)
      rw [show u p = 1 / (p : ℝ) by simp [u,h],
        show F p = 1 + 1 / ((p : ℝ) - 1) by simp [F,h]]
      constructor <;> linarith
    · simp [u,F,h,div_pos hε hpos]
  have hF (p : ℕ) : 1 ≤ F p := by linarith [(hstep p).1, hu p]
  have hR (n : ℕ) : 1 ≤ R n := Finset.one_le_prod fun p _ => hF p
  have hsum (n : ℕ) : 1 + ∑ p ∈ range n, u p ≤ R n := by
    induction n with
    | zero => simp [R]
    | succ n ih =>
      simp only [Finset.sum_range_succ]
      rw [show R (n+1) = R n * F n by simp [R, Finset.prod_range_succ]]
      calc
        _ ≤ R n + u n := by linarith
        _ ≤ R n * (1 + u n) := by nlinarith [mul_nonneg (sub_nonneg.mpr (hR n)) (hu n)]
        _ ≤ R n * F n := mul_le_mul_of_nonneg_left (hstep n).1 (by linarith [hR n])
  have hex : ∃ n, α ≤ R n := by
    obtain ⟨n,hn⟩ := ((tendsto_atTop.mp hlim) α).exists
    exact ⟨n,by linarith [hsum n]⟩
  let n := Nat.find hex
  have hn : α ≤ R n := Nat.find_spec hex
  have hnu : R n < α + ε := by
    cases hn' : n with
    | zero => simpa [hn',R] using (show 1 < α + ε by linarith)
    | succ m =>
      have hm : m < Nat.find hex := by change m < n; omega
      have hmR : R m < α := lt_of_not_ge (Nat.find_min hex hm)
      rw [show R (m+1) = R m * F m by simp [R, Finset.prod_range_succ]]
      calc
        _ ≤ α * F m := mul_le_mul_of_nonneg_right hmR.le (by linarith [hF m])
        _ < α * (1 + ε / α) := mul_lt_mul_of_pos_left (hstep m).2 hpos
        _ = _ := by field_simp
  let s := (range n).filter fun p => K ≤ p ∧ p.Prime
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.2
  refine ⟨∏ p ∈ s, p, Finset.prod_pos (fun p hp => (hs p hp).pos), ?_⟩
  have heq : ((∏ p ∈ s, p : ℕ) : ℝ) / (∏ p ∈ s,p : ℕ).totient = R n := by
    rw [ratio_of_primes s hs]
    exact Finset.prod_filter _ _
  rw [heq, abs_of_nonneg (sub_nonneg.mpr hn)]
  linarith

end TotientRatioDensity

open Filter Topology
namespace TotientPair

-- Multiplying by a number supported on the same primes scales the totient linearly.
private lemma scale {a t : ℕ} (ha : 0 < a) (ht : 0 < t)
    (hs : t.primeFactors ⊆ a.primeFactors) :
    (a * t).totient = t * a.totient := by
  have h : (a * t).primeFactors = a.primeFactors := by
    rw [Nat.primeFactors_mul ha.ne' ht.ne', Finset.union_eq_left.mpr hs]
  have hq : ((a * t).totient : ℚ) = (t : ℚ) * (a.totient : ℚ) := by
    rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors, h, Nat.cast_mul]
    ring
  exact_mod_cast hq

-- For q ≡ 1 modulo φ(P), realize the ratio P(q−1)/(φ(P)q) exactly.
lemma realize {P q : ℕ} (hP : 0 < P) (hq : q.Prime)
    (hcong : q ≡ 1 [MOD P.totient]) :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ n.totient = m.totient ∧
      (n : ℝ) / m = ((P : ℝ) / P.totient) * (1 - 1 / (q : ℝ)) := by
  classical
  obtain ⟨t, htq⟩ := (Nat.modEq_iff_dvd' hq.one_lt.le).mp hcong.symm
  have ht : 0 < t := by
    by_contra! hz
    have : t = 0 := by omega
    simp [this] at htq
    have := hq.one_lt
    omega
  have htlt : t < q := by
    have := Nat.le_mul_of_pos_left t (Nat.totient_pos.mpr hP)
    omega
  let S := t.primeFactors \ P.primeFactors
  let k := ∏ p ∈ S, p
  have hs (p : ℕ) (h : p ∈ S) : p.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp h).1
  have hk : 0 < k := Finset.prod_pos (fun p hp => (hs p hp).pos)
  have hkf : k.primeFactors = S := Nat.primeFactors_prod hs
  have hPk : P.Coprime k := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    exact ((hs p hp).coprime_iff_not_dvd.mpr (fun hd =>
      (Finset.mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr ⟨hs p hp, hd, hP.ne'⟩))).symm
  have hqk : q.Coprime k := by
    apply hq.coprime_iff_not_dvd.mpr
    intro hd
    have hmem := Nat.mem_primeFactors.mpr ⟨hq, hd, hk.ne'⟩
    rw [hkf] at hmem
    have hdvd := Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hmem).1
    exact (Nat.le_of_dvd ht hdvd).not_gt htlt
  have hsubset : t.primeFactors ⊆ (P*k).primeFactors := by
    rw [Nat.primeFactors_mul hP.ne' hk.ne', hkf]
    intro p hp
    by_cases h : p ∈ P.primeFactors
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp,h⟩)
  refine ⟨(P*k)*t, q*k, by positivity, Nat.mul_pos hq.pos hk, ?_, ?_⟩
  · rw [scale (Nat.mul_pos hP hk) ht hsubset, Nat.totient_mul hPk, Nat.totient_mul hqk,
        Nat.totient_prime hq, htq]
    ring
  · have hcast : (q : ℝ) - 1 = (P.totient : ℝ) * t := by
      have hc := congrArg (fun a : ℕ => (a : ℝ)) htq
      simpa [Nat.cast_sub hq.one_lt.le] using hc
    push_cast
    have hφ : (P.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hP).ne'
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
    nlinarith [congrArg (fun z : ℝ => z * (P:ℝ) * k) hcast]

end TotientPair

namespace TotientPair

lemma sequences (dense : ∀ α ε : ℝ, 1 ≤ α → 0 < ε →
    ∃ P : ℕ, 0 < P ∧ |(P : ℝ) / P.totient - α| < ε) (α : ℝ) (hα : 1 ≤ α) :
    ∃ n m : ℕ → ℕ, (∀ i, 0 < n i) ∧ (∀ i, 0 < m i) ∧
      (∀ i, (n i).totient = (m i).totient) ∧
      Tendsto (fun i => (n i : ℝ) / m i) atTop (𝓝 α) := by
  let A : Set ℝ := {x | ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ n.totient = m.totient ∧ (n : ℝ) / m = x}
  have hc : α ∈ closure A := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨P,hP,hclose⟩ := dense α (ε/2) hα (by positivity)
    let r : ℝ := (P : ℝ) / P.totient
    have hr : 0 < r := div_pos (by exact_mod_cast hP) (by exact_mod_cast Nat.totient_pos.mpr hP)
    obtain ⟨N,hN⟩ := exists_nat_gt (r / (ε/2))
    obtain ⟨q,hq,hqN,hcong⟩ := Nat.exists_prime_gt_modEq_one N (Nat.totient_pos.mpr hP).ne'
    obtain ⟨n,m,hn,hm,heq,hratio⟩ := realize hP hq hcong
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hbound : r / (q : ℝ) < ε/2 := by
      apply (div_lt_iff₀ hqr).mpr
      have hlarge : r / (ε/2) < (q : ℝ) := hN.trans (by exact_mod_cast hqN)
      have hz := (div_lt_iff₀ (by positivity : 0 < ε/2)).mp hlarge
      linarith
    refine ⟨(n : ℝ)/m, ⟨n,m,hn,hm,heq,rfl⟩, ?_⟩
    calc
      dist α ((n : ℝ)/m) ≤ dist α r + dist r ((n : ℝ)/m) := dist_triangle _ _ _
      _ < ε := by
        rw [dist_comm α r, Real.dist_eq, Real.dist_eq, hratio]
        change |r - α| + |r - r * (1 - 1 / (q : ℝ))| < ε
        rw [show r - r * (1 - 1 / (q : ℝ)) = r / q by ring, abs_of_pos (div_pos hr hqr)]
        change |r - α| < ε/2 at hclose
        linarith
  obtain ⟨s,hs,hlim⟩ := mem_closure_iff_seq_limit.mp hc
  change ∀ i, ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ n.totient = m.totient ∧ (n:ℝ)/m = s i at hs
  choose n m hn hm heq hr using hs
  exact ⟨n,m,hn,hm,heq,(show (fun i => (n i : ℝ) / m i) = s from funext hr) ▸ hlim⟩
end TotientPair

theorem OMA.solution : type_of% @Erdos823.erdos_823.variants.totient :=
  TotientPair.sequences TotientRatioDensity.approximate
