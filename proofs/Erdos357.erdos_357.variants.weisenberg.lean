import FormalConjectures.ErdosProblems.«357»

-- Problem: Erdős Problem 357 — weisenberg
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/357.lean:115 (declaration Erdos357.erdos_357.variants.weisenberg)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

namespace OMA.E357

lemma lt_of_len (x k s t s' t' : ℤ) (hx : k ^ 2 ≤ 4 * x) (hx0 : 0 ≤ x) (h0 : 0 ≤ s)
    (hst : s ≤ t) (htk : t < k) (h0' : 0 ≤ s') (hst' : s' ≤ t') (htk' : t' < k)
    (hl : t - s < t' - s') :
    (t - s + 1) * (2 * x + 2 + s + t) < (t' - s' + 1) * (2 * x + 2 + s' + t') := by
  set l := t - s + 1 with hl1
  set l' := t' - s' + 1 with hl2
  have hlpos : 0 < l := by omega
  have hll : l + 1 ≤ l' := by omega
  have h1 : l * (2 * x + 2 + s + t) ≤ l * (2 * x + 2 * k - l + 1) :=
    mul_le_mul_of_nonneg_left (by omega) hlpos.le
  have h4 : l' * (2 * x + l' + 1) ≤ l' * (2 * x + 2 + s' + t') :=
    mul_le_mul_of_nonneg_left (by omega) (by omega)
  have h2 : (l + 1) * (2 * x + l + 2) ≤ l' * (2 * x + l' + 1) := by nlinarith
  have h3 : l * (2 * x + 2 * k - l + 1) < (l + 1) * (2 * x + l + 2) := by
    nlinarith [sq_nonneg (k - 2 * l)]
  linarith

lemma eq_of_sum (x k s t s' t' : ℤ) (hx : k ^ 2 ≤ 4 * x) (hx0 : 0 ≤ x) (h0 : 0 ≤ s)
    (hst : s ≤ t) (htk : t < k) (h0' : 0 ≤ s') (hst' : s' ≤ t') (htk' : t' < k)
    (heq : (t - s + 1) * (2 * x + 2 + s + t) = (t' - s' + 1) * (2 * x + 2 + s' + t')) :
    s = s' ∧ t = t' := by
  rcases lt_trichotomy (t - s) (t' - s') with h | h | h
  · have := lt_of_len x k s t s' t' hx hx0 h0 hst htk h0' hst' htk' h
    omega
  · rw [show t' - s' + 1 = t - s + 1 by omega] at heq
    have hpos : (0 : ℤ) < t - s + 1 := by omega
    have := mul_left_cancel₀ hpos.ne' heq
    omega
  · have := lt_of_len x k s' t' s t hx hx0 h0' hst' htk' h0 hst htk h
    omega

lemma sum_nat (c : ℤ) (s : ℕ) : ∀ d : ℕ,
    2 * ∑ j ∈ Finset.Icc s (s + d), (c + (j : ℤ)) = ((d : ℤ) + 1) * (2 * c + 2 * s + d)
  | 0 => by simp; ring
  | d + 1 => by
    rw [show s + (d + 1) = (s + d) + 1 by ring, Finset.sum_Icc_succ_top (by omega), mul_add,
      sum_nat c s d]
    push_cast
    ring

lemma sum_fin (k : ℕ) (c : ℤ) (s t : Fin k) (hst : s ≤ t) :
    2 * ∑ i ∈ Finset.Icc s t, (c + ((i : ℕ) : ℤ)) =
      (((t : ℕ) : ℤ) - ((s : ℕ) : ℤ) + 1) * (2 * c + (s : ℕ) + (t : ℕ)) := by
  have h1 : ∑ i ∈ Finset.Icc s t, (c + ((i : ℕ) : ℤ)) =
      ∑ j ∈ (Finset.Icc s t).map Fin.valEmbedding, (c + (j : ℤ)) := by
    rw [Finset.sum_map]
    rfl
  rw [h1, Fin.map_valEmbedding_Icc]
  obtain ⟨d, hd⟩ : ∃ d, (t : ℕ) = (s : ℕ) + d := ⟨(t : ℕ) - s, by
    have : (s : ℕ) ≤ t := hst
    omega⟩
  rw [hd, sum_nat]
  push_cast
  ring

lemma icc_of_ordConnected {k : ℕ} (J : Finset (Fin k)) (hJ : (J : Set (Fin k)).OrdConnected)
    (hne : J.Nonempty) : J = Finset.Icc (J.min' hne) (J.max' hne) := by
  ext i
  rw [Finset.mem_Icc]
  constructor
  · intro hi
    exact ⟨J.min'_le i hi, J.le_max' i hi⟩
  · rintro ⟨h1, h2⟩
    have := hJ.out (J.min'_mem hne) (J.max'_mem hne) ⟨h1, h2⟩
    exact this

lemma distinct (n k : ℕ) (hk : k ≤ n) (hx : (k : ℤ) ^ 2 ≤ 4 * ((n : ℤ) - k)) :
    Erdos357.HasDistinctSums (fun i : Fin k => ((n : ℤ) - k + 1 + ((i : ℕ) : ℤ))) := by
  intro J1 hJ1 J2 hJ2 heq
  simp only [Set.mem_ofPred_eq] at hJ1 hJ2
  simp only at heq
  have hc : (1 : ℤ) ≤ (n : ℤ) - k + 1 := by omega
  have hpos : ∀ J : Finset (Fin k), J.Nonempty →
      0 < ∑ i ∈ J, ((n : ℤ) - k + 1 + ((i : ℕ) : ℤ)) := by
    intro J hJ
    apply Finset.sum_pos _ hJ
    intro i _
    have : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := by positivity
    omega
  rcases J1.eq_empty_or_nonempty with h1 | h1 <;> rcases J2.eq_empty_or_nonempty with h2 | h2
  · rw [h1, h2]
  · rw [h1, Finset.sum_empty] at heq
    have := hpos J2 h2
    omega
  · rw [h2, Finset.sum_empty] at heq
    have := hpos J1 h1
    omega
  · have e1 := icc_of_ordConnected J1 hJ1 h1
    have e2 := icc_of_ordConnected J2 hJ2 h2
    set s := J1.min' h1
    set t := J1.max' h1
    set s' := J2.min' h2
    set t' := J2.max' h2
    have hst : s ≤ t := J1.min'_le _ (J1.max'_mem h1)
    have hst' : s' ≤ t' := J2.min'_le _ (J2.max'_mem h2)
    rw [e1, e2] at heq
    have q1 := sum_fin k ((n : ℤ) - k + 1) s t hst
    have q2 := sum_fin k ((n : ℤ) - k + 1) s' t' hst'
    rw [heq] at q1
    rw [q1] at q2
    have hst2 : ((s : ℕ) : ℤ) ≤ ((t : ℕ) : ℤ) := by exact_mod_cast (show (s : ℕ) ≤ t from hst)
    have hst2' : ((s' : ℕ) : ℤ) ≤ ((t' : ℕ) : ℤ) := by
      exact_mod_cast (show (s' : ℕ) ≤ t' from hst')
    have htk : ((t : ℕ) : ℤ) < k := by exact_mod_cast t.isLt
    have htk' : ((t' : ℕ) : ℤ) < k := by exact_mod_cast t'.isLt
    have key := eq_of_sum ((n : ℤ) - k) k (s : ℕ) (t : ℕ) (s' : ℕ) (t' : ℕ) hx (by omega)
      (by positivity) hst2 htk (by positivity) hst2' htk' (by linarith)
    have hs : s = s' := Fin.ext (by exact_mod_cast key.1)
    have ht : t = t' := Fin.ext (by exact_mod_cast key.2)
    rw [e1, e2, hs, ht]

lemma card_le (n k : ℕ) (a : Fin k → ℤ) (hr : Set.range a ⊆ Set.Icc 1 (n : ℤ))
    (hm : StrictMono a) : k ≤ n := by
  have h := Finset.card_le_card_of_injOn a (s := Finset.univ) (t := Finset.Icc (1 : ℤ) n)
    (by
      intro i _
      have := hr ⟨i, rfl⟩
      simpa using this)
    (hm.injective.injOn)
  simp at h
  omega

end OMA.E357

theorem OMA.solution : type_of% @Erdos357.erdos_357.variants.weisenberg := by
  refine ⟨fun n => -4 / √(n : ℝ), ?_, ?_⟩
  · show _ =o[atTop] (fun _ => (1 : ℝ))
    rw [Asymptotics.isLittleO_one_iff]
    have h := ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop).const_mul
      (-4 : ℝ)
    rw [mul_zero] at h
    refine h.congr (fun n => ?_)
    simp [div_eq_mul_inv]
  · filter_upwards [eventually_ge_atTop 4] with n hn
    set r := Nat.sqrt n with hrdef
    have hr2 : 2 ≤ r := Nat.le_sqrt.2 (by omega)
    have hrr : r * r ≤ n := Nat.sqrt_le n
    set k := 2 * r - 2 with hkdef
    have hkn : k ≤ n := by
      have : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr2
      omega
    have hx : (k : ℤ) ^ 2 ≤ 4 * ((n : ℤ) - k) := by
      have : ((k : ℕ) : ℤ) = 2 * (r : ℤ) - 2 := by omega
      rw [this]
      have : ((r * r : ℕ) : ℤ) ≤ n := by exact_mod_cast hrr
      push_cast at this
      nlinarith
    have hmem : k ∈ {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 (n : ℤ) ∧
        StrictMono a ∧ Erdos357.HasDistinctSums a} := by
      refine ⟨fun i : Fin k => ((n : ℤ) - k + 1 + ((i : ℕ) : ℤ)), ?_, ?_,
        OMA.E357.distinct n k hkn hx⟩
      · rintro _ ⟨i, rfl⟩
        have := i.isLt
        simp only [Set.mem_Icc]
        constructor <;> omega
      · intro i j hij
        have : (i : ℕ) < j := hij
        simp only
        omega
    have hbdd : BddAbove {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 (n : ℤ) ∧
        StrictMono a ∧ Erdos357.HasDistinctSums a} := by
      refine ⟨n, ?_⟩
      rintro m ⟨a, hr, hm, _⟩
      exact OMA.E357.card_le n m a hr hm
    have hf : k ≤ Erdos357.f n := le_csSup hbdd hmem
    have hfr : (k : ℝ) ≤ Erdos357.f n := by exact_mod_cast hf
    have hkr : (k : ℝ) = 2 * (r : ℝ) - 2 := by
      have : (k : ℕ) + 2 = 2 * r := by omega
      have : ((k : ℕ) : ℝ) + 2 = 2 * (r : ℝ) := by exact_mod_cast this
      linarith
    have hsq : √(n : ℝ) < (r : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
    have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
    have : (2 + -4 / √(n : ℝ)) * √(n : ℝ) = 2 * √(n : ℝ) - 4 := by
      field_simp
      ring
    rw [this]
    linarith
