import FormalConjectures.ErdosProblems.«882»

/-!
# Erdős Problem 882
The upper estimate counts distinct subset sums; the lower estimate uses the shifted
binary construction of Csaba Sándor, as reported by Paul Erdős in
*Some of my new and almost new problems and results in combinatorial number theory* (1998).
-/

open Finset Filter
open scoped BigOperators Topology

namespace OMA

private theorem max_spec (n : ℕ) :
    ∃ A ⊆ Icc 1 n, Erdos882.IsSubsetSumAntichain A ∧
      A.card = Erdos882.maxAntichainCard n := by
  classical
  let admissible : Set ℕ := {k | ∃ A ⊆ Icc 1 n, Erdos882.IsSubsetSumAntichain A ∧ A.card = k}
  change sSup admissible ∈ admissible
  apply Nat.sSup_mem
  · exact ⟨0, ∅, empty_subset _, by simp [Erdos882.IsSubsetSumAntichain], rfl⟩
  · refine ⟨(Icc 1 n).card, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    exact card_le_card hA

private theorem card_le_max {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hB : Erdos882.IsSubsetSumAntichain A) : A.card ≤ Erdos882.maxAntichainCard n := by
  classical
  unfold Erdos882.maxAntichainCard
  apply le_csSup
  · refine ⟨(Icc 1 n).card, ?_⟩
    rintro k ⟨B, hB', -, rfl⟩
    exact card_le_card hB'
  · exact ⟨A, hA, hB, rfl⟩

private theorem count_upper (n : ℕ) :
    2 ^ Erdos882.maxAntichainCard n ≤ Erdos882.maxAntichainCard n * n + 1 := by
  classical
  obtain ⟨A, hA, hanti, hk⟩ := max_spec n
  rw [← hk]
  let f : Finset ℕ → ℕ := fun S => ∑ a ∈ S, a
  have hi : Set.InjOn f ↑A.powerset := by
    intro S hS T hT heq
    have hSA := mem_powerset.mp (mem_coe.mp hS)
    have hTA := mem_powerset.mp (mem_coe.mp hT)
    have hf : ∀ U : Finset ℕ, U ⊆ A → U.Nonempty → 0 < f U := by
      intro U hU hn
      obtain ⟨i, hi⟩ := hn
      exact (mem_Icc.mp (hA (hU hi))).1.trans (single_le_sum (fun j _ => Nat.zero_le j) hi)
    by_contra hne
    rcases eq_empty_or_nonempty S with rfl | hs
    · rcases eq_empty_or_nonempty T with rfl | ht
      · exact hne rfl
      · have hp := hf T hTA ht
        have hz : f (∅ : Finset ℕ) = 0 := by simp [f]
        omega
    · rcases eq_empty_or_nonempty T with rfl | ht
      · have hp := hf S hSA hs
        have hz : f (∅ : Finset ℕ) = 0 := by simp [f]
        omega
      · apply hanti S hSA T hTA hs ht hne
        change f S ∣ f T
        rw [← heq]
  have hR : A.powerset.image f ⊆ range (A.card * n + 1) := by
    intro y hy
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hy
    have hSA := mem_powerset.mp hS
    have hb : f S ≤ S.card * n := by
      calc
        f S ≤ ∑ _a ∈ S, n := sum_le_sum fun a ha => (mem_Icc.mp (hA (hSA ha))).2
        _ = S.card * n := by simp [Nat.mul_comm]
    exact mem_range.mpr (Nat.lt_succ_of_le (hb.trans (Nat.mul_le_mul_right n (card_le_card hSA))))
  simpa [card_image_of_injOn hi] using card_le_card hR

private def wt (n : ℕ) : ℕ := n.bitIndices.length

private theorem wt_succ (n : ℕ) : wt (n + 1) ≤ wt n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · simp [wt]
    · have h := ih k (by omega)
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
      simp only [wt, Nat.bitIndices_two_mul, Nat.bitIndices_two_mul_add_one,
        List.length_map, List.length_cons] at *
      omega

private theorem wt_add (N : ℕ) : ∀ a b : ℕ, a + b = N → wt (a + b) ≤ wt a + wt b := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a b hab
    by_cases hz : N = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      simp [ha, hb, wt]
    rcases Nat.even_or_odd' a with ⟨x, rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' b with ⟨y, rfl | rfl⟩
    · have h := ih (x+y) (by omega) x y rfl
      rw [show 2*x + 2*y = 2*(x+y) by omega]
      simpa [wt] using h
    · have h := ih (x+y) (by omega) x y rfl
      rw [show 2*x + (2*y+1) = 2*(x+y)+1 by omega]
      simp [wt] at *
      omega
    · have h := ih (x+y) (by omega) x y rfl
      rw [show (2*x+1) + 2*y = 2*(x+y)+1 by omega]
      simp [wt] at *
      omega
    · have h := ih (x+y) (by omega) x y rfl
      have h' := wt_succ (x+y)
      rw [show (2*x+1) + (2*y+1) = 2*(x+y+1) by omega]
      simp [wt] at *
      omega

private theorem wt_mul_bound (k u : ℕ) : wt ((k+2)*u) ≤ (k+1)*wt u := by
  induction k with
  | zero => simp [wt]
  | succ k ih =>
    rw [show (k+1+2)*u = (k+2)*u+u by ring, show (k+1+1)*wt u = (k+1)*wt u+wt u by ring]
    exact (wt_add _ _ _ rfl).trans (Nat.add_le_add_right ih _)

private def lowBits (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2^i

private theorem lowBits_wt (S : Finset ℕ) : wt (lowBits S) = S.card := by
  unfold wt lowBits
  rw [← List.toFinset_card_of_nodup Nat.bitIndices_nodup, Finset.toFinset_bitIndices_sum_two_pow]

private theorem lowBits_inj : Function.Injective lowBits := by
  intro S T h
  have eqn := congrArg (fun n : ℕ => n.bitIndices.toFinset) h
  simpa only [lowBits, Finset.toFinset_bitIndices_sum_two_pow] using eqn

private theorem lowBits_lt {S : Finset ℕ} {m : ℕ} (h : S ⊆ range m) :
    lowBits S < 2^m := by
  exact Nat.geomSum_lt (m := 2) (by decide) (fun i hi => mem_range.mp (h hi))

private def base (m : ℕ) : ℕ := (m+1)*2^m
private def shift (m i : ℕ) : ℕ := base m + 2^i
private def total (m : ℕ) (S : Finset ℕ) : ℕ := ∑ i ∈ S, shift m i

private theorem total_eq (m : ℕ) (S : Finset ℕ) :
    total m S = S.card * base m + lowBits S := by
  simp [total, shift, lowBits, sum_add_distrib]

/-- A multiple can carry neither between the two blocks nor preserve the
number of occupied binary positions. Multiplicity one forces identical subsets. -/
private theorem indexed_antichain {m : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ range m) (hT : T ⊆ range m) (hs : S.Nonempty) (ht : T.Nonempty) (hne : S ≠ T) :
    ¬ total m S ∣ total m T := by
  rintro ⟨q,hq⟩
  have hspos : 0 < S.card := card_pos.mpr hs
  have hc : T.card ≤ m := by simpa using card_le_card hT
  have hp : 0 < 2^m := by positivity
  have hb : 0 < base m := by unfold base; positivity
  have h₂ : 2^m ≤ base m := by
    unfold base
    exact le_mul_of_one_le_left (Nat.zero_le _) (by omega)
  have hSlt := lowBits_lt hS
  have hTlt := lowBits_lt hT
  have hN : total m T < (m+1)*base m := by
    rw [total_eq, Nat.add_mul, Nat.one_mul]
    exact (Nat.add_lt_add_left (hTlt.trans_le h₂) _).trans_le
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _)
  have hJ : base m ≤ total m S := by
    rw [total_eq]
    have h := Nat.mul_le_mul_right (base m) (show 1 ≤ S.card by omega)
    simp only [Nat.one_mul] at h
    omega
  have hqm : q ≤ m := by
    have h := Nat.mul_le_mul_right q hJ
    rw [← hq] at h
    have hh := h.trans_lt hN
    rw [Nat.mul_comm (base m) q] at hh
    exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_right hb).mp hh)
  have hqr : lowBits S * q < base m := by
    unfold base
    have h := Nat.mul_le_mul (Nat.le_of_lt hSlt) hqm
    rw [Nat.mul_comm (2^m) m] at h
    exact h.trans_lt (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hp)
  have he : T.card * base m + lowBits T =
      (S.card*q) * base m + lowBits S*q := by
    rw [total_eq, total_eq] at hq
    rw [hq]
    ring
  have hbits : lowBits T = lowBits S*q := by
    have hh := congrArg (fun n : ℕ => n % base m) he
    simpa [Nat.mul_add_mod, Nat.add_mod, Nat.mod_eq_of_lt (hTlt.trans_le h₂), Nat.mod_eq_of_lt hqr] using hh
  have hcards : T.card = S.card*q := by
    rw [hbits, Nat.add_right_cancel_iff] at he
    exact Nat.eq_of_mul_eq_mul_right hb he
  have hqpos : 0 < q := by
    by_contra hn
    have hz : q = 0 := by omega
    have hh : total m T = 0 := by simpa [hz] using hq
    have := (show 0 < lowBits T by
      obtain ⟨i,hi⟩ := ht
      exact (Nat.pow_pos (by decide)).trans_le (single_le_sum (fun _ _ => Nat.zero_le _) hi))
    rw [total_eq] at hh
    omega
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h1 | hbig
  · have hz : q = 1 := h1.symm
    have := lowBits_inj (show lowBits T = lowBits S by simpa [hz] using hbits)
    exact hne this.symm
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, q = k+2 := ⟨q-2, by omega⟩
    have hh := wt_mul_bound k (lowBits S)
    have hwt : wt ((k+2)*lowBits S) = T.card := by
      rw [Nat.mul_comm, ← hk, ← hbits, lowBits_wt]
    rw [hwt, lowBits_wt] at hh
    rw [hk, Nat.mul_comm S.card (k+2), show (k+2)*S.card = (k+1)*S.card+S.card by ring] at hcards
    omega

private theorem lower_witness (m n : ℕ) (hn : (m+2)*2^m ≤ n) :
    m ≤ Erdos882.maxAntichainCard n := by
  classical
  let e : ℕ ↪ ℕ := ⟨shift m, fun i j h => Nat.pow_right_injective (by decide)
    (Nat.add_left_cancel h)⟩
  let A := (range m).map e
  have hA : A ⊆ Icc 1 n := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
    have him : i < m := mem_range.mp hi
    have hpow : 2^i ≤ 2^m := Nat.pow_le_pow_right (by decide) him.le
    have hpos : 0 < 2^i := by positivity
    apply mem_Icc.mpr
    constructor
    · change 1 ≤ base m + 2^i
      omega
    · change base m + 2^i ≤ n
      exact (Nat.add_le_add_left hpow _).trans (by
        rw [show base m + 2^m = (m+2)*2^m by unfold base; ring]
        exact hn)
  have hanti : Erdos882.IsSubsetSumAntichain A := by
    intro U hU V hV hu hv hne
    let S := (range m).filter fun i => e i ∈ U
    let T := (range m).filter fun i => e i ∈ V
    have hS : S ⊆ range m := filter_subset _ _
    have hT : T ⊆ range m := filter_subset _ _
    have hmap (W : Finset ℕ) (hW : W ⊆ A) :
        ((range m).filter fun i => e i ∈ W).map e = W := by
      ext w
      simp only [Finset.mem_map, mem_filter]
      constructor
      · rintro ⟨i, ⟨-, hi⟩, rfl⟩
        exact hi
      · intro hw
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (hW hw)
        exact ⟨i, ⟨hi, hw⟩, rfl⟩
    have hSU : S.map e = U := hmap U hU
    have hTV : T.map e = V := hmap V hV
    have hs : S.Nonempty := by
      rwa [← hSU, map_nonempty] at hu
    have ht : T.Nonempty := by
      rwa [← hTV, map_nonempty] at hv
    have hst : S ≠ T := by
      intro h
      apply hne
      rw [← hSU, ← hTV, h]
    rw [← hSU, ← hTV, sum_map, sum_map]
    exact indexed_antichain hS hT hs ht hst
  exact (show m = A.card by simp [A]).le.trans (card_le_max hA hanti)

end OMA

/-- The maximum subset-sum antichain size is asymptotic to the binary logarithm. -/
theorem OMA.solution : type_of% @Erdos882.erdos_882 := by
  let K := Erdos882.maxAntichainCard
  have hK : Tendsto K atTop atTop := by
    refine tendsto_atTop.2 (fun m => ?_)
    filter_upwards [eventually_ge_atTop ((m+2)*2^m)] with n hn
    exact OMA.lower_witness m n hn
  have hKr : Tendsto (fun n => (K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hK
  have hc : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have herr : Tendsto (fun n => (Real.log 4 + Real.log (K n : ℝ)) / (K n : ℝ))
      atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n => Real.log 4 / (K n : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log 4)).comp hK
    have h₂ := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hKr
    convert h₁.add h₂ using 1
    · ext n
      exact add_div _ _ _
    · simp
  have hone : Tendsto (fun n => Real.log 2 / (K n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).comp hK
  have hbounds : ∀ᶠ n : ℕ in atTop,
      Real.log 2 - (Real.log 4 + Real.log (K n : ℝ)) / (K n : ℝ) ≤
        Real.log (n : ℝ) / (K n : ℝ) ∧
      Real.log (n : ℝ) / (K n : ℝ) ≤
        Real.log 2 + (Real.log 4 + Real.log (K n : ℝ)) / (K n : ℝ) +
          Real.log 2 / (K n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), tendsto_atTop.1 hK 1] with n hn hk
    let k := K n
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by linarith
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlower : 2^k ≤ (k+1)*n := by
      have hcount : 2^k ≤ k*n+1 := OMA.count_upper n
      exact hcount.trans (by rw [Nat.add_mul, Nat.one_mul]; omega)
    have hupper : n < (k+3)*2^(k+1) := by
      by_contra! hh
      have hb := OMA.lower_witness (k+1) n (by simpa [Nat.add_assoc] using hh)
      change k+1 ≤ k at hb
      omega
    have h₁ : (2:ℝ)^k ≤ ((k:ℝ)+1)*n := by exact_mod_cast hlower
    have h₂ : (n:ℝ) ≤ ((k:ℝ)+3)*2^(k+1) := by exact_mod_cast hupper.le
    have hlog1 := Real.log_le_log (by positivity) h₁
    have hlog2 := Real.log_le_log hnR h₂
    rw [Real.log_pow, Real.log_mul (by positivity) hnR.ne'] at hlog1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Nat.cast_add,
      Nat.cast_one] at hlog2
    have hcorr : Real.log ((k:ℝ)+3) ≤ Real.log 4 + Real.log (k:ℝ) := by
      rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hkpos.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    have hcorr' : Real.log ((k:ℝ)+1) ≤ Real.log 4 + Real.log (k:ℝ) :=
      (Real.log_le_log (by positivity) (by linarith : (k:ℝ)+1 ≤ (k:ℝ)+3)).trans hcorr
    constructor
    · change Real.log 2 - (Real.log 4 + Real.log (k:ℝ)) / (k:ℝ) ≤ _
      apply (le_div_iff₀ hkpos).2
      rw [sub_mul, div_mul_cancel₀ _ hkpos.ne']
      linarith
    · change Real.log (n:ℝ) / (k:ℝ) ≤ _
      apply (div_le_iff₀ hkpos).2
      rw [add_mul, add_mul, div_mul_cancel₀ _ hkpos.ne', div_mul_cancel₀ _ hkpos.ne']
      linarith
  have hlim : Tendsto (fun n : ℕ => Real.log (n:ℝ) / (K n:ℝ)) atTop (𝓝 (Real.log 2)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
    · simpa only [sub_zero] using tendsto_const_nhds.sub herr
    · simpa only [add_zero] using (tendsto_const_nhds.add herr).add hone
  have ht : Tendsto (fun n : ℕ => Real.log 2 / (Real.log (n:ℝ) / (K n:ℝ))) atTop (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2)) :=
      tendsto_const_nhds
    simpa only [Pi.div_def, div_self hc.ne'] using hconst.div hlim hc.ne'
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ), tendsto_atTop.1 hK 1] with n hn hk
  change Real.log 2 / (Real.log (n:ℝ) / (K n:ℝ)) = (K n:ℝ) / Real.logb 2 (n:ℝ)
  rw [Real.logb]
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hkR : (K n : ℝ) ≠ 0 := by exact_mod_cast (show K n ≠ 0 by omega)
  field_simp

