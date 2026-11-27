import OMAReductions.R_RegularPrimes_not_isRegularPrime_37_R1

/-! Certify the first 33 Bernoulli numbers against their defining recurrence. -/

namespace OMA.BernoulliTable

def entry (n : ℕ) : ℚ :=
  ([1, 1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0, -691/2730, 0, 7/6, 0, -3617/510, 0, 43867/798, 0, -174611/330, 0, 854513/138, 0, -236364091/2730, 0, 8553103/6, 0, -23749461029/870, 0, 8615841276005/14322, 0, -7709321041217/510] : List ℚ)[n]?.getD 0

set_option maxRecDepth 10000 in
private lemma recurrence : ∀ i : Fin 33, entry i = 1 -
    ∑ k ∈ Finset.range i.val, i.val.choose k / (i.val - k + 1) * entry k := by
  decide +kernel

lemma correct (n : ℕ) (hn : n < 33) : bernoulli' n = entry n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [bernoulli'_def, recurrence ⟨n, hn⟩]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih k (Finset.mem_range.mp hk) ((Finset.mem_range.mp hk).trans hn)]

end OMA.BernoulliTable

theorem OMA.solution : OMA.R_RegularPrimes_not_isRegularPrime_37_R1.H1 := by
  change (37 : ℤ) ∣ (bernoulli' 32).num
  rw [OMA.BernoulliTable.correct 32 (by decide)]
  exact ⟨-208360028141, by decide +kernel⟩
