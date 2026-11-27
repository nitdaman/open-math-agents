import OMAReductions.R_RiemannZetaValues_apery_central_binomial_series_R1

/-! # Triangular telescoping for Apéry’s series
Based on the WZ pair in T. Amdeberhan, Faster and Faster Convergent Series for ζ(3), case s = 1. -/
-- Credit: @steveDOTdigital

open Finset
namespace OMA.AperyFinite
private noncomputable def F (n k : ℕ) : ℂ := (-1 : ℂ)^k * (k.factorial : ℂ)^2 * ((n-k-1).factorial : ℂ) /
  (((n+k+1).factorial : ℂ) * (k+1))
private noncomputable def G (n k : ℕ) : ℂ := 2 * (-1 : ℂ)^k * (k.factorial : ℂ)^2 * ((n-k).factorial : ℂ) /
  (((n+k+1).factorial : ℂ) * (n+1)^2)
private theorem step {n k : ℕ} (h : k < n) :
    F (n+1) k - F n k = G n (k+1) - G n k := by
  have hd : (n-k).factorial = (n-k)*(n-k-1).factorial := by
    conv_lhs => rw [show n-k = (n-k-1)+1 by omega, Nat.factorial_succ]
    congr 1 <;> omega
  have hf : ((n+k+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hk : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hnk : (n : ℂ)+k+1+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+k+1)
  simp only [F,G,show n+1-k-1=n-k by omega,show n-(k+1)=n-k-1 by omega,
    show n+1+k+1=(n+k+1)+1 by omega,show n+(k+1)+1=(n+k+1)+1 by omega,
    Nat.factorial_succ (n+k+1), Nat.factorial_succ k, hd, pow_succ (-1 : ℂ) k]
  push_cast [Nat.cast_sub h.le]
  field_simp
  ring
private theorem g0 (n : ℕ) : G n 0 = 2 / ((n : ℂ)+1)^3 := by
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have ht : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [G,Nat.factorial_succ]
  field_simp [hf,ht]
  <;> ring
private theorem diag (n : ℕ) : G n n + F (n+1) n =
    5 * ((-1 : ℂ)^n / (((n : ℂ)+1)^3 * Nat.centralBinom (n+1))) := by
  have fact : (Nat.centralBinom (n+1) : ℂ) * ((n+1).factorial : ℂ) * (n+1).factorial =
      ((2*(n+1)).factorial : ℂ) := by
    exact_mod_cast (show Nat.centralBinom (n+1) * (n+1).factorial * (n+1).factorial =
      (2*(n+1)).factorial by simpa [Nat.centralBinom, two_mul] using Nat.add_choose_mul_factorial_mul_factorial (n+1) (n+1))
  rw [show 2*(n+1)=(n+n+1)+1 by omega,Nat.factorial_succ (n+n+1),Nat.factorial_succ n] at fact
  push_cast at fact
  have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hbin : (Nat.centralBinom (n+1) : ℂ) ≠ 0 := by exact_mod_cast (Nat.centralBinom_pos (n+1)).ne'
  have hf : ((n+n+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (n : ℂ)+n+1+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+n+1)
  simp only [F,G,Nat.sub_self,show n+1-n-1=0 by omega,Nat.factorial_zero,Nat.cast_one,mul_one,
    show n+1+n+1=(n+n+1)+1 by omega,Nat.factorial_succ (n+n+1)]
  push_cast
  rw [show (n : ℂ)+n+1+1 = 2*((n : ℂ)+1) by ring] at fact ⊢
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have eqb : ((n+n+1).factorial : ℂ) =
      ((n+1).centralBinom : ℂ) * ((n : ℂ)+1) * (n.factorial : ℂ)^2 / 2 := by
    apply mul_left_cancel₀ hn
    linear_combination (-1/2 : ℂ) * fact
  rw [eqb]
  field_simp [hn,hbin,hfac]
  <;> ring
theorem triangle : OMA.R_RiemannZetaValues_apery_central_binomial_series_R1.H1 := by
  intro N
  change (∑ n ∈ range N, 1 / ((n : ℂ)+1)^3) = (5/2 : ℂ) *
    (∑ n ∈ range N, (-1 : ℂ)^n / (((n : ℂ)+1)^3 * Nat.centralBinom (n+1))) -
      (1/2 : ℂ) * ∑ k ∈ range N, F N k
  induction N with
  | zero => simp
  | succ N ih =>
    have telescope : (∑ k ∈ range N, (F (N+1) k - F N k)) = G N N - G N 0 := calc
      _ = ∑ k ∈ range N, (G N (k+1) - G N k) := Finset.sum_congr rfl (fun k hk => step (mem_range.mp hk))
      _ = _ := Finset.sum_range_sub (G N) N
    rw [Finset.sum_sub_distrib] at telescope
    simp only [Finset.sum_range_succ]
    linear_combination ih + (1/2 : ℂ)*telescope + (1/2 : ℂ)*diag N - (1/2 : ℂ)*g0 N
end OMA.AperyFinite

theorem OMA.solution : OMA.R_RiemannZetaValues_apery_central_binomial_series_R1.H1 := OMA.AperyFinite.triangle
