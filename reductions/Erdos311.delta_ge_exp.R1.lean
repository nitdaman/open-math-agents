import FormalConjectures.ErdosProblems.«311»

-- Reduction Erdos311.delta_ge_exp.R1 of Erdős Problem 311 — delta ge exp
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Where the exponential lower bound for `δ` comes from

`δ N` is the least nonzero value of `|1 - ∑_{n ∈ A} 1/n|` over `A ⊆ {1, …, N}`.  Two inputs give
the bound `δ N ≥ e^{-(1+o(1)) N}`.

* `H2` is the trivial arithmetic bound: such a difference is a nonzero rational whose denominator
  divides `[1, …, N]`, so it is at least `1 / [1, …, N]`.  (This is the statement
  `Erdos311.delta_ge_inv_lcm` of the same file.)
* `H1` is the prime number theorem in Chebyshev's form: `ψ N / N → 1`, where `ψ N = log [1, …, N]`
  (`Chebyshev.psi_eq_log_lcmUpto`).

The content of the reduction is the translation between them: `1 / [1, …, N] = e^{-ψ N}`, and
`ψ N ≤ (1 + ε) N` eventually, so `e^{-(1+ε)N} ≤ 1 / [1, …, N] ≤ δ N` eventually.  Nothing about
`δ` itself is unfolded: only the two inputs are used.
-/

namespace OMA.R_Erdos311_delta_ge_exp_R1

open Filter Topology

/-- The prime number theorem in the form `ψ N / N → 1`, where `ψ` is Chebyshev's function. -/
def H1 : Prop :=
  Tendsto (fun N : ℕ => Chebyshev.psi (N : ℝ) / (N : ℝ)) atTop (nhds 1)

/-- The trivial bound: every nonzero value of `1 - ∑_{n ∈ A} 1/n` has denominator dividing
`[1, …, N]`, hence is at least `1 / [1, …, N]` in absolute value. -/
def H2 : Prop :=
  ∀ N : ℕ, 1 / ((Nat.lcmUpto N : ℝ)) ≤ Erdos311.delta N

theorem main : H1 → H2 → type_of% @Erdos311.delta_ge_exp := by
  intro h1 h2 ε hε
  -- `ψ N / N < 1 + ε` eventually
  have hev : ∀ᶠ N : ℕ in atTop, Chebyshev.psi (N : ℝ) / (N : ℝ) < 1 + ε :=
    h1.eventually (Iio_mem_nhds (by linarith : (1 : ℝ) < 1 + ε))
  filter_upwards [hev, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hψ : Chebyshev.psi (N : ℝ) < (1 + ε) * N := by
    have h := (div_lt_iff₀ hNpos).1 hN
    linarith
  have hexp : Real.exp (-(1 + ε) * N) ≤ Real.exp (-(Chebyshev.psi (N : ℝ))) := by
    refine Real.exp_le_exp.2 ?_
    linarith
  have hlcm : Real.exp (-(Chebyshev.psi (N : ℝ))) = 1 / (Nat.lcmUpto N : ℝ) := by
    rw [Chebyshev.psi_eq_log_lcmUpto, Real.exp_neg, Real.exp_log]
    · rw [one_div]
    · exact_mod_cast Nat.lcmUpto_pos N
  calc Real.exp (-(1 + ε) * N)
      ≤ Real.exp (-(Chebyshev.psi (N : ℝ))) := hexp
    _ = 1 / (Nat.lcmUpto N : ℝ) := hlcm
    _ ≤ Erdos311.delta N := h2 N

end OMA.R_Erdos311_delta_ge_exp_R1
