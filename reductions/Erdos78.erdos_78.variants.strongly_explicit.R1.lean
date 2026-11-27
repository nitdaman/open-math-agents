import FormalConjectures.ErdosProblems.«78»
-- Reduction Erdos78.erdos_78.variants.strongly_explicit.R1
-- Credit: @adammcarter
-- H1 (open core): the same statement, but only for graph sizes that are powers of two.
-- H2 (engineering): feeding one poly-time map into another stays poly-time (for these types).
-- H3 (engineering): rounding the vertex count up to the next power of two is poly-time.
-- main: H1, H2 and H3 together give the full strongly explicit statement. A graph on n vertices
-- is read off as the first n vertices of the graph on the next power of two above n.
namespace OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1
open Filter Real ComplexityTheory Erdos78

-- H1 (OPEN core): the target restricted to graph sizes that are powers of two.
def H1 : Prop := ∃ c > (0 : ℝ), ∃ adj : ℕ × ℕ × ℕ → Bool, IsPolyTime adj ∧
  ∀ᶠ k : ℕ in atTop, NoHomogeneousSet (stronglyExplicitGraph adj (2 ^ k)) ⌈c * k⌉₊
-- H2 (true, engineering): composition of poly-time maps, for these types.
def H2 : Prop := ∀ (f : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (g : ℕ × ℕ × ℕ → Bool),
  IsPolyTime f → IsPolyTime g → IsPolyTime (g ∘ f)
-- H3 (true, engineering): padding the vertex count up to the next power of two is poly-time.
def H3 : Prop := IsPolyTime (fun x : ℕ × ℕ × ℕ => ((2 : ℕ) ^ Nat.size x.1, x.2))

/-- The graph for n with the padded oracle embeds into the graph for a larger size N. -/
theorem padEmb (adj : ℕ × ℕ × ℕ → Bool) (n N : ℕ) (h : n ≤ N) :
    Nonempty (SimpleGraph.Embedding
      (SimpleGraph.fromRel fun u v : Fin n => adj (N, (u : ℕ), (v : ℕ)))
      (stronglyExplicitGraph adj N)) :=
  ⟨{ toEmbedding := Fin.castLEEmb h
     map_rel_iff' := by
       intro a b
       simp [stronglyExplicitGraph, SimpleGraph.fromRel_adj, Fin.ext_iff] }⟩

theorem noHom_transfer (adj : ℕ × ℕ × ℕ → Bool) (n N m : ℕ) (h : n ≤ N)
    (H : NoHomogeneousSet (stronglyExplicitGraph adj N) m) :
    NoHomogeneousSet
      (SimpleGraph.fromRel fun u v : Fin n => adj (N, (u : ℕ), (v : ℕ))) m := by
  obtain ⟨h1, h2⟩ := H
  obtain ⟨e⟩ := padEmb adj n N h
  exact ⟨h1.comap ⟨e.toCopy⟩, h2.comap ⟨(SimpleGraph.Embedding.complEquiv e).toCopy⟩⟩

theorem size_le_log (n : ℕ) (hn : 2 ≤ n) :
    (Nat.size n : ℝ) ≤ 2 * Real.log n / Real.log 2 := by
  have hs : 0 < Nat.size n := Nat.size_pos.2 (by omega)
  have hp : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 (by omega)
  have hpR : (2 : ℝ) ^ (Nat.size n - 1) ≤ (n : ℝ) := by exact_mod_cast hp
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : ((Nat.size n - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpR
  have hn2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hcast : ((Nat.size n - 1 : ℕ) : ℝ) = (Nat.size n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at hlog
  rw [le_div_iff₀ hl2]
  nlinarith

theorem main : H1 → H2 → H3 → type_of% @Erdos78.erdos_78.variants.strongly_explicit := by
  rintro ⟨c, hc, adj, hadj, hev⟩ h2 h3
  set pad : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun x => ((2 : ℕ) ^ Nat.size x.1, x.2) with hpad
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * c / Real.log 2, by positivity, adj ∘ pad, h2 pad adj h3 hadj, ?_⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨max 2 (2 ^ K), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hsK : K ≤ Nat.size n := by
    have : K < Nat.size n + 1 := by
      rw [Nat.lt_succ_iff]
      exact (Nat.lt_size.2 (le_trans (le_max_right _ _) hn)).le
    omega
  have hbig := hK _ hsK
  have hsub := noHom_transfer adj n (2 ^ Nat.size n) ⌈c * (Nat.size n : ℕ)⌉₊
    (Nat.lt_size_self n).le hbig
  have hgr : stronglyExplicitGraph (adj ∘ pad) n =
      SimpleGraph.fromRel fun u v : Fin n => adj (2 ^ Nat.size n, (u : ℕ), (v : ℕ)) := by
    simp [stronglyExplicitGraph, hpad]
  have hm : ⌈c * (Nat.size n : ℝ)⌉₊ ≤ ⌈2 * c / Real.log 2 * Real.log n⌉₊ := by
    apply Nat.ceil_mono
    have := size_le_log n hn2
    calc c * (Nat.size n : ℝ) ≤ c * (2 * Real.log n / Real.log 2) :=
          mul_le_mul_of_nonneg_left this hc.le
      _ = 2 * c / Real.log 2 * Real.log n := by ring
  rw [hgr]
  exact ⟨hsub.1.mono hm, hsub.2.mono hm⟩

end OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1
