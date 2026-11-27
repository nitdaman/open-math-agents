import FormalConjectures.Wikipedia.HedetniemiConjecture
import Mathlib

/-!
# El-Zahar--Sauer: K_3 is multiplicative (the n = 3 core)

Route: Wrochna, Square-free graphs are multiplicative (arXiv 1601.04551), Section 4,
specialised to K_3. The fundamental-groupoid language of that paper is replaced by one integer
invariant: the sum of signed steps of a sequence of colours in Z/3 (wind below).

Everything combinatorial is stated for sequences indexed by the natural numbers; a closed walk
of odd length is a periodic sequence (IsOddCyc). Blueprint: work/BLUEPRINT-ElZaharSauer.md.
-/

open SimpleGraph HedetniemiConjecture

namespace ElZS

/- ## Part 0: foundations (core_ prefix; to be deduplicated against Small.lean) -/

/-- A closed walk of odd length m, written as an m-periodic sequence of vertices. -/
def IsOddCyc {V : Type*} (G : SimpleGraph V) (c : ℕ → V) (m : ℕ) : Prop :=
  Odd m ∧ (∀ i, G.Adj (c i) (c (i + 1))) ∧ ∀ i, c (i + m) = c i

/-- F1. A graph that is not 2-colourable has an odd closed walk (as a periodic sequence). -/
theorem core_exists_oddCyc {V : Type*} {G : SimpleGraph V} (h : ¬ G.Colorable 2) :
    ∃ (c : ℕ → V) (m : ℕ), IsOddCyc G c m := by
  by_contra hno
  apply h
  rw [two_colorable_iff_forall_loop_even]
  intro u w
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  apply hno
  have hpos : 0 < w.length := hodd.pos
  refine ⟨fun i => w.getVert (i % w.length), w.length, hodd, fun i => ?_, fun i => ?_⟩
  · have hlt : i % w.length < w.length := Nat.mod_lt _ hpos
    have key : w.getVert ((i + 1) % w.length) = w.getVert (i % w.length + 1) := by
      rw [← Nat.mod_add_mod i w.length 1]
      rcases Nat.lt_or_ge (i % w.length + 1) w.length with h1 | h1
      · rw [Nat.mod_eq_of_lt h1]
      · have h2 : i % w.length + 1 = w.length := by omega
        rw [h2, Nat.mod_self, Walk.getVert_zero, Walk.getVert_length]
    show G.Adj (w.getVert (i % w.length)) (w.getVert ((i + 1) % w.length))
    rw [key]
    exact w.adj_getVert_succ hlt
  · show w.getVert ((i + w.length) % w.length) = w.getVert (i % w.length)
    rw [Nat.add_mod_right]

/-- F2. A periodic sequence is periodic with every multiple of its period. -/
theorem periodic_mul {X : Type*} (k : ℕ → X) (N : ℕ) (hk : ∀ t, k (t + N) = k t) (r t : ℕ) :
    k (t + N * r) = k t := by
  induction r with
  | zero => simp
  | succ r ih => rw [Nat.mul_succ, ← add_assoc, hk, ih]

/- ## Part 1: signed steps in Z/3 -/

/-- The signed lift of an element of Z/3 to -1, 0, 1. -/
def sg (x : Fin 3) : ℤ := if x = 0 then 0 else if x = 1 then 1 else -1

/-- S1. -/
theorem sg_neg (a b : Fin 3) : sg (a - b) = - sg (b - a) := by
  revert a b; decide

/-- S2. A proper step is plus or minus one. -/
theorem sg_eq_one_or (a b : Fin 3) (h : a ≠ b) : sg (b - a) = 1 ∨ sg (b - a) = -1 := by
  revert a b; decide

/-- S3. Two proper steps a, b, c only depend on a and c. -/
theorem sg_two_step (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) :
    sg (b - a) + sg (c - b) = -2 * sg (c - a) := by
  revert a b c; decide

/-- S4. Signed steps add up inside a set of at most two colours. -/
theorem sg_add_of_avoid (a b c e : Fin 3) (ha : e ≠ a) (hb : e ≠ b) (hc : e ≠ c) :
    sg (c - a) = sg (b - a) + sg (c - b) := by
  revert a b c e; decide

/-- S5. -/
theorem sg_cross (u v u' v' : Fin 3) (h1 : u ≠ v) (h2 : u' ≠ v') (h3 : u ≠ u') (h4 : v ≠ v') :
    sg (v' - u') - sg (v - u) = sg (v' - v) - sg (u' - u) := by
  revert u v u' v'; decide

/- ## Part 2: the winding sum of a sequence of colours -/

/-- Sum of the signed steps of the first N steps of a sequence of colours. -/
def wind (k : ℕ → Fin 3) (N : ℕ) : ℤ := ∑ i ∈ Finset.range N, sg (k (i + 1) - k i)

theorem wind_zero (k : ℕ → Fin 3) : wind k 0 = 0 := by
  simp [wind]

theorem wind_succ (k : ℕ → Fin 3) (N : ℕ) :
    wind k (N + 1) = wind k N + sg (k (N + 1) - k N) := by
  simp [wind, Finset.sum_range_succ]

/-- W1. Splitting. -/
theorem wind_add (k : ℕ → Fin 3) (a b : ℕ) :
    wind k (a + b) = wind k a + wind (fun t => k (t + a)) b := by
  induction b with
  | zero => simp [wind_zero]
  | succ b ih =>
    rw [← add_assoc, wind_succ, wind_succ, ih]
    have e1 : a + b + 1 = b + 1 + a := by omega
    have e2 : a + b = b + a := by omega
    show wind k a + wind (fun t => k (t + a)) b + sg (k (a + b + 1) - k (a + b))
      = wind k a + (wind (fun t => k (t + a)) b + sg (k (b + 1 + a) - k (b + a)))
    rw [e1, e2]
    ring

/-- W2. Going r times round a period. -/
theorem wind_periodic_mul (k : ℕ → Fin 3) (N : ℕ) (hk : ∀ t, k (t + N) = k t) (r : ℕ) :
    wind k (N * r) = r * wind k N := by
  induction r with
  | zero => simp [wind_zero]
  | succ r ih =>
    rw [Nat.mul_succ, wind_add, ih]
    have e : (fun t => k (t + N * r)) = k := funext fun t => periodic_mul k N hk r t
    rw [e]
    push_cast
    ring

/-- W3. For a proper sequence, the winding sum is minus twice that of the even positions. -/
theorem wind_two_step (k : ℕ → Fin 3) (hk : ∀ t, k (t + 1) ≠ k t) (N : ℕ) :
    wind k (2 * N) = -2 * wind (fun i => k (2 * i)) N := by
  induction N with
  | zero => simp [wind_zero]
  | succ N ih =>
    have e : 2 * (N + 1) = 2 * N + 1 + 1 := by ring
    have h := sg_two_step (k (2 * N)) (k (2 * N + 1)) (k (2 * N + 1 + 1)) (hk _).symm (hk _).symm
    have hs : wind (fun i => k (2 * i)) (N + 1)
        = wind (fun i => k (2 * i)) N + sg (k (2 * N + 1 + 1) - k (2 * N)) := by
      rw [wind_succ, e]
    rw [e, wind_succ, wind_succ, ih, hs]
    linarith

/-- W4. For a proper sequence, the winding sum has the parity of the number of steps. -/
theorem wind_mod_two (k : ℕ → Fin 3) (hk : ∀ t, k (t + 1) ≠ k t) (N : ℕ) :
    wind k N % 2 = (N : ℤ) % 2 := by
  induction N with
  | zero => simp [wind_zero]
  | succ N ih =>
    rw [wind_succ]
    rcases sg_eq_one_or (k N) (k (N + 1)) (hk N).symm with h | h <;> rw [h] <;> push_cast <;> omega

/- ## Part 3: the grid identity -/

/-- G1. Moving a column of the grid one step to the right. -/
theorem wind_col_transfer (M : ℕ → ℕ → Fin 3)
    (hsq : ∀ i j, ∃ e, e ≠ M i j ∧ e ≠ M (i + 1) j ∧ e ≠ M i (j + 1) ∧ e ≠ M (i + 1) (j + 1))
    (i j : ℕ) :
    wind (fun t => M i t) j + sg (M (i + 1) j - M i j)
      = sg (M (i + 1) 0 - M i 0) + wind (fun t => M (i + 1) t) j := by
  induction j with
  | zero => simp [wind_zero]
  | succ j ih =>
    obtain ⟨e, h1, h2, h3, h4⟩ := hsq i j
    have a1 := sg_add_of_avoid (M i j) (M i (j + 1)) (M (i + 1) (j + 1)) e h1 h3 h4
    have a2 := sg_add_of_avoid (M i j) (M (i + 1) j) (M (i + 1) (j + 1)) e h1 h2 h4
    rw [wind_succ, wind_succ]
    show wind (fun t => M i t) j + sg (M i (j + 1) - M i j) + sg (M (i + 1) (j + 1) - M i (j + 1))
      = sg (M (i + 1) 0 - M i 0)
        + (wind (fun t => M (i + 1) t) j + sg (M (i + 1) (j + 1) - M (i + 1) j))
    linarith

/-- G2. The grid identity: if every unit square of a grid of colours misses a colour, the
winding sum along the diagonal equals bottom row plus last column. -/
theorem wind_diag (M : ℕ → ℕ → Fin 3)
    (hsq : ∀ i j, ∃ e, e ≠ M i j ∧ e ≠ M (i + 1) j ∧ e ≠ M i (j + 1) ∧ e ≠ M (i + 1) (j + 1))
    (L : ℕ) :
    wind (fun t => M t t) L = wind (fun t => M t 0) L + wind (fun t => M L t) L := by
  induction L with
  | zero => simp [wind_zero]
  | succ L ih =>
    obtain ⟨e, h1, h2, h3, h4⟩ := hsq L L
    have a2 := sg_add_of_avoid (M L L) (M (L + 1) L) (M (L + 1) (L + 1)) e h1 h2 h4
    have tr := wind_col_transfer M hsq L L
    rw [wind_succ, wind_succ, wind_succ, ih]
    show wind (fun t => M t 0) L + wind (fun t => M L t) L + sg (M (L + 1) (L + 1) - M L L)
      = wind (fun t => M t 0) L + sg (M (L + 1) 0 - M L 0)
        + (wind (fun t => M (L + 1) t) L + sg (M (L + 1) (L + 1) - M (L + 1) L))
    linarith

/- ## Part 4: two facts about closed proper sequences of even length 2m -/

/-- A1 (antipodal fixed point, K_3 case of the fixpoint lemma in Wrochna Section 4). A proper sequence of period 2m,
m odd, in which no position has the same colour as its antipode, has even half-winding. -/
theorem wind_even_of_no_antipode (u : ℕ → Fin 3) (m : ℕ) (hm : Odd m)
    (hstep : ∀ t, u (t + 1) ≠ u t) (hper : ∀ t, u (t + 2 * m) = u t)
    (hanti : ∀ t, u (t + m) ≠ u t) : Even (wind (fun i => u (2 * i)) m) := by
  have tel : ∀ N, sg (u (N + m) - u N) - sg (u (0 + m) - u 0)
      = wind (fun t => u (t + m)) N - wind u N := by
    intro N
    induction N with
    | zero => simp [wind_zero]
    | succ N ih =>
      have h4 : u (N + m) ≠ u (N + 1 + m) := by
        have h := hstep (N + m)
        rw [show N + m + 1 = N + 1 + m by omega] at h
        exact h.symm
      have c := sg_cross (u N) (u (N + m)) (u (N + 1)) (u (N + 1 + m)) (hanti N).symm
        (hanti (N + 1)).symm (hstep N).symm h4
      rw [wind_succ, wind_succ]
      show sg (u (N + 1 + m) - u (N + 1)) - sg (u (0 + m) - u 0)
        = wind (fun t => u (t + m)) N + sg (u (N + 1 + m) - u (N + m))
          - (wind u N + sg (u (N + 1) - u N))
      linarith
  have h1 := tel m
  have hsplit := wind_add u m m
  have h2 := wind_two_step u hstep m
  have hpar := wind_mod_two u hstep m
  have e0 := sg_eq_one_or (u 0) (u (0 + m)) (hanti 0).symm
  have em : sg (u (m + m) - u m) = - sg (u (0 + m) - u 0) := by
    have h := hper 0
    rw [zero_add, two_mul] at h
    rw [h, zero_add]
    exact sg_neg _ _
  have hmm : 2 * m = m + m := two_mul m
  rw [hmm] at h2
  obtain ⟨r, hr⟩ := hm
  rw [Int.even_iff]
  rcases e0 with e | e <;> omega

/-- A2. Shifting a proper sequence of period 2n by n does not change the half-winding. -/
theorem wind_double_shift (x : ℕ → Fin 3) (n : ℕ) (hstep : ∀ t, x (t + 1) ≠ x t)
    (hper : ∀ t, x (t + 2 * n) = x t) :
    wind (fun j => x (2 * j)) n = wind (fun j => x (2 * j + n)) n := by
  have hn : 2 * n = n + n := two_mul n
  have h1 := wind_two_step x hstep n
  have hy : ∀ t, (fun t => x (t + n)) (t + 1) ≠ (fun t => x (t + n)) t := by
    intro t
    show x (t + 1 + n) ≠ x (t + n)
    have h := hstep (t + n)
    rw [show t + n + 1 = t + 1 + n by omega] at h
    exact h
  have h2 : wind (fun t => x (t + n)) (2 * n) = -2 * wind (fun j => x (2 * j + n)) n :=
    wind_two_step (fun t => x (t + n)) hy n
  have s1 := wind_add x n n
  have s2 := wind_add (fun t => x (t + n)) n n
  have e : (fun t => (fun t => x (t + n)) (t + n)) = x := by
    funext t
    show x (t + n + n) = x t
    rw [add_assoc, ← two_mul]
    exact hper t
  rw [e] at s2
  rw [hn] at h1 h2
  linarith

/- ## Part 5: colourings of a product -/

section Product

variable {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {μ : α → β → Fin 3}

/-- A proper 3-colouring of the tensor product, in curried form. -/
def Proper (G : SimpleGraph α) (H : SimpleGraph β) (μ : α → β → Fin 3) : Prop :=
  ∀ g g' h h', G.Adj g g' → H.Adj h h' → μ g h ≠ μ g' h'

theorem Proper.swap (hμ : Proper G H μ) : Proper H G (fun h g => μ g h) :=
  fun h h' g g' hh hg => hμ g g' h h' hg hh

/-- The half-winding of the closed walk c (period m) of G at the vertex h of H. -/
def hw (μ : α → β → Fin 3) (c : ℕ → α) (m : ℕ) (h : β) : ℤ :=
  wind (fun i => μ (c (2 * i)) h) m

/-- The colours along c, read alternately in the rows h and h'. -/
def altSeq (μ : α → β → Fin 3) (c : ℕ → α) (h h' : β) : ℕ → Fin 3 :=
  fun t => μ (c t) (if t % 2 = 0 then h else h')

theorem altSeq_step (hμ : Proper G H μ) {c : ℕ → α} (hadj : ∀ i, G.Adj (c i) (c (i + 1)))
    {h h' : β} (hh : H.Adj h h') (t : ℕ) : altSeq μ c h h' (t + 1) ≠ altSeq μ c h h' t := by
  show μ (c (t + 1)) (if (t + 1) % 2 = 0 then h else h') ≠ μ (c t) (if t % 2 = 0 then h else h')
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · have ht' : ¬ (t + 1) % 2 = 0 := by omega
    rw [if_pos ht, if_neg ht']
    exact (hμ _ _ _ _ (hadj t) hh).symm
  · have ht' : (t + 1) % 2 = 0 := by omega
    have ht'' : ¬ t % 2 = 0 := by omega
    rw [if_pos ht', if_neg ht'']
    exact (hμ _ _ _ _ (hadj t) hh.symm).symm

theorem altSeq_per {c : ℕ → α} {m : ℕ} (hper : ∀ i, c (i + m) = c i) (h h' : β) (t : ℕ) :
    altSeq μ c h h' (t + 2 * m) = altSeq μ c h h' t := by
  show μ (c (t + 2 * m)) (if (t + 2 * m) % 2 = 0 then h else h')
    = μ (c t) (if t % 2 = 0 then h else h')
  have e1 : c (t + 2 * m) = c t := by rw [two_mul, ← add_assoc, hper, hper]
  have e2 : (t + 2 * m) % 2 = t % 2 := by omega
  rw [e1, e2]

theorem altSeq_even (c : ℕ → α) (h h' : β) (j : ℕ) :
    altSeq μ c h h' (2 * j) = μ (c (2 * j)) h := by
  show μ (c (2 * j)) (if (2 * j) % 2 = 0 then h else h') = μ (c (2 * j)) h
  have e : (2 * j) % 2 = 0 := by omega
  rw [if_pos e]

theorem altSeq_shift {c : ℕ → α} {m : ℕ} (hm : Odd m) (hper : ∀ i, c (i + m) = c i)
    (h h' : β) (t : ℕ) : altSeq μ c h h' (t + m) = altSeq μ c h' h t := by
  show μ (c (t + m)) (if (t + m) % 2 = 0 then h else h')
    = μ (c t) (if t % 2 = 0 then h' else h)
  obtain ⟨r, hr⟩ := hm
  rw [hper]
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · have ht' : ¬ (t + m) % 2 = 0 := by omega
    rw [if_pos ht, if_neg ht']
  · have ht' : (t + m) % 2 = 0 := by omega
    have ht'' : ¬ t % 2 = 0 := by omega
    rw [if_pos ht', if_neg ht'']

/-- P1. The half-winding of a closed odd walk of G does not change along an edge of H. -/
theorem hw_adj (hμ : Proper G H μ) {c : ℕ → α} {m : ℕ} (hc : IsOddCyc G c m) {h h' : β}
    (hh : H.Adj h h') : hw μ c m h = hw μ c m h' := by
  obtain ⟨hm, hadj, hper⟩ := hc
  have key := wind_double_shift (altSeq μ c h h') m (altSeq_step hμ hadj hh)
    (altSeq_per hper h h')
  have eL : (fun j => altSeq μ c h h' (2 * j)) = fun i => μ (c (2 * i)) h :=
    funext fun j => altSeq_even c h h' j
  have eR : (fun j => altSeq μ c h h' (2 * j + m)) = fun i => μ (c (2 * i)) h' :=
    funext fun j => by rw [altSeq_shift hm hper, altSeq_even]
  rw [eL, eR] at key
  exact key

/-- P2. Hence it is the same at any two vertices of H joined by a walk. -/
theorem hw_reachable (hμ : Proper G H μ) {c : ℕ → α} {m : ℕ} (hc : IsOddCyc G c m) {h h' : β}
    (hh : H.Reachable h h') : hw μ c m h = hw μ c m h' := by
  obtain ⟨p⟩ := hh
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hw_adj hμ hc hadj).trans ih

/-- P3 (parity switch, K_3 case of the paritySwitch lemma in Wrochna Section 4). For odd closed walks c of G and d of H,
exactly one of the two half-windings is odd. -/
theorem parity_switch (hμ : Proper G H μ) {c : ℕ → α} {m : ℕ} (hc : IsOddCyc G c m)
    {d : ℕ → β} {n : ℕ} (hd : IsOddCyc H d n) :
    Odd (hw μ c m (d 0) + hw (fun h g => μ g h) d n (c 0)) := by
  obtain ⟨hm, hcadj, hcper⟩ := hc
  obtain ⟨hn, hdadj, hdper⟩ := hd
  have e2 : ∀ i, 2 * (i + 1) = 2 * i + 1 + 1 := fun i => by ring
  have hsq : ∀ i j, ∃ e, e ≠ μ (c (2 * i)) (d (2 * j)) ∧ e ≠ μ (c (2 * (i + 1))) (d (2 * j))
      ∧ e ≠ μ (c (2 * i)) (d (2 * (j + 1))) ∧ e ≠ μ (c (2 * (i + 1))) (d (2 * (j + 1))) := by
    intro i j
    rw [e2 i, e2 j]
    exact ⟨μ (c (2 * i + 1)) (d (2 * j + 1)),
      (hμ _ _ _ _ (hcadj (2 * i)) (hdadj (2 * j))).symm,
      hμ _ _ _ _ (hcadj (2 * i + 1)) (hdadj (2 * j)).symm,
      hμ _ _ _ _ (hcadj (2 * i)).symm (hdadj (2 * j + 1)),
      hμ _ _ _ _ (hcadj (2 * i + 1)) (hdadj (2 * j + 1))⟩
  have grid := wind_diag (fun i j => μ (c (2 * i)) (d (2 * j))) hsq (m * n)
  have hf : ∀ t, (fun t => μ (c t) (d t)) (t + 1) ≠ (fun t => μ (c t) (d t)) t :=
    fun t => (hμ _ _ _ _ (hcadj t) (hdadj t)).symm
  have hfper : ∀ t, (fun t => μ (c t) (d t)) (t + m * n) = (fun t => μ (c t) (d t)) t := by
    intro t
    show μ (c (t + m * n)) (d (t + m * n)) = μ (c t) (d t)
    rw [periodic_mul c m hcper n t, mul_comm m n, periodic_mul d n hdper m t]
  have d1 : wind (fun t => μ (c t) (d t)) (2 * (m * n))
      = -2 * wind (fun i => μ (c (2 * i)) (d (2 * i))) (m * n) :=
    wind_two_step (fun t => μ (c t) (d t)) hf (m * n)
  have d2 := wind_periodic_mul (fun t => μ (c t) (d t)) (m * n) hfper 2
  have d3 := wind_mod_two (fun t => μ (c t) (d t)) hf (m * n)
  have r1 : wind (fun i => μ (c (2 * i)) (d 0)) (m * n) = n * hw μ c m (d 0) :=
    wind_periodic_mul (fun i => μ (c (2 * i)) (d 0)) m (fun t => by
      show μ (c (2 * (t + m))) (d 0) = μ (c (2 * t)) (d 0)
      rw [show 2 * (t + m) = 2 * t + m + m by ring, hcper, hcper]) n
  have r2 : wind (fun j => μ (c 0) (d (2 * j))) (n * m) = m * hw (fun h g => μ g h) d n (c 0) :=
    wind_periodic_mul (fun j => μ (c 0) (d (2 * j))) n (fun t => by
      show μ (c 0) (d (2 * (t + n))) = μ (c 0) (d (2 * t))
      rw [show 2 * (t + n) = 2 * t + n + n by ring, hdper, hdper]) m
  have ecol : (fun j => μ (c (2 * (m * n))) (d (2 * j))) = fun j => μ (c 0) (d (2 * j)) := by
    have h0 : c (2 * (m * n)) = c 0 := by
      have h := periodic_mul c m hcper (2 * n) 0
      rw [zero_add] at h
      rw [← h]
      congr 1
      ring
    rw [h0]
  have grid' : wind (fun i => μ (c (2 * i)) (d (2 * i))) (m * n)
      = wind (fun i => μ (c (2 * i)) (d 0)) (m * n)
        + wind (fun j => μ (c (2 * (m * n))) (d (2 * j))) (m * n) := grid
  rw [ecol, r1, mul_comm m n, r2] at grid'
  rw [mul_comm m n] at d1 d2 d3
  rw [mul_comm (n * m) 2] at d2
  have hnm : (n * m) % 2 = 1 := Nat.odd_iff.mp (hn.mul hm)
  have hD : Odd (wind (fun i => μ (c (2 * i)) (d (2 * i))) (n * m)) := by
    rw [Int.odd_iff]
    push_cast at d2
    omega
  rw [grid'] at hD
  obtain ⟨q, hq⟩ := hD
  obtain ⟨a, ha⟩ := hn
  obtain ⟨b, hb⟩ := hm
  have ha' : (n : ℤ) = 2 * a + 1 := by exact_mod_cast ha
  have hb' : (m : ℤ) = 2 * b + 1 := by exact_mod_cast hb
  refine ⟨q - a * hw μ c m (d 0) - b * hw (fun h g => μ g h) d n (c 0), ?_⟩
  linear_combination hq - hw μ c m (d 0) * ha' - hw (fun h g => μ g h) d n (c 0) * hb'

/-- P4 (fixed vertex, K_3 case of the fixpoint corollary in Wrochna Section 4). An odd closed walk of G with odd
half-winding at h0 passes through a vertex having the same colour in the rows h0 and h1. -/
theorem exists_fixed_vertex (hμ : Proper G H μ) {c : ℕ → α} {m : ℕ} (hc : IsOddCyc G c m)
    {h0 h1 : β} (hh : H.Adj h0 h1) (hodd : Odd (hw μ c m h0)) :
    ∃ i, μ (c i) h0 = μ (c i) h1 := by
  by_contra hno
  have hne : ∀ i, μ (c i) h0 ≠ μ (c i) h1 := fun i hi => hno ⟨i, hi⟩
  obtain ⟨hm, hadj, hper⟩ := hc
  have hanti : ∀ t, altSeq μ c h0 h1 (t + m) ≠ altSeq μ c h0 h1 t := by
    intro t
    rw [altSeq_shift hm hper]
    show μ (c t) (if t % 2 = 0 then h1 else h0) ≠ μ (c t) (if t % 2 = 0 then h0 else h1)
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · rw [if_pos ht, if_pos ht]
      exact (hne t).symm
    · have ht' : ¬ t % 2 = 0 := by omega
      rw [if_neg ht', if_neg ht']
      exact hne t
  have key := wind_even_of_no_antipode (altSeq μ c h0 h1) m hm (altSeq_step hμ hadj hh)
    (altSeq_per hper h0 h1) hanti
  have eL : (fun j => altSeq μ c h0 h1 (2 * j)) = fun i => μ (c (2 * i)) h0 :=
    funext fun j => altSeq_even c h0 h1 j
  rw [eL] at key
  exact (Int.not_odd_iff_even.mpr key) hodd

/-- The graph G with every vertex that has the same colour in rows h0 and h1 isolated. -/
def cutGraph (G : SimpleGraph α) (μ : α → β → Fin 3) (h0 h1 : β) : SimpleGraph α where
  Adj g g' := G.Adj g g' ∧ μ g h0 ≠ μ g h1 ∧ μ g' h0 ≠ μ g' h1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- P5 (K_3 case of the cutOddCycles lemma in Wrochna Section 4). If every odd closed walk of G passes through a vertex
with the same colour in the rows h0 and h1, then G is 3-colourable. -/
theorem colorable_of_fixed (hμ : Proper G H μ) {h0 h1 : β} (hh : H.Adj h0 h1)
    (hfix : ∀ (c : ℕ → α) (m : ℕ), IsOddCyc G c m → ∃ i, μ (c i) h0 = μ (c i) h1) :
    G.Colorable 3 := by
  have h2 : (cutGraph G μ h0 h1).Colorable 2 := by
    by_contra hn
    obtain ⟨c, m, hc⟩ := core_exists_oddCyc hn
    obtain ⟨i, hi⟩ := hfix c m ⟨hc.1, fun i => (hc.2.1 i).1, hc.2.2⟩
    exact (hc.2.1 i).2.1 hi
  obtain ⟨δ⟩ := h2
  refine ⟨Coloring.mk (fun g => μ g (if δ g = 0 then h0 else h1)) ?_⟩
  intro g g' hadj
  show μ g (if δ g = 0 then h0 else h1) ≠ μ g' (if δ g' = 0 then h0 else h1)
  by_cases hcut : (cutGraph G μ h0 h1).Adj g g'
  · have hδ : δ g ≠ δ g' := δ.valid hcut
    by_cases h0g : δ g = 0
    · have h0g' : ¬ δ g' = 0 := fun h => hδ (h0g.trans h.symm)
      rw [if_pos h0g, if_neg h0g']
      exact hμ _ _ _ _ hadj hh
    · have h0g' : δ g' = 0 := by omega
      rw [if_neg h0g, if_pos h0g']
      exact hμ _ _ _ _ hadj hh.symm
  · have hS : μ g h0 = μ g h1 ∨ μ g' h0 = μ g' h1 := by
      by_contra hS
      rw [not_or] at hS
      exact hcut ⟨hadj, hS.1, hS.2⟩
    have k1 : μ g h0 ≠ μ g' h1 := hμ _ _ _ _ hadj hh
    have k2 : μ g h1 ≠ μ g' h0 := hμ _ _ _ _ hadj hh.symm
    by_cases h0g : δ g = 0 <;> by_cases h0g' : δ g' = 0
    · rw [if_pos h0g, if_pos h0g']
      rcases hS with hS | hS
      · rw [hS]; exact k2
      · rw [hS]; exact k1
    · rw [if_pos h0g, if_neg h0g']; exact k1
    · rw [if_neg h0g, if_pos h0g']; exact k2
    · rw [if_neg h0g, if_neg h0g']
      rcases hS with hS | hS
      · rw [← hS]; exact k1
      · rw [← hS]; exact k2

/-- P6. One side of the theorem: if G is connected and some odd closed walk of G has odd
half-winding at the base point of an odd closed walk of H, then G is 3-colourable. -/
theorem colorable_of_odd_hw (hμ : Proper G H μ) (hG : G.Preconnected) {c0 : ℕ → α} {m0 : ℕ}
    (hc0 : IsOddCyc G c0 m0) {d0 : ℕ → β} {n0 : ℕ} (hd0 : IsOddCyc H d0 n0)
    (hodd : Odd (hw μ c0 m0 (d0 0))) : G.Colorable 3 := by
  refine colorable_of_fixed hμ (hd0.2.1 0) fun c m hc => ?_
  refine exists_fixed_vertex hμ hc (hd0.2.1 0) ?_
  have p1 := parity_switch hμ hc hd0
  have p0 := parity_switch hμ hc0 hd0
  have e : hw (fun h g => μ g h) d0 n0 (c 0) = hw (fun h g => μ g h) d0 n0 (c0 0) :=
    hw_reachable hμ.swap hd0 (hG (c 0) (c0 0))
  rw [e] at p1
  rw [Int.odd_iff] at p0 p1 hodd ⊢
  omega

end Product

/- ## Part 6: the theorem -/

/-- T1. K_3 is multiplicative for connected graphs. -/
theorem core3_connected {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    (hG : G.Preconnected) (hH : H.Preconnected) :
    (tensorProd G H).Colorable 3 → G.Colorable 3 ∨ H.Colorable 3 := by
  rintro ⟨C⟩
  have hμ : Proper G H (fun g h => C (g, h)) := fun g g' h h' hg hh =>
    C.valid (show (tensorProd G H).Adj (g, h) (g', h') from ⟨hg, hh⟩)
  by_cases hG2 : G.Colorable 2
  · exact Or.inl (hG2.mono (by norm_num))
  by_cases hH2 : H.Colorable 2
  · exact Or.inr (hH2.mono (by norm_num))
  obtain ⟨c0, m0, hc0⟩ := core_exists_oddCyc hG2
  obtain ⟨d0, n0, hd0⟩ := core_exists_oddCyc hH2
  have p := parity_switch hμ hc0 hd0
  by_cases hodd : Odd (hw (fun g h => C (g, h)) c0 m0 (d0 0))
  · exact Or.inl (colorable_of_odd_hw hμ hG hc0 hd0 hodd)
  · refine Or.inr (colorable_of_odd_hw hμ.swap hH hd0 hc0 ?_)
    rw [Int.odd_iff] at p hodd ⊢
    omega

/-- T2. **El-Zahar--Sauer**: K_3 is multiplicative. -/
theorem core3 {α β : Type} [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β) :
    (tensorProd G H).Colorable 3 → G.Colorable 3 ∨ H.Colorable 3 := by
  intro hc
  by_contra hno
  rw [not_or] at hno
  obtain ⟨hG, hH⟩ := hno
  rw [colorable_iff_forall_connectedComponent, not_forall] at hG hH
  obtain ⟨cG, hcG⟩ := hG
  obtain ⟨cH, hcH⟩ := hH
  have hom : tensorProd cG.toSimpleGraph cH.toSimpleGraph →g tensorProd G H :=
    ⟨fun p => (p.1.val, p.2.val), fun h => ⟨h.1, h.2⟩⟩
  rcases core3_connected cG.toSimpleGraph cH.toSimpleGraph
      cG.connected_toSimpleGraph.preconnected cH.connected_toSimpleGraph.preconnected
      (hc.of_hom hom) with h | h
  · exact hcG h
  · exact hcH h

end ElZS


/-!
# El-Zahar--Sauer: the easy cases n = 0, 1, 2

`K_n` is multiplicative for `n ≤ 2`: if `G × H` is `n`-colourable then so is `G` or `H`.
For `n = 2`, odd closed walks in `G` and `H` (of lengths `a`, `b`) are run in lockstep for
`a * b` steps to get an odd closed walk in `G × H`.
-/

open SimpleGraph HedetniemiConjecture

namespace ElZS

/-- A graph with no odd closed walk is 2-colourable (wrapper around Mathlib). -/
theorem colorable_two_of_no_odd_loop {V : Type*} {G : SimpleGraph V}
    (h : ∀ (u : V) (w : G.Walk u u), ¬ Odd w.length) : G.Colorable 2 :=
  two_colorable_iff_forall_loop_even.mpr fun u w => Nat.not_odd_iff_even.mp (h u w)

/-- A graph that is not 2-colourable has an odd closed walk. -/
theorem exists_odd_loop_of_not_colorable_two {V : Type*} {G : SimpleGraph V}
    (h : ¬ G.Colorable 2) : ∃ (u : V) (w : G.Walk u u), Odd w.length := by
  by_contra hno
  exact h (colorable_two_of_no_odd_loop fun u w hw => hno ⟨u, w, hw⟩)

/-- A walk along any sequence of consecutively adjacent vertices. -/
theorem exists_walk_of_seq {V : Type*} {G : SimpleGraph V} (s : ℕ → V)
    (h : ∀ i, G.Adj (s i) (s (i + 1))) (N : ℕ) :
    ∃ w : G.Walk (s 0) (s N), w.length = N := by
  induction N with
  | zero => exact ⟨Walk.nil, rfl⟩
  | succ N ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨w.concat (h N), by rw [Walk.length_concat, hw]⟩

/-- Going round a closed walk periodically: consecutive positions are adjacent. -/
theorem adj_getVert_mod {V : Type*} {G : SimpleGraph V} {u : V} (p : G.Walk u u)
    (hp : 0 < p.length) (i : ℕ) :
    G.Adj (p.getVert (i % p.length)) (p.getVert ((i + 1) % p.length)) := by
  have hlt : i % p.length < p.length := Nat.mod_lt _ hp
  have key : p.getVert ((i + 1) % p.length) = p.getVert (i % p.length + 1) := by
    rw [← Nat.mod_add_mod i p.length 1]
    rcases Nat.lt_or_ge (i % p.length + 1) p.length with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]
    · have h2 : i % p.length + 1 = p.length := by omega
      rw [h2, Nat.mod_self, Walk.getVert_zero, Walk.getVert_length]
  rw [key]
  exact p.adj_getVert_succ hlt

/-- Odd closed walks in both factors give an odd closed walk in the tensor product. -/
theorem exists_odd_loop_tensorProd {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    {u : α} {v : β} (p : G.Walk u u) (q : H.Walk v v) (hp : Odd p.length)
    (hq : Odd q.length) : ∃ w : (tensorProd G H).Walk (u, v) (u, v), Odd w.length := by
  let s : ℕ → α × β := fun i => (p.getVert (i % p.length), q.getVert (i % q.length))
  have hs : ∀ i, (tensorProd G H).Adj (s i) (s (i + 1)) := fun i =>
    ⟨adj_getVert_mod p hp.pos i, adj_getVert_mod q hq.pos i⟩
  obtain ⟨w, hw⟩ := exists_walk_of_seq s hs (p.length * q.length)
  have h0 : s 0 = (u, v) := by simp [s]
  have hN : s (p.length * q.length) = (u, v) := by
    simp [s, Nat.mul_mod_right, Nat.mul_mod_left]
  refine ⟨w.copy h0 hN, ?_⟩
  rw [Walk.length_copy, hw]
  exact hp.mul hq

theorem mult_zero {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) :
    (tensorProd G H).Colorable 0 → G.Colorable 0 ∨ H.Colorable 0 := by
  intro hc
  simp only [colorable_zero_iff] at hc ⊢
  exact isEmpty_prod.mp hc

theorem exists_adj_of_ne_bot {V : Type*} {G : SimpleGraph V} (h : G ≠ ⊥) :
    ∃ a b, G.Adj a b := by
  by_contra hno
  apply h
  ext a b
  simp only [bot_adj, iff_false]
  exact fun hab => hno ⟨a, b, hab⟩

theorem mult_one {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) :
    (tensorProd G H).Colorable 1 → G.Colorable 1 ∨ H.Colorable 1 := by
  intro hc
  by_contra hno
  rw [not_or, colorable_one_iff, colorable_one_iff] at hno
  obtain ⟨a, a', ha⟩ := exists_adj_of_ne_bot hno.1
  obtain ⟨b, b', hb⟩ := exists_adj_of_ne_bot hno.2
  have hadj : (tensorProd G H).Adj (a, b) (a', b') := ⟨ha, hb⟩
  rw [colorable_one_iff.mp hc] at hadj
  exact hadj

theorem mult_two {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) :
    (tensorProd G H).Colorable 2 → G.Colorable 2 ∨ H.Colorable 2 := by
  intro hc
  by_contra hno
  rw [not_or] at hno
  obtain ⟨u, p, hp⟩ := exists_odd_loop_of_not_colorable_two hno.1
  obtain ⟨v, q, hq⟩ := exists_odd_loop_of_not_colorable_two hno.2
  obtain ⟨w, hw⟩ := exists_odd_loop_tensorProd p q hp hq
  exact Nat.not_even_iff_odd.mpr hw (two_colorable_iff_forall_loop_even.mp hc _ w)

/-- `K_n` is multiplicative for `n ≤ 2`. -/
theorem mult_le_two {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) (n : ℕ)
    (hn : n ≤ 2) : (tensorProd G H).Colorable n → G.Colorable n ∨ H.Colorable n := by
  interval_cases n
  · exact mult_zero G H
  · exact mult_one G H
  · exact mult_two G H

end ElZS


/-!
# El-Zahar--Sauer: final assembly

Reduces the upstream statement
`HedetniemiConjecture.hedetniemi_conjecture.variants.el_zahar_sauer` to the
multiplicativity of the complete graphs K_n for n at most 3 (`ElZS.mult`).
-/

open SimpleGraph HedetniemiConjecture

namespace ElZS

/-- The final step: if `K_n` is multiplicative for every `n ≤ 3`, then the
El-Zahar--Sauer equality holds whenever `min χ(G) χ(H) ≤ 4`. -/
theorem main_of_mult
    (mult : ∀ {α β : Type} [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β)
      (n : ℕ), n ≤ 3 → (tensorProd G H).Colorable n → G.Colorable n ∨ H.Colorable n)
    {α β : Type} [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β)
    (h : min G.chromaticNumber H.chromaticNumber ≤ 4) :
    (tensorProd G H).chromaticNumber = min G.chromaticNumber H.chromaticNumber := by
  refine le_antisymm (chromaticNumber_tensorProd_le_min G H) ?_
  by_contra hlt
  rw [not_le] at hlt
  set n : ℕ := (tensorProd G H).chromaticNumber.toNat with hn
  have hcol : (tensorProd G H).Colorable n := colorable_chromaticNumber_of_fintype _
  have hne : (tensorProd G H).chromaticNumber ≠ ⊤ := ne_top_of_lt hlt
  have heq : ((n : ℕ) : ℕ∞) = (tensorProd G H).chromaticNumber := ENat.natCast_toNat hne
  have hn3 : n ≤ 3 := by
    have : ((n : ℕ) : ℕ∞) < 4 := heq ▸ lt_of_lt_of_le hlt h
    exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
  rcases mult G H n hn3 hcol with hG | hH
  · have := hG.chromaticNumber_le
    have : min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber :=
      heq ▸ (min_le_left _ _).trans this
    exact absurd hlt (not_lt.mpr this)
  · have := hH.chromaticNumber_le
    have : min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber :=
      heq ▸ (min_le_right _ _).trans this
    exact absurd hlt (not_lt.mpr this)

/-- `K_n` is multiplicative for every `n ≤ 3`. -/
theorem mult {α β : Type} [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β)
    (n : ℕ) (hn : n ≤ 3) : (tensorProd G H).Colorable n → G.Colorable n ∨ H.Colorable n := by
  rcases Nat.lt_or_ge n 3 with h | h
  · exact mult_le_two G H n (by omega)
  · obtain rfl : n = 3 := by omega
    exact core3 G H

/-- The upstream target `hedetniemi_conjecture.variants.el_zahar_sauer`, same type. -/
theorem main {α β : Type} [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β)
    (h : min G.chromaticNumber H.chromaticNumber ≤ 4) :
    (tensorProd G H).chromaticNumber = min G.chromaticNumber H.chromaticNumber :=
  main_of_mult (fun G H n hn => mult G H n hn) G H h

end ElZS

theorem OMA.solution : type_of% @HedetniemiConjecture.hedetniemi_conjecture.variants.el_zahar_sauer :=
  @ElZS.main
