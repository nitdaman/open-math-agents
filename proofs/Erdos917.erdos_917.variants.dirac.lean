import FormalConjectures.ErdosProblems.«917»

/-! Dirac's construction: the join of two odd cycles of length `2n+1` is `6`-critical and has
`(2n+1)^2 + 2(2n+1) = 4n^2+8n+3` edges. The vertex `i` of `Fin (4n+2)` lies on the side `i % 2`
at the position `i / 2` of the cycle of that side. -/

open SimpleGraph

namespace OMA

/-- Adjacency along the cycle on the positions `0, …, 2n`. -/
def cyc (n a b : ℕ) : Prop :=
  a + 1 = b ∨ b + 1 = a ∨ (a = 0 ∧ b = 2 * n) ∨ (a = 2 * n ∧ b = 0)

/-- Adjacency of the join of the two cycles, on natural numbers. -/
def adjN (n i j : ℕ) : Prop :=
  i % 2 ≠ j % 2 ∨ (i % 2 = j % 2 ∧ cyc n (i / 2) (j / 2))

/-- The join of two cycles of length `2n+1`. -/
def dg (n : ℕ) : SimpleGraph (Fin (4 * n + 2)) where
  Adj i j := 0 < n ∧ adjN n i.val j.val
  symm := ⟨fun i j h => ⟨h.1, by
    have h2 := h.2
    unfold adjN cyc at *
    omega⟩⟩
  loopless := ⟨fun i h => by
    have h1 := h.1
    have h2 := h.2
    unfold adjN cyc at h2
    omega⟩

/-- A proper `3`-colouring of the odd cycle. -/
def col3 (n a : ℕ) : ℕ := if a = 2 * n then 2 else a % 2

/-- A proper `6`-colouring of the join. -/
def c6 (n i : ℕ) : ℕ := 3 * (i % 2) + col3 n (i / 2)

/-- The position `a` read from the position `q` onwards around the cycle. -/
def shift (n q a : ℕ) : ℕ := if q ≤ a then a - q else a + (2 * n + 1) - q

/-- A `5`-colouring of the join with the vertex `v` removed. -/
def fv (n v i : ℕ) : ℕ :=
  if i % 2 = v % 2 then shift n (v / 2) (i / 2) % 2 else 2 + col3 n (i / 2)

/-- The later endpoint of a cycle edge. -/
def qq (pu pv : ℕ) : ℕ := if pu + 1 = pv then pv else if pv + 1 = pu then pu else 0

/-- The colouring used when the removed edge `uv` lies on one side. -/
def geS (n q su si pi : ℕ) : ℕ := if si = su then shift n q pi % 2 else 2 + col3 n pi

/-- The colouring used when the removed edge `uv` joins the two sides. -/
def geC (n su pu pv si pi : ℕ) : ℕ :=
  if si = su then (if shift n pu pi = 0 then 4 else shift n pu pi % 2)
  else (if shift n pv pi = 0 then 4 else 2 + shift n pv pi % 2)

/-- A `5`-colouring of the join with the edge `uv` removed. -/
def ge (n u v i : ℕ) : ℕ :=
  if u % 2 = v % 2 then geS n (qq (u / 2) (v / 2)) (u % 2) (i % 2) (i / 2)
  else geC n (u % 2) (u / 2) (v / 2) (i % 2) (i / 2)

lemma c6_lt (n i : ℕ) : c6 n i < 6 := by
  unfold c6 col3
  split_ifs <;> omega

lemma c6_ne {n i j : ℕ} (hn : 0 < n) (hi : i < 4 * n + 2) (hj : j < 4 * n + 2)
    (h : adjN n i j) : c6 n i ≠ c6 n j := by
  unfold adjN cyc at h
  unfold c6 col3
  split_ifs <;> omega

lemma fv_lt (n v i : ℕ) : fv n v i < 5 := by
  unfold fv col3
  split_ifs <;> omega

lemma fv_ne {n v i j : ℕ} (hn : 0 < n) (hi : i < 4 * n + 2) (hj : j < 4 * n + 2)
    (hv : v < 4 * n + 2) (h : adjN n i j) (hiv : i ≠ v) (hjv : j ≠ v) :
    fv n v i ≠ fv n v j := by
  unfold adjN cyc at h
  unfold fv col3 shift
  split_ifs <;> omega

lemma ge_lt (n u v i : ℕ) : ge n u v i < 5 := by
  unfold ge geS geC col3
  split_ifs <;> omega

set_option maxHeartbeats 4000000 in
lemma geS_ne {n su pu pv si pi sj pj : ℕ} (hn : 0 < n) (hpu : pu ≤ 2 * n) (hpv : pv ≤ 2 * n)
    (hpi : pi ≤ 2 * n) (hpj : pj ≤ 2 * n) (hsu : su < 2) (hsi : si < 2) (hsj : sj < 2)
    (huv : cyc n pu pv) (h : si ≠ sj ∨ (si = sj ∧ cyc n pi pj))
    (hne : ¬ ((si = su ∧ pi = pu ∧ sj = su ∧ pj = pv) ∨
      (si = su ∧ pi = pv ∧ sj = su ∧ pj = pu))) :
    geS n (qq pu pv) su si pi ≠ geS n (qq pu pv) su sj pj := by
  unfold cyc at h huv
  unfold geS col3 shift qq
  rcases huv with huv | huv | huv | huv <;>
  rcases h with h | ⟨h, h' | h' | h' | h'⟩ <;>
  split_ifs <;> omega

set_option maxHeartbeats 4000000 in
lemma geC_ne {n su sv pu pv si pi sj pj : ℕ} (hn : 0 < n) (hpu : pu ≤ 2 * n) (hpv : pv ≤ 2 * n)
    (hpi : pi ≤ 2 * n) (hpj : pj ≤ 2 * n) (hsu : su < 2) (hsv : sv < 2) (hsi : si < 2)
    (hsj : sj < 2) (huv : su ≠ sv) (h : si ≠ sj ∨ (si = sj ∧ cyc n pi pj))
    (hne : ¬ ((si = su ∧ pi = pu ∧ sj = sv ∧ pj = pv) ∨
      (si = sv ∧ pi = pv ∧ sj = su ∧ pj = pu))) :
    geC n su pu pv si pi ≠ geC n su pu pv sj pj := by
  unfold cyc at h
  unfold geC shift
  rcases h with h | ⟨h, h' | h' | h' | h'⟩ <;>
  split_ifs <;> omega

lemma ge_ne {n u v i j : ℕ} (hn : 0 < n) (hu : u < 4 * n + 2) (hv : v < 4 * n + 2)
    (hi : i < 4 * n + 2) (hj : j < 4 * n + 2) (huv : adjN n u v) (h : adjN n i j)
    (hne : ¬ ((i = u ∧ j = v) ∨ (i = v ∧ j = u))) : ge n u v i ≠ ge n u v j := by
  unfold adjN at h huv
  unfold ge
  by_cases hs : u % 2 = v % 2
  · rw [if_pos hs, if_pos hs]
    have hc : cyc n (u / 2) (v / 2) := by
      rcases huv with huv | huv
      · exact absurd hs huv
      · exact huv.2
    apply geS_ne hn (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hc h
    intro hcon
    apply hne
    omega
  · rw [if_neg hs, if_neg hs]
    apply geC_ne hn (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hs h
    intro hcon
    apply hne
    omega

lemma colorable_of_nat {V : Type*} (H : SimpleGraph V) (k : ℕ) (f : V → ℕ)
    (hlt : ∀ v, f v < k) (hne : ∀ a b, H.Adj a b → f a ≠ f b) : H.Colorable k :=
  ⟨Coloring.mk (fun v => (⟨f v, hlt v⟩ : Fin k))
    (fun {a b} h heq => hne a b h (congrArg Fin.val heq))⟩

lemma dg_colorable6 (n : ℕ) (hn : 0 < n) : (dg n).Colorable 6 :=
  colorable_of_nat _ 6 (fun i => c6 n i.val) (fun i => c6_lt n _)
    (fun a b h => c6_ne hn a.2 b.2 h.2)

lemma three_of_two {α : Type*} {p q a b c : α} (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (hc : c = p ∨ c = q) (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;> simp_all

/-- The vertex with a given number. -/
def vtx (n k : ℕ) : Fin (4 * n + 2) := ⟨k % (4 * n + 2), Nat.mod_lt _ (by omega)⟩

lemma vtx_val {n k : ℕ} (h : k < 4 * n + 2) : (vtx n k).val = k := Nat.mod_eq_of_lt h

lemma col_adj (n : ℕ) (hn : 0 < n) (c : (dg n).Coloring (Fin 5)) (i j : ℕ)
    (hi : i < 4 * n + 2) (hj : j < 4 * n + 2) (h : adjN n i j) :
    c (vtx n i) ≠ c (vtx n j) := by
  apply c.valid
  refine ⟨hn, ?_⟩
  rw [vtx_val hi, vtx_val hj]
  exact h

/-- An odd cycle sees a third colour. -/
lemma odd_side (n : ℕ) (hn : 0 < n) (c : (dg n).Coloring (Fin 5)) (s : ℕ) (hs : s < 2) :
    ∃ a, a ≤ 2 * n ∧ c (vtx n (2 * a + s)) ≠ c (vtx n s) ∧
      c (vtx n (2 * a + s)) ≠ c (vtx n (2 + s)) := by
  by_contra hcon
  have hall : ∀ a, a ≤ 2 * n →
      (c (vtx n (2 * a + s)) = c (vtx n s) ∨ c (vtx n (2 * a + s)) = c (vtx n (2 + s))) := by
    intro a ha
    by_cases h1 : c (vtx n (2 * a + s)) = c (vtx n s)
    · exact Or.inl h1
    · by_cases h2 : c (vtx n (2 * a + s)) = c (vtx n (2 + s))
      · exact Or.inr h2
      · exact absurd ⟨a, ha, h1, h2⟩ hcon
  have hev : ∀ k, k ≤ n → c (vtx n (2 * (2 * k) + s)) = c (vtx n s) := by
    intro k
    induction k with
    | zero =>
      intro _
      have e : 2 * (2 * 0) + s = s := by omega
      rw [e]
    | succ k ih =>
      intro hk
      have h0 := ih (by omega)
      have e1 := col_adj n hn c (2 * (2 * k) + s) (2 * (2 * k + 1) + s) (by omega) (by omega)
        (by unfold adjN cyc; omega)
      have e2 := col_adj n hn c (2 * (2 * k + 1) + s) (2 * (2 * (k + 1)) + s) (by omega)
        (by omega) (by unfold adjN cyc; omega)
      have h3 := three_of_two (hall (2 * k) (by omega)) (hall (2 * k + 1) (by omega))
        (hall (2 * (k + 1)) (by omega)) e1 e2
      rw [← h3]
      exact h0
  have hw := col_adj n hn c (2 * (2 * n) + s) s (by omega) (by omega)
    (by unfold adjN cyc; omega)
  exact hw (hev n le_rfl)

lemma six_in_five (a b c d e f : Fin 5) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) (h4 : d ≠ e)
    (h5 : d ≠ f) (h6 : e ≠ f) (h7 : a ≠ d) (h8 : a ≠ e) (h9 : a ≠ f) (h10 : b ≠ d)
    (h11 : b ≠ e) (h12 : b ≠ f) (h13 : c ≠ d) (h14 : c ≠ e) (h15 : c ≠ f) : False := by
  have hinj : Function.Injective ![a, b, c, d, e, f] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have := Fintype.card_le_of_injective _ hinj
  simp at this

lemma not_colorable5 (n : ℕ) (hn : 0 < n) : ¬ (dg n).Colorable 5 := by
  rintro ⟨c⟩
  obtain ⟨a, ha, ha1, ha2⟩ := odd_side n hn c 0 (by omega)
  obtain ⟨b, hb, hb1, hb2⟩ := odd_side n hn c 1 (by omega)
  have hadj := col_adj n hn c
  exact six_in_five (c (vtx n 0)) (c (vtx n (2 + 0))) (c (vtx n (2 * a + 0)))
    (c (vtx n 1)) (c (vtx n (2 + 1))) (c (vtx n (2 * b + 1)))
    (hadj 0 (2 + 0) (by omega) (by omega) (by unfold adjN cyc; omega))
    ha1.symm ha2.symm
    (hadj 1 (2 + 1) (by omega) (by omega) (by unfold adjN cyc; omega))
    hb1.symm hb2.symm
    (hadj 0 1 (by omega) (by omega) (by unfold adjN; omega))
    (hadj 0 (2 + 1) (by omega) (by omega) (by unfold adjN; omega))
    (hadj 0 (2 * b + 1) (by omega) (by omega) (by unfold adjN; omega))
    (hadj (2 + 0) 1 (by omega) (by omega) (by unfold adjN; omega))
    (hadj (2 + 0) (2 + 1) (by omega) (by omega) (by unfold adjN; omega))
    (hadj (2 + 0) (2 * b + 1) (by omega) (by omega) (by unfold adjN; omega))
    (hadj (2 * a + 0) 1 (by omega) (by omega) (by unfold adjN; omega))
    (hadj (2 * a + 0) (2 + 1) (by omega) (by omega) (by unfold adjN; omega))
    (hadj (2 * a + 0) (2 * b + 1) (by omega) (by omega) (by unfold adjN; omega))

lemma dg_critical (n : ℕ) (hn : 0 < n) : Erdos917.IsKCritical (dg n) 6 := by
  have h6 := dg_colorable6 n hn
  have h5 := not_colorable5 n hn
  have hchi : (dg n).chromaticNumber = ((6 : ℕ) : ℕ∞) := by
    have h := (chromaticNumber_eq_iff_colorable_not_colorable (G := dg n) (n := 5)).mpr ⟨h6, h5⟩
    rw [h]
    norm_num
  have h56 : ((5 : ℕ) : ℕ∞) < ((6 : ℕ) : ℕ∞) := by exact_mod_cast (by norm_num : (5 : ℕ) < 6)
  refine ⟨⟨hchi, ?_⟩, ?_⟩
  · intro v
    change ((⊤ : (dg n).Subgraph).deleteVerts {v}).coe.chromaticNumber <
      (⊤ : (dg n).Subgraph).coe.chromaticNumber
    have hlow : ((5 : ℕ) : ℕ∞) < (⊤ : (dg n).Subgraph).coe.chromaticNumber := by
      rw [lt_chromaticNumber_iff_not_colorable]
      rintro ⟨c⟩
      exact h5 ⟨Coloring.mk (fun x => c ⟨x, Set.mem_univ x⟩) (fun {a b} h => c.valid h)⟩
    have hup : ((⊤ : (dg n).Subgraph).deleteVerts {v}).coe.chromaticNumber ≤ ((5 : ℕ) : ℕ∞) := by
      apply Colorable.chromaticNumber_le
      refine colorable_of_nat _ 5 (fun x => fv n v.val x.1.val) (fun x => fv_lt n _ _) ?_
      intro a b hab
      have h := hab
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at h
      obtain ⟨-, hav, -, hbv, hadj⟩ := h
      have hadj' : (dg n).Adj a.1 b.1 := Subgraph.top_adj.mp hadj
      exact fv_ne hn a.1.2 b.1.2 v.2 hadj'.2
        (fun e => hav (Set.mem_singleton_iff.mpr (Fin.ext e)))
        (fun e => hbv (Set.mem_singleton_iff.mpr (Fin.ext e)))
    exact lt_of_le_of_lt hup hlow
  · intro e he
    induction e using Sym2.ind with
    | _ u w =>
      have huw : (dg n).Adj u w := he
      change ((dg n).deleteEdges {s(u, w)}).chromaticNumber < (dg n).chromaticNumber
      rw [hchi]
      have hup : ((dg n).deleteEdges {s(u, w)}).chromaticNumber ≤ ((5 : ℕ) : ℕ∞) := by
        apply Colorable.chromaticNumber_le
        refine colorable_of_nat _ 5 (fun x => ge n u.val w.val x.val) (fun x => ge_lt n _ _ _) ?_
        intro a b hab
        rw [deleteEdges_adj] at hab
        obtain ⟨hadj, hne⟩ := hab
        apply ge_ne hn u.2 w.2 a.2 b.2 huw.2 hadj.2
        intro hc
        apply hne
        rw [Set.mem_singleton_iff, Sym2.eq_iff]
        rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
        · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩
      exact lt_of_le_of_lt hup h56

/-- The edges of the join, listed without repetition: the cross edges and the cycle edges. -/
def emap (n : ℕ) :
    (Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕ (Fin 2 × Fin (2 * n + 1)) → Sym2 (Fin (4 * n + 2))
  | Sum.inl (a, b) =>
    s((⟨2 * a.val, by have := a.2; omega⟩ : Fin (4 * n + 2)),
      (⟨2 * b.val + 1, by have := b.2; omega⟩ : Fin (4 * n + 2)))
  | Sum.inr (s, a) =>
    s((⟨2 * a.val + s.val, by have := a.2; have := s.2; omega⟩ : Fin (4 * n + 2)),
      (⟨2 * (if a.val = 2 * n then 0 else a.val + 1) + s.val, by
        have := a.2
        have := s.2
        split_ifs <;> omega⟩ : Fin (4 * n + 2)))

lemma emap_inj (n : ℕ) (hn : 0 < n) : Function.Injective (emap n) := by
  intro x y h
  rcases x with ⟨a, b⟩ | ⟨s, a⟩ <;> rcases y with ⟨a', b'⟩ | ⟨s', a'⟩
  · simp only [emap, Sym2.eq_iff, Fin.mk.injEq] at h
    have h' : a.val = a'.val ∧ b.val = b'.val := by omega
    rw [show a = a' from Fin.ext h'.1, show b = b' from Fin.ext h'.2]
  · exfalso
    simp only [emap, Sym2.eq_iff, Fin.mk.injEq] at h
    have := s'.2
    split_ifs at h <;> omega
  · exfalso
    simp only [emap, Sym2.eq_iff, Fin.mk.injEq] at h
    have := s.2
    split_ifs at h <;> omega
  · simp only [emap, Sym2.eq_iff, Fin.mk.injEq] at h
    have h1 := s.2
    have h2 := s'.2
    have h3 := a.2
    have h4 := a'.2
    have h' : s.val = s'.val ∧ a.val = a'.val := by
      split_ifs at h <;> omega
    rw [show s = s' from Fin.ext h'.1, show a = a' from Fin.ext h'.2]

lemma emap_mem (n : ℕ) (hn : 0 < n) (x) : emap n x ∈ (dg n).edgeSet := by
  rcases x with ⟨a, b⟩ | ⟨s, a⟩
  · simp only [emap, mem_edgeSet]
    refine ⟨hn, ?_⟩
    change adjN n (2 * a.val) (2 * b.val + 1)
    unfold adjN
    omega
  · simp only [emap, mem_edgeSet]
    refine ⟨hn, ?_⟩
    change adjN n (2 * a.val + s.val) (2 * (if a.val = 2 * n then 0 else a.val + 1) + s.val)
    have h1 := a.2
    have h2 := s.2
    unfold adjN cyc
    split_ifs <;> omega

lemma edge_count (n : ℕ) (hn : 0 < n) : 4 * n ^ 2 + 8 * n + 3 ≤ (dg n).edgeSet.ncard := by
  have hsub : Set.range (emap n) ⊆ (dg n).edgeSet := by
    rintro _ ⟨x, rfl⟩
    exact emap_mem n hn x
  have hcard : (Set.range (emap n)).ncard = (2 * n + 1) * (2 * n + 1) + 2 * (2 * n + 1) := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ (emap_inj n hn), Set.ncard_univ,
      Nat.card_eq_fintype_card]
    simp [Fintype.card_sum, Fintype.card_prod]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard] at hle
  have e : (2 * n + 1) * (2 * n + 1) + 2 * (2 * n + 1) = 4 * n ^ 2 + 8 * n + 3 := by ring
  omega

end OMA

theorem OMA.solution : type_of% @Erdos917.erdos_917.variants.dirac := by
  intro n hn
  exact (OMA.edge_count n hn).trans (Erdos917.edgeSet_ncard_le_f (OMA.dg_critical n hn))
