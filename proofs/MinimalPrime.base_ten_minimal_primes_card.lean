import FormalConjectures.Wikipedia.MinimalPrime

-- Problem: Minimal primes in radix bases — base ten minimal primes card
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/MinimalPrime.lean:127 (declaration MinimalPrime.base_ten_minimal_primes_card)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.O11

/-- The 26 minimal primes of base ten. -/
def mlist : List ℕ := [2, 3, 5, 7, 11, 19, 41, 61, 89, 409, 449, 499, 881, 991, 6469, 6949, 9001,
  9049, 9649, 9949, 60649, 666649, 946669, 60000049, 66000049, 66600049]

/-- Their little-endian digit lists. -/
def pats : List (List ℕ) := [[2], [3], [5], [7], [1, 1], [9, 1], [1, 4], [1, 6], [9, 8], [9, 0, 4],
  [9, 4, 4], [9, 9, 4], [1, 8, 8], [1, 9, 9], [9, 6, 4, 6], [9, 4, 9, 6], [1, 0, 0, 9],
  [9, 4, 0, 9], [9, 4, 6, 9], [9, 4, 9, 9], [9, 4, 6, 0, 6], [9, 4, 6, 6, 6, 6],
  [9, 6, 6, 6, 4, 9], [9, 4, 0, 0, 0, 0, 0, 6], [9, 4, 0, 0, 0, 0, 6, 6], [9, 4, 0, 0, 0, 6, 6, 6]]

/-- Little-endian value. -/
def lval : List ℕ → ℕ
  | [] => 0
  | h :: t => h + 10 * lval t

theorem lval_eq (L : List ℕ) : lval L = Nat.ofDigits 10 L := by
  induction L with
  | nil => rfl
  | cons h t ih => simp [lval, Nat.ofDigits_cons, ih]

def isSub : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then isSub as bs else isSub (a :: as) bs

theorem isSub_sound : ∀ (b a : List ℕ), isSub a b = true → a.Sublist b := by
  intro b
  induction b with
  | nil =>
    intro a h
    cases a with
    | nil => exact List.Sublist.slnil
    | cons x xs => simp [isSub] at h
  | cons y ys ih =>
    intro a h
    cases a with
    | nil => exact List.nil_sublist _
    | cons x xs =>
      simp only [isSub] at h
      split_ifs at h with hxy
      · subst hxy
        exact (ih xs h).cons₂ x
      · exact (ih (x :: xs) h).cons y

def hasFactor (n : ℕ) : Bool := (List.range' 2 298).any (fun d => n % d == 0 && decide (d < n))

theorem hasFactor_sound (n : ℕ) (h : hasFactor n = true) : ¬ n.Prime := by
  simp only [hasFactor, List.any_eq_true, List.mem_range', Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨d, ⟨i, hi, rfl⟩, hmod, hlt⟩ := h
  exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) (by omega) hlt

def chk (L : List ℕ) : Bool :=
  pats.any (fun P => isSub P L) || decide (lval L < 2) || hasFactor (lval L)

theorem chk_sound (L : List ℕ) (hp : (lval L).Prime) (hav : ∀ P ∈ pats, ¬ P.Sublist L)
    (h : chk L = true) : False := by
  simp only [chk, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  rcases h with (⟨P, hP, hs⟩ | h2) | hf
  · exact hav P hP (isSub_sound _ _ hs)
  · exact absurd hp (by intro h; have := h.two_le; omega)
  · exact hasFactor_sound _ hf hp

def allL (A : List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => [] :: A.flatMap (fun a => (allL A n).map (fun u => a :: u))

theorem mem_allL (A : List ℕ) : ∀ (n : ℕ) (u : List ℕ), (∀ x ∈ u, x ∈ A) → u.length ≤ n →
    u ∈ allL A n := by
  intro n
  induction n with
  | zero =>
    intro u _ hl
    have : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [allL]
  | succ n ih =>
    intro u hu hl
    cases u with
    | nil => simp [allL]
    | cons x xs =>
      simp only [allL, List.mem_cons, List.mem_flatMap, List.mem_map]
      right
      refine ⟨x, hu x (by simp), xs, ih xs (fun y hy => hu y (by simp [hy])) ?_, rfl⟩
      simp at hl
      omega

theorem pats_val : pats.map lval = mlist := by decide

theorem mlist_prime : ∀ q ∈ mlist, q.Prime := by
  intro q hq
  simp only [mlist, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem pats_ok : pats.all (fun P => P.all (fun x => decide (x < 10)) &&
    (P.getLast? != some 0) && (P != [])) = true := by decide

theorem pats_digits (P : List ℕ) (hP : P ∈ pats) : Nat.digits 10 (lval P) = P := by
  have h := pats_ok
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, _⟩ := h P hP
  rw [lval_eq]
  apply Nat.digits_ofDigits 10 (by norm_num) P h1
  intro hne hl
  apply h2
  rw [List.getLast?_eq_getLast hne, hl]

theorem pats_mem (P : List ℕ) (hP : P ∈ pats) : lval P ∈ mlist := by
  rw [← pats_val]; exact List.mem_map_of_mem hP

theorem sum_mod (w : List ℕ) (h : ∀ x ∈ w, x = 0 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨ x = 9) :
    w.sum % 3 = (w.count 4 + 2 * w.count 8) % 3 := by
  induction w with
  | nil => simp
  | cons x t ih =>
    have ih' := ih (fun y hy => h y (by simp [hy]))
    rcases h x (by simp) with rfl | rfl | rfl | rfl | rfl <;>
      simp [List.count_cons] <;> omega

theorem len2 {a b : ℕ} (hab : a ≠ b) : ∀ w : List ℕ, (∀ x ∈ w, x = a ∨ x = b) →
    w.length = w.count a + w.count b := by
  intro w
  induction w with
  | nil => simp
  | cons x t ih =>
    intro h
    have ih' := ih (fun y hy => h y (by simp [hy]))
    rcases h x (by simp) with rfl | rfl
    · simp [List.count_cons, hab] <;> omega
    · simp [List.count_cons, Ne.symm hab] <;> omega

theorem pair (x y : ℕ) (hxy : x ≠ y) : ∀ l : List ℕ, x ∈ l → y ∈ l →
    [x, y].Sublist l ∨ [y, x].Sublist l := by
  intro l
  induction l with
  | nil => simp
  | cons z t ih =>
    intro hx hy
    rw [List.mem_cons] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact Or.inl ((List.singleton_sublist.mpr hy).cons₂ x)
    · rcases hy with rfl | hy
      · exact Or.inr ((List.singleton_sublist.mpr hx).cons₂ y)
      · rcases ih hx hy with h | h
        · exact Or.inl (h.cons z)
        · exact Or.inr (h.cons z)

theorem rep_sub {a n : ℕ} {l : List ℕ} (h : n ≤ l.count a) : (List.replicate n a).Sublist l :=
  List.replicate_sublist_iff.mpr h

theorem seven_lemma (a : ℕ) : lval (List.replicate a 6 ++ [4]) % 7 = 4 ∧
    4 ≤ lval (List.replicate a 6 ++ [4]) := by
  induction a with
  | zero => simp [lval]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, lval]
    omega

theorem enum1 : (allL [0, 9] 2).all (fun w => chk (1 :: w)) = true := by decide +kernel

theorem enum2 : (allL [0, 6] 7).all (fun u => chk (9 :: 4 :: u)) = true := by decide +kernel

theorem enum3 : ([0, 1, 2].all fun a => (allL [0, 9] 1).all
    fun u => chk (9 :: (List.replicate a 6 ++ 4 :: u))) = true := by decide +kernel

theorem minimality : pats.all (fun P => P.sublists.all (fun l => l.isEmpty ||
    (l.getLast? == some 0) || (lval l == lval P) || decide (lval l < 2) ||
    hasFactor (lval l))) = true := by decide +kernel

/-- Core of the classification, on a digit list. -/
theorem classify (L : List ℕ) (hp : (lval L).Prime) (hnot : lval L ∉ mlist)
    (hav : ∀ P ∈ pats, ¬ P.Sublist L) (hlt : ∀ x ∈ L, x < 10)
    (hlast : ∀ h : L ≠ [], L.getLast h ≠ 0) : False := by
  have hck : ∀ L', L' = L → chk L' = true → False := by
    intro L' e h; subst e; exact chk_sound _ hp hav h
  have h3 : ¬ 3 ∣ lval L := fun h => hnot
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h ▸ (by decide : 3 ∈ mlist))
  have h2 : ¬ 2 ∣ lval L := fun h => hnot
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h ▸ (by decide : 2 ∈ mlist))
  have hsum : ¬ 3 ∣ L.sum := by
    intro h
    apply h3
    have hd : Nat.digits 10 (lval L) = L := by
      rw [lval_eq]
      exact Nat.digits_ofDigits 10 (by norm_num) L hlt hlast
    rw [Nat.three_dvd_iff, hd]
    exact h
  have nm : ∀ d, [d] ∈ pats → d ∉ L := fun d hd hm => hav [d] hd (List.singleton_sublist.mpr hm)
  have n2 := nm 2 (by decide)
  have n3 := nm 3 (by decide)
  have n5 := nm 5 (by decide)
  have n7 := nm 7 (by decide)
  have hne : L ≠ [] := by
    intro h; subst h; exact Nat.not_prime_zero hp
  obtain ⟨d, w, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hd10 : d < 10 := hlt d (by simp)
  have hdm2 : d ≠ 2 := by rintro rfl; exact n2 (by simp)
  have hdm3 : d ≠ 3 := by rintro rfl; exact n3 (by simp)
  have hdm5 : d ≠ 5 := by rintro rfl; exact n5 (by simp)
  have hdm7 : d ≠ 7 := by rintro rfl; exact n7 (by simp)
  have hvd : lval (d :: w) = d + 10 * lval w := rfl
  have hw10 : ∀ x ∈ w, x < 10 := fun x hx => hlt x (by simp [hx])
  have hwm : ∀ x ∈ w, x ≠ 2 ∧ x ≠ 3 ∧ x ≠ 5 ∧ x ≠ 7 := by
    intro x hx
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact n2 (by simp [hx])
    · exact n3 (by simp [hx])
    · exact n5 (by simp [hx])
    · exact n7 (by simp [hx])
  have hsumL : (d :: w).sum = d + w.sum := by simp
  have hd19 : d = 1 ∨ d = 9 := by
    rw [hvd] at h2
    omega
  rcases hd19 with rfl | rfl
  · -- last digit 1
    have n1 : 1 ∉ w := fun h => hav [1, 1] (by decide) ((List.singleton_sublist.mpr h).cons₂ 1)
    have n4 : 4 ∉ w := fun h => hav [1, 4] (by decide) ((List.singleton_sublist.mpr h).cons₂ 1)
    have n6 : 6 ∉ w := fun h => hav [1, 6] (by decide) ((List.singleton_sublist.mpr h).cons₂ 1)
    have hal : ∀ x ∈ w, x = 0 ∨ x = 8 ∨ x = 9 := by
      intro x hx
      have := hw10 x hx
      obtain ⟨a1, a2, a3, a4⟩ := hwm x hx
      have : x ≠ 1 := fun e => n1 (e ▸ hx)
      have : x ≠ 4 := fun e => n4 (e ▸ hx)
      have : x ≠ 6 := fun e => n6 (e ▸ hx)
      omega
    have hc4 : w.count 4 = 0 := List.count_eq_zero_of_not_mem n4
    have hc8 : w.count 8 ≤ 1 := by
      by_contra hc
      exact hav [1, 8, 8] (by decide) ((rep_sub (a := 8) (n := 2) (by omega)).cons₂ 1)
    by_cases h8 : 8 ∈ w
    · have hc8' : w.count 8 = 1 := by
        have := List.count_pos_iff.mpr h8
        omega
      have hm := sum_mod w (fun x hx => by rcases hal x hx with h | h | h <;> simp [h])
      apply hsum
      rw [hsumL]
      omega
    · have hal2 : ∀ x ∈ w, x = 0 ∨ x = 9 := by
        intro x hx
        rcases hal x hx with h | h | h
        · exact Or.inl h
        · exact absurd (h ▸ hx) h8
        · exact Or.inr h
      have hc9 : w.count 9 ≤ 1 := by
        by_contra hc
        exact hav [1, 9, 9] (by decide) ((rep_sub (a := 9) (n := 2) (by omega)).cons₂ 1)
      have hc0 : w.count 0 ≤ 1 := by
        by_contra hc
        rcases List.eq_nil_or_concat w with hw | ⟨t, b, hw⟩
        · subst hw; simp at hc
        · rw [List.concat_eq_append] at hw
          subst hw
          have hb : b ≠ 0 := by
            have := hlast (by simp)
            simpa using this
          have hb9 : b = 9 := by
            rcases hal2 b (by simp) with h | h
            · exact absurd h hb
            · exact h
          subst hb9
          have hct : 2 ≤ t.count 0 := by
            simp [List.count_append] at hc
            omega
          exact hav [1, 0, 0, 9] (by decide)
            (((rep_sub (a := 0) (n := 2) hct).append (List.Sublist.refl [9])).cons₂ 1)
      have hlen := len2 (by norm_num : (0 : ℕ) ≠ 9) w hal2
      have hmem : w ∈ allL [0, 9] 2 :=
        mem_allL _ _ _ (fun x hx => by rcases hal2 x hx with h | h <;> simp [h]) (by omega)
      have := enum1
      rw [List.all_eq_true] at this
      exact hck _ rfl (this w hmem)
  · -- last digit 9
    have n1 : 1 ∉ w := fun h => hav [9, 1] (by decide) ((List.singleton_sublist.mpr h).cons₂ 9)
    have n8 : 8 ∉ w := fun h => hav [9, 8] (by decide) ((List.singleton_sublist.mpr h).cons₂ 9)
    have hal : ∀ x ∈ w, x = 0 ∨ x = 4 ∨ x = 6 ∨ x = 9 := by
      intro x hx
      have := hw10 x hx
      obtain ⟨a1, a2, a3, a4⟩ := hwm x hx
      have : x ≠ 1 := fun e => n1 (e ▸ hx)
      have : x ≠ 8 := fun e => n8 (e ▸ hx)
      omega
    have hc8 : w.count 8 = 0 := List.count_eq_zero_of_not_mem n8
    have hc4 : w.count 4 ≤ 1 := by
      by_contra hc
      exact hav [9, 4, 4] (by decide) ((rep_sub (a := 4) (n := 2) (by omega)).cons₂ 9)
    by_cases h4 : 4 ∈ w
    swap
    · have hc4' : w.count 4 = 0 := List.count_eq_zero_of_not_mem h4
      have hm := sum_mod w (fun x hx => by rcases hal x hx with h | h | h | h <;> simp [h])
      apply hsum
      rw [hsumL]
      omega
    obtain ⟨v, u, hw⟩ := List.append_of_mem h4
    subst hw
    have hcnt : (v ++ 4 :: u).count 4 = v.count 4 + u.count 4 + 1 := by
      rw [List.count_append, List.count_cons_self]
      omega
    have v4 : 4 ∉ v := fun h => by
      have := List.count_pos_iff.mpr h
      omega
    have u4 : 4 ∉ u := fun h => by
      have := List.count_pos_iff.mpr h
      omega
    have hv6 : ∀ x ∈ v, x = 6 := by
      intro x hx
      rcases hal x (by simp [hx]) with h | h | h | h
      · subst h
        exact absurd (((List.singleton_sublist.mpr hx).append
          (by simp : [4].Sublist (4 :: u))).cons₂ 9) (hav [9, 0, 4] (by decide))
      · exact absurd (h ▸ hx) v4
      · exact h
      · subst h
        exact absurd (((List.singleton_sublist.mpr hx).append
          (by simp : [4].Sublist (4 :: u))).cons₂ 9) (hav [9, 9, 4] (by decide))
    have hv : v = List.replicate v.length 6 := List.eq_replicate_iff.mpr ⟨rfl, hv6⟩
    have hu : ∀ x ∈ u, x = 0 ∨ x = 6 ∨ x = 9 := by
      intro x hx
      rcases hal x (by simp [hx]) with h | h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hx) u4
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    rcases List.eq_nil_or_concat u with hu0 | ⟨t, e, hue⟩
    · -- divisible by seven
      subst hu0
      rw [hv] at hp
      have hs := seven_lemma v.length
      have hlv : lval (9 :: (List.replicate v.length 6 ++ [4])) =
          9 + 10 * lval (List.replicate v.length 6 ++ [4]) := rfl
      have h7 : 7 ∣ lval (9 :: (List.replicate v.length 6 ++ [4])) := by
        rw [hlv]
        omega
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h7
      rw [hlv] at this
      omega
    rw [List.concat_eq_append] at hue
    subst hue
    have he0 : e ≠ 0 := by
      have := hlast (by simp)
      simpa using this
    by_cases h6 : 6 ∈ t ++ [e]
    · have hvnil : v = [] := by
        rcases List.eq_nil_or_concat v with h | ⟨s, y, hy⟩
        · exact h
        · exfalso
          rw [List.concat_eq_append] at hy
          have hy6 : y = 6 := hv6 y (by simp [hy])
          have hs1 : [6].Sublist v := List.singleton_sublist.mpr (by simp [hy, hy6])
          have hs2 : [4, 6].Sublist (4 :: (t ++ [e])) :=
            (List.singleton_sublist.mpr h6).cons₂ 4
          exact hav [9, 6, 4, 6] (by decide) ((hs1.append hs2).cons₂ 9)
      subst hvnil
      have n9 : 9 ∉ t ++ [e] := by
        intro h9
        rcases pair 6 9 (by norm_num) _ h6 h9 with h | h
        · exact hav [9, 4, 6, 9] (by decide) ((h.cons₂ 4).cons₂ 9)
        · exact hav [9, 4, 9, 6] (by decide) ((h.cons₂ 4).cons₂ 9)
      have hal2 : ∀ x ∈ t ++ [e], x = 0 ∨ x = 6 := by
        intro x hx
        rcases hu x hx with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (h ▸ hx) n9
      have he6 : e = 6 := by
        rcases hal2 e (by simp) with h | h
        · exact absurd h he0
        · exact h
      subst he6
      have hc6 : (t ++ [6]).count 6 ≤ 3 := by
        by_contra hc
        exact hav [9, 4, 6, 6, 6, 6] (by decide)
          (((rep_sub (a := 6) (n := 4) (by omega)).cons₂ 4).cons₂ 9)
      have hc0 : (t ++ [6]).count 0 ≤ 4 := by
        by_contra hc
        have hct : 5 ≤ t.count 0 := by
          simp [List.count_append] at hc
          omega
        exact hav [9, 4, 0, 0, 0, 0, 0, 6] (by decide)
          ((((rep_sub (a := 0) (n := 5) hct).append (List.Sublist.refl [6])).cons₂ 4).cons₂ 9)
      have hlen := len2 (by norm_num : (0 : ℕ) ≠ 6) _ hal2
      have hmem : t ++ [6] ∈ allL [0, 6] 7 :=
        mem_allL _ _ _ (fun x hx => by rcases hal2 x hx with h | h <;> simp [h]) (by omega)
      have := enum2
      rw [List.all_eq_true] at this
      exact hck _ (by simp) (this _ hmem)
    · have hal2 : ∀ x ∈ t ++ [e], x = 0 ∨ x = 9 := by
        intro x hx
        rcases hu x hx with h | h | h
        · exact Or.inl h
        · exact absurd (h ▸ hx) h6
        · exact Or.inr h
      have he9 : e = 9 := by
        rcases hal2 e (by simp) with h | h
        · exact absurd h he0
        · exact h
      subst he9
      have hc9 : (t ++ [9]).count 9 ≤ 1 := by
        by_contra hc
        exact hav [9, 4, 9, 9] (by decide)
          ((((rep_sub (a := 9) (n := 2) (by omega)).cons₂ 4).trans
            (List.sublist_append_right v _)).cons₂ 9)
      have hc0 : (t ++ [9]).count 0 = 0 := by
        by_contra hc
        have h0 : 0 ∈ t := by
          have : 0 < (t ++ [9]).count 0 := by omega
          have := List.count_pos_iff.mp this
          simpa using this
        exact hav [9, 4, 0, 9] (by decide)
          (((((List.singleton_sublist.mpr h0).append (List.Sublist.refl [9])).cons₂ 4).trans
            (List.sublist_append_right v _)).cons₂ 9)
      have hlen := len2 (by norm_num : (0 : ℕ) ≠ 9) _ hal2
      have hmem : t ++ [9] ∈ allL [0, 9] 1 :=
        mem_allL _ _ _ (fun x hx => by rcases hal2 x hx with h | h <;> simp [h]) (by omega)
      have ha : v.length ≤ 2 := by
        by_contra hc
        have h3v : (List.replicate 3 6).Sublist v :=
          rep_sub (by rw [hv, List.count_replicate_self]; omega)
        exact hav [9, 6, 6, 6, 4, 9] (by decide)
          ((h3v.append ((List.singleton_sublist.mpr (by simp : 9 ∈ t ++ [9])).cons₂ 4)).cons₂ 9)
      have := enum3
      simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false] at this
      have key := this v.length (by omega) _ hmem
      exact hck _ (by rw [← hv]) key

end OMA.O11

open OMA.O11 in
theorem OMA.solution : type_of% @MinimalPrime.base_ten_minimal_primes_card := by
  have key : ∀ p, MinimalPrime.IsMinimalPrimeInBase 10 p ↔ p ∈ mlist := by
    intro p
    constructor
    · rintro ⟨-, hp, hmin⟩
      by_contra hnot
      have hval : lval (Nat.digits 10 p) = p := by rw [lval_eq, Nat.ofDigits_digits]
      apply classify (Nat.digits 10 p) (by rw [hval]; exact hp) (by rw [hval]; exact hnot)
      · intro P hP hsub
        apply hmin
        refine ⟨lval P, mlist_prime _ (pats_mem P hP), ?_, ?_⟩
        · intro he
          exact hnot (he ▸ pats_mem P hP)
        · rw [pats_digits P hP]; exact hsub
      · intro x hx; exact Nat.digits_lt_base (by norm_num) hx
      · intro h; exact Nat.getLast_digit_ne_zero 10 (by rintro rfl; exact Nat.not_prime_zero hp)
    · intro hp
      refine ⟨by norm_num, mlist_prime p hp, ?_⟩
      rintro ⟨q, hq, hqp, hsub⟩
      rw [← pats_val, List.mem_map] at hp
      obtain ⟨P, hP, rfl⟩ := hp
      rw [pats_digits P hP] at hsub
      have hm := minimality
      simp only [List.all_eq_true, List.mem_sublists] at hm
      have h := hm P hP _ hsub
      have hq0 : q ≠ 0 := hq.ne_zero
      have hlq : lval (Nat.digits 10 q) = q := by rw [lval_eq, Nat.ofDigits_digits]
      rw [hlq] at h
      simp only [Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq, decide_eq_true_eq] at h
      rcases h with (((h | h) | h) | h) | h
      · exact Nat.digits_ne_nil_iff_ne_zero.mpr hq0 h
      · have hne : Nat.digits 10 q ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hq0
        rw [List.getLast?_eq_getLast hne] at h
        exact Nat.getLast_digit_ne_zero 10 hq0 (Option.some_injective _ h)
      · exact hqp h
      · exact absurd hq (by intro h'; have := h'.two_le; omega)
      · exact hasFactor_sound _ h hq
  have hs : {p | MinimalPrime.IsMinimalPrimeInBase 10 p} = (mlist.toFinset : Set ℕ) := by
    ext p
    simp only [Set.mem_setOf_eq, key, Finset.mem_coe, List.mem_toFinset]
  rw [hs, Set.ncard_coe_finset]
  decide
