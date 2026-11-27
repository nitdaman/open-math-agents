import FormalConjectures.GreensOpenProblems.«14»

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# Exact mixed van der Waerden number W(3,11)

The lower bound is certified by the explicit 113-bit coloring checked below.
For the upper bound, look outward from the two middle positions of a 114-bit
coloring. Eleven consecutive blue positions already give the required progression,
so some red position is among the central twelve. Reflection lets us put the
nearest red on the left. The three finite hypotheses partition its six possible
distances from the middle. Indices in these hypotheses start at zero, and
`true` denotes red. Every progression in the hypotheses lies inside the interval.

The order and arithmetic-progression lemmas are adapted from Dominic Dabish’s
Apache-2.0 proof of W(3,9), open-math-agents PR 591. The new coloring, reflection
argument and subproblem partition are by @Halldon.
-/

open Set Green14
open scoped Classical

namespace OMA.R_Green14_W_3_11_R1

def H1 : Prop :=
  ∀ r : Fin 114 → Bool, ∀ j : Fin 6, 0 ≤ j.val → j.val ≤ 1 →
    r (Fin.ofNat 114 (56 - j.val)) = true →
    (∀ i : Fin 114, 56 - j.val < i.val → i.val < 57 + j.val → r i = false) →
    ∃ (b : Bool) (a d : Fin 114), 0 < d.val ∧ a.val + (if b then 2 else 10) * d.val < 114 ∧
      ∀ t : Fin 11, t.val ≤ (if b then 2 else 10) → r (Fin.ofNat 114 (a.val + t.val * d.val)) = b

def H2 : Prop :=
  ∀ r : Fin 114 → Bool, ∀ j : Fin 6, 2 ≤ j.val → j.val ≤ 3 →
    r (Fin.ofNat 114 (56 - j.val)) = true →
    (∀ i : Fin 114, 56 - j.val < i.val → i.val < 57 + j.val → r i = false) →
    ∃ (b : Bool) (a d : Fin 114), 0 < d.val ∧ a.val + (if b then 2 else 10) * d.val < 114 ∧
      ∀ t : Fin 11, t.val ≤ (if b then 2 else 10) → r (Fin.ofNat 114 (a.val + t.val * d.val)) = b

def H3 : Prop :=
  ∀ r : Fin 114 → Bool, ∀ j : Fin 6, 4 ≤ j.val → j.val ≤ 5 →
    r (Fin.ofNat 114 (56 - j.val)) = true →
    (∀ i : Fin 114, 56 - j.val < i.val → i.val < 57 + j.val → r i = false) →
    ∃ (b : Bool) (a d : Fin 114), 0 < d.val ∧ a.val + (if b then 2 else 10) * d.val < 114 ∧
      ∀ t : Fin 11, t.val ≤ (if b then 2 else 10) → r (Fin.ofNat 114 (a.val + t.val * d.val)) = b

theorem mixedMonoAPGuaranteeSet_upward (k r : ℕ) {M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ mixedMonoAPGuaranteeSet k r) :
    N ∈ mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let emb : Icc 1 M ↪ Icc 1 N :=
    ⟨fun x ↦ ⟨x, x.2.1, x.2.2.trans hMN⟩, by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Icc 1 N ↦ (z : Nat)) h⟩
  let restricted : Icc 1 M → Fin 2 := fun x ↦ coloring (emb x)
  rcases hM restricted with hzero | hone
  · left
    rcases hzero with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy
  · right
    rcases hone with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy

/-- One bad coloring of `{1, ..., N}` proves the numerical lower bound
`W(k,r) ≥ N+1`. -/
private theorem W_ge_succ_of_not_mem (k r N : ℕ)
    (hne : (mixedMonoAPGuaranteeSet k r).Nonempty) (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf hne
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

private lemma progression_at {N k a d : Nat} (hd : 0 < d)
    (c : Icc 1 N → Fin 2) (color : Fin 2)
    (bound : ∀ i : Fin k, a+i.val*d < N)
    (mono : ∀ (i : Fin k) (hi : a+i.val*d < N), c ⟨a+i.val*d+1, by constructor <;> omega⟩ = color) :
    ∃ s : Finset (Icc 1 N), ({(z : Nat) | z ∈ s}).IsAPOfLength k ∧
      ∀ z ∈ s, c z = color := by
  classical
  let value (i : Fin k) := a + i.val*d + 1
  have inj : Function.Injective value := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (by simpa [value] using h)
  let point : Fin k ↪ Icc 1 N := ⟨fun i => ⟨value i, by
    have := bound i
    dsimp [value]
    constructor <;> omega⟩, fun i j h => inj (congrArg Subtype.val h)⟩
  let s := Finset.univ.map point
  have eqs : ({(z : Nat) | z ∈ s} : Set Nat) = range value := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨point i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨s, ?_, ?_⟩
  · rw [eqs]
    refine ⟨a+1,d,?_,?_⟩
    · rw [ENat.card_coe_set_eq, ← Set.image_univ, inj.encard_image]
      simp
    · ext z
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨i.val,by exact_mod_cast i.isLt,by simp [value]; omega⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,by exact_mod_cast hi⟩,by simp [value]; omega⟩
  · intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hz
    exact mono i (bound i)


private lemma extract_progression {N k : ℕ} (hk : 2 ≤ k) (q : ℕ → Fin 2) (col : Fin 2)
    (h : ∃ s : Finset (Icc 1 N), ({(x : ℕ) | x ∈ s}).IsAPOfLength k ∧
      ∀ x ∈ s, q (x.val-1) = col) :
    ∃ a d : Fin N, 0 < d.val ∧ a.val + (k-1)*d.val < N ∧
      ∀ i : Fin k, q (a.val + i.val*d.val) = col := by
  obtain ⟨s,⟨a,d,hcard,hset⟩,hc⟩ := h
  have term (i : ℕ) (hi : i < k) :
      ∃ x ∈ s, (x : ℕ) = a + i*d := by
    change a + i*d ∈ ({(x : ℕ) | x ∈ s} : Set ℕ)
    rw [hset]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  obtain ⟨x₀, -, hx₀⟩ := term 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero] at hx₀
  obtain ⟨x₁, -, hx₁⟩ := term (k-1) (by omega)
  have ha : 1 ≤ a := hx₀ ▸ x₀.property.1
  have hb : a + (k-1)*d ≤ N := hx₁ ▸ x₁.property.2
  have hpos : 0 < d := by
    by_contra! hz
    have hd : d = 0 := by omega
    have heq : ({(x : ℕ) | x ∈ s} : Set ℕ) = {a} := by
      rw [hset]
      ext z
      simp only [hd, nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,hi,rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, by exact_mod_cast (show 0 < k by omega), rfl⟩
    have hone : (k : ℕ∞) = 1 := by rw [← hcard, heq]; simp
    have : k = 1 := by exact_mod_cast hone
    omega
  have hd' : d ≤ (k-1)*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k-1 by omega)
  refine ⟨⟨a-1,by omega⟩,⟨d,by omega⟩,hpos,by change a-1+(k-1)*d < N; omega,?_⟩
  intro i
  obtain ⟨x,hx,hval⟩ := term i.val i.isLt
  have he := hc x hx
  change q (a - 1 + i.val*d) = col
  convert he using 2 <;> omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem lower_witness : 113 ∉ mixedMonoAPGuaranteeSet 3 11 := by
  let q (i : ℕ) : Fin 2 := if (0x20218100260081401b0020600400 : ℕ).testBit i then 0 else 1
  have red : ∀ a d : Fin 113, 0 < d.val → a.val + 2*d.val < 113 →
      ¬ ∀ i : Fin 3, q (a.val + i.val*d.val) = 0 := by decide +kernel
  have blue : ∀ a d : Fin 113, 0 < d.val → a.val + 10*d.val < 113 →
      ¬ ∀ i : Fin 11, q (a.val + i.val*d.val) = 1 := by decide +kernel
  intro h
  rcases h (fun x => q (x.val-1)) with hr | hb
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 3) q 0 hr
    exact red a d hd hbound hc
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 11) q 1 hb
    exact blue a d hd hbound hc

private lemma idx_val (i : ℕ) (hi : i < 114) : (Fin.ofNat 114 i).val = i :=
  Nat.mod_eq_of_lt hi

private lemma some_progression (h₁ : H1) (h₂ : H2) (h₃ : H3) (r : Fin 114 → Bool) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 10)*d < 114 ∧
      ∀ t ≤ (if b then 2 else 10), r (Fin.ofNat 114 (a+t*d)) = b := by
  let Good (s : Fin 114 → Bool) := ∃ (b : Bool) (a d : ℕ),
    0 < d ∧ a + (if b then 2 else 10)*d < 114 ∧
      ∀ t ≤ (if b then 2 else 10), s (Fin.ofNat 114 (a+t*d)) = b
  have normal (s : Fin 114 → Bool) (j : ℕ) (hj : j ≤ 5)
      (hr : s (Fin.ofNat 114 (56-j)) = true)
      (hb : ∀ i : Fin 114, 56-j < i.val → i.val < 57+j → s i = false) : Good s := by
    let k : Fin 6 := ⟨j,by omega⟩
    have hc : ∃ (b : Bool) (a d : Fin 114), 0 < d.val ∧
        a.val + (if b then 2 else 10)*d.val < 114 ∧
        ∀ t : Fin 11, t.val ≤ (if b then 2 else 10) →
          s (Fin.ofNat 114 (a.val+t.val*d.val)) = b := by
      by_cases h : j ≤ 1
      · exact h₁ s k (Nat.zero_le j) h hr hb
      by_cases h' : j ≤ 3
      · exact h₂ s k (show 2 ≤ j by omega) h' hr hb
      exact h₃ s k (show 4 ≤ j by omega) hj hr hb
    obtain ⟨b,a,d,hd,he,hm⟩ := hc
    refine ⟨b,a.val,d.val,hd,he,?_⟩
    intro t ht
    have hL : (if b then 2 else 10 : ℕ) ≤ 10 := by cases b <;> decide
    exact hm ⟨t,by omega⟩ ht
  let P (j : ℕ) := j ≤ 5 ∧
    (r (Fin.ofNat 114 (56-j)) = true ∨ r (Fin.ofNat 114 (57+j)) = true)
  by_cases h : ∃ j, P j
  · let j := Nat.find h
    obtain ⟨hj, hred⟩ := Nat.find_spec h
    change j ≤ 5 at hj
    have blue (i : ℕ) (hi : 56-j < i) (hi' : i < 57+j) :
        r (Fin.ofNat 114 i) = false := by
      by_contra! hh
      by_cases left : i ≤ 56
      · have heq : 56 - (56-i) = i := by omega
        have hp : P (56-i) := ⟨by omega,Or.inl (by simpa [heq] using hh)⟩
        have := Nat.find_min' h hp
        change j ≤ 56-i at this
        omega
      · have heq : 57 + (i-57) = i := by omega
        have hp : P (i-57) := ⟨by omega,Or.inr (by simpa [heq] using hh)⟩
        have := Nat.find_min' h hp
        change j ≤ i-57 at this
        omega
    rcases hred with left | right
    · apply normal r j hj left
      intro i hi hi'
      simpa using blue i.val hi hi'
    · let flip (i : Fin 114) := r (Fin.ofNat 114 (113-i.val))
      have hf : flip (Fin.ofNat 114 (56-j)) = true := by
        dsimp only [flip]
        rw [idx_val _ (by omega), show 113-(56-j) = 57+j by omega]
        exact right
      have hb (i : Fin 114) (hl : 56-j < i.val) (hr : i.val < 57+j) : flip i = false :=
        blue _ (by omega) (by omega)
      obtain ⟨b,a,d,hd,he,hm⟩ := normal flip j hj hf hb
      let L : ℕ := if b then 2 else 10
      change a + L*d < 114 at he
      change ∀ t ≤ L, flip (Fin.ofNat 114 (a+t*d)) = b at hm
      refine ⟨b,113-(a+L*d),d,hd,by change 113-(a+L*d)+L*d < 114; omega,?_⟩
      intro t ht
      change t ≤ L at ht
      have hh := hm (L-t) (by omega)
      dsimp only [flip] at hh
      have hmul := Nat.mul_le_mul_right d ht
      rw [Nat.sub_mul,idx_val _ (by omega)] at hh
      simpa only [show 113-(a+(L*d-t*d)) = 113-(a+L*d)+t*d by omega] using hh
  · refine ⟨false,51,1,by decide,by decide,?_⟩
    intro t ht
    change t ≤ 10 at ht
    by_contra! hh
    have hh : r (Fin.ofNat 114 (51+t*1)) = true := by simpa using hh
    by_cases left : t ≤ 5
    · have heq : 56-(5-t) = 51+t*1 := by omega
      exact h ⟨5-t,by omega,Or.inl (by simpa only [heq] using hh)⟩
    · have heq : 57+(t-6) = 51+t*1 := by omega
      exact h ⟨t-6,by omega,Or.inr (by simpa only [heq] using hh)⟩

theorem main : H1 → H2 → H3 → type_of% @Green14.W_3_11 := by
  intro h₁ h₂ h₃
  have upper : 114 ∈ mixedMonoAPGuaranteeSet 3 11 := by
    intro c
    let r (i : Fin 114) := decide (c ⟨i.val+1, by constructor <;> omega⟩ = 0)
    obtain ⟨b,a,d,hd,he,hm⟩ := some_progression h₁ h₂ h₃ r
    cases b
    · right
      apply progression_at (a := a) hd c 1
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 10 by omega)
        simp only [Bool.false_eq_true,if_false] at he
        omega
      · intro i hi
        have hh := hm i.val (by change i.val ≤ 10; omega)
        have hx : Fin.ofNat 114 (a+i.val*d) = ⟨a+i.val*d,hi⟩ := Fin.ext (idx_val _ hi)
        rw [hx] at hh
        dsimp only [r] at hh
        have hv : c ⟨a+i.val*d+1,by constructor <;> omega⟩ ≠ 0 := of_decide_eq_false hh
        exact (show ∀ x : Fin 2, x ≠ 0 → x = 1 by decide) _ hv
    · left
      apply progression_at (a := a) hd c 0
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 2 by omega)
        simp only [if_true] at he
        omega
      · intro i hi
        have hh := hm i.val (by change i.val ≤ 2; omega)
        have hx : Fin.ofNat 114 (a+i.val*d) = ⟨a+i.val*d,hi⟩ := Fin.ext (idx_val _ hi)
        rw [hx] at hh
        dsimp only [r] at hh
        exact of_decide_eq_true hh
  exact le_antisymm (Nat.sInf_le upper)
    (W_ge_succ_of_not_mem 3 11 113 ⟨114,upper⟩ lower_witness)

end OMA.R_Green14_W_3_11_R1
