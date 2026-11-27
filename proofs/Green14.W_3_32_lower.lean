import FormalConjectures.GreensOpenProblems.«14»
import Mathlib.Combinatorics.HalesJewett

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


/-! Certificate formalization for the bounds of Ahmed, Kullmann and Snevily,
https://arxiv.org/abs/1102.5433, Appendix A.
The finite-existence and certificate bridge below are adapted from Dominic
Dabish’s Apache-2.0 Green14 proofs, revision 013a0f04de0057d2bd1034c7cc4caf10ac8dc2cf
of https://github.com/DomTheDeveloper/formal-conjectures. Credit: @Deldor14. -/

open Set
open scoped Classical

namespace Green14

/-- For positive progression lengths, some finite interval forces either a
color-0 progression of length `k` or a color-1 progression of length `r`.

This is deliberately only an existence theorem; its bound is the enormous
Hales--Jewett bound and is not intended for computation. -/
theorem mixedMonoAPGuaranteeSet_nonempty (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    (mixedMonoAPGuaranteeSet k r).Nonempty := by
  classical
  let m := max k r
  obtain ⟨ι, instι, hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin m) (Fin 2)
  let : Fintype ι := instι
  let N := Fintype.card ι * (m - 1) + 1

  have word_sum_le (v : ι → Fin m) :
      ∑ i, (v i : ℕ) ≤ Fintype.card ι * (m - 1) := by
    calc
      ∑ i, (v i : ℕ) ≤ ∑ _i : ι, (m - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.le_pred_of_lt (v i).isLt
      _ = Fintype.card ι * (m - 1) := by simp

  refine ⟨N, ?_⟩
  intro coloring

  let wordPoint (v : ι → Fin m) : Icc 1 N :=
    ⟨1 + ∑ i, (v i : ℕ), by
      constructor
      · omega
      · dsimp only [N]
        have h := word_sum_le v
        omega⟩

  obtain ⟨line, color, hmono⟩ := hι (fun v ↦ coloring (wordPoint v))

  set active : Finset ι := {i | line.idxFun i = none} with hactive
  let a : ℕ := active.card
  let b : ℕ :=
    ∑ i ∈ activeᶜ, ((line.idxFun i).map fun x : Fin m ↦ (x : ℕ)).getD 0

  have ha : 0 < a := by
    apply Finset.card_pos.mpr
    refine ⟨line.proper.choose, ?_⟩
    rw [hactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, line.proper.choose_spec⟩

  have line_sum (x : Fin m) :
      ∑ i, ((line x i : Fin m) : ℕ) = a * (x : ℕ) + b := by
    rw [← Finset.sum_add_sum_compl active]
    congr 1
    · calc
        ∑ i ∈ active, ((line x i : Fin m) : ℕ) =
            ∑ _i ∈ active, (x : ℕ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hnone : line.idxFun i = none := by
            rw [hactive, Finset.mem_filter] at hi
            exact hi.2
          simp [Combinatorics.Line.coe_apply, hnone]
        _ = active.card * (x : ℕ) := by simp
        _ = a * (x : ℕ) := rfl
    · calc
        ∑ i ∈ activeᶜ, ((line x i : Fin m) : ℕ) =
            ∑ i ∈ activeᶜ,
              ((line.idxFun i).map fun y : Fin m ↦ (y : ℕ)).getD 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          cases hopt : line.idxFun i with
          | none =>
              have himem : i ∈ active := by
                rw [hactive, Finset.mem_filter]
                exact ⟨Finset.mem_univ _, hopt⟩
              exact ((Finset.mem_compl.mp hi) himem).elim
          | some y =>
              simp [Combinatorics.Line.coe_apply, hopt]
        _ = b := rfl

  have build_progression (q : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) :
      ∃ s : Finset (Icc 1 N),
        ({(z : ℕ) | z ∈ s}).IsAPOfLength q ∧
          ∀ z ∈ s, coloring z = color := by
    let liftFin : Fin q → Fin m := fun x ↦ Fin.castLE hqm x
    let value : Fin q → ℕ := fun x ↦ a * (x : ℕ) + b + 1
    have hvalue_inj : Function.Injective value := by
      intro x y hxy
      apply Fin.ext
      dsimp only [value] at hxy
      have hmul : a * (x : ℕ) = a * (y : ℕ) := by omega
      exact Nat.eq_of_mul_eq_mul_left ha hmul

    let point : Fin q → Icc 1 N := fun x ↦
      ⟨value x, by
        constructor
        · dsimp only [value]
          omega
        · have hp := (wordPoint (line (liftFin x))).property.2
          dsimp only [wordPoint] at hp
          rw [line_sum] at hp
          simpa [liftFin, value, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp⟩

    have hpoint_inj : Function.Injective point := by
      intro x y hxy
      apply hvalue_inj
      exact Subtype.ext_iff.mp hxy

    let emb : Fin q ↪ Icc 1 N := ⟨point, hpoint_inj⟩
    let s : Finset (Icc 1 N) := Finset.univ.map emb
    let T : Set ℕ := Set.range value

    have hT : T.IsAPOfLengthWith q (b + 1) a := by
      constructor
      · rw [_root_.ENat.card_coe_set_eq]
        have hTrange : T = value '' Set.univ := by
          ext z
          simp [T]
        rw [hTrange, hvalue_inj.encard_image]
        simp
      · ext z
        constructor
        · rintro ⟨x, rfl⟩
          refine ⟨x, ?_, ?_⟩
          · exact_mod_cast x.isLt
          · simp [value, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
        · rintro ⟨n, hn, rfl⟩
          have hnq : n < q := by exact_mod_cast hn
          refine ⟨⟨n, hnq⟩, ?_⟩
          change a * n + b + 1 = b + 1 + n * a
          rw [Nat.mul_comm n a]
          omega

    have hsT : ({(z : ℕ) | z ∈ s} : Set ℕ) = T := by
      ext z
      simp [s, emb, point, T, value]

    refine ⟨s, ?_, ?_⟩
    · rw [hsT]
      exact ⟨b + 1, a, hT⟩
    · intro z hz
      rcases Finset.mem_map.mp hz with ⟨x, -, rfl⟩
      change coloring (point x) = color
      have hpoint_word : point x = wordPoint (line (liftFin x)) := by
        apply Subtype.ext
        dsimp only [point, value, wordPoint]
        rw [line_sum]
        simp [liftFin, Nat.add_comm]
      rw [hpoint_word]
      exact hmono (liftFin x)

  fin_cases color
  · exact Or.inl (build_progression k hk (le_max_left k r))
  · exact Or.inr (build_progression r hr (le_max_right k r))

end Green14

open Set
open scoped Classical

namespace Green14

/-- If an interval forces a mixed monochromatic progression, every larger
interval forces one as well. -/
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
theorem W_ge_succ_of_not_mem (k r N : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf (mixedMonoAPGuaranteeSet_nonempty k r hk hr)
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

end Green14

open Set
open scoped Classical

namespace Green14.FunctionCertificateBridge

/-- Bit i of starts m d j records that i through i+j*d all belong to m. -/
private def starts (m d : Nat) : Nat → Nat
  | 0 => m
  | j+1 => starts m d j &&& (m >>> ((j+1)*d))

private theorem start_bit {m d a j : Nat}
    (h : ∀ i ≤ j, m.testBit (a + i*d) = true) :
    (starts m d j).testBit a = true := by
  induction j with
  | zero => simpa [starts] using h 0 le_rfl
  | succ j ih =>
    simp only [starts, Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true]
    exact ⟨ih fun i hi => h i (Nat.le_succ_of_le hi), by simpa [Nat.add_comm] using h (j+1) le_rfl⟩

private def clear (N k m : Nat) : Bool :=
  (List.range ((N-1)/(k-1))).all fun d => starts m (d+1) (k-1) == 0

private lemma mismatch {N k m : Nat} (hk : 2 ≤ k) (hc : clear N k m = true)
    {a d : Nat} (hd : 0 < d) (he : a + (k-1)*d < N) :
    ∃ i < k, m.testBit (a+i*d) = false := by
  by_contra! h
  have hmul : d*(k-1) ≤ N-1 := by rw [Nat.mul_comm]; omega
  have hle := (Nat.le_div_iff_mul_le (show 0 < k-1 by omega)).mpr hmul
  have hz := List.all_eq_true.mp hc (d-1) (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq, Nat.sub_add_cancel (show 1 ≤ d by omega)] at hz
  have H := start_bit (a := a) (j := k-1) (m := m) (d := d) (by
    intro i hi
    simpa using h i (by omega))
  simp [hz] at H

def boolColor : Bool → Fin 2
  | false => 0
  | true => 1

lemma boolColor_injective : Function.Injective boolColor := by
  intro x y h
  cases x <;> cases y <;> simp_all [boolColor]

def certificateColoring (N : Nat) (coloring : Nat → Bool) : Icc 1 N → Fin 2 :=
  fun x => boolColor (coloring (x.1 - 1))

private lemma mem_coe_finset_set_iff {N : Nat} {s : Finset (Icc 1 N)} {z : Nat} :
    z ∈ ({(x : Nat) | x ∈ s} : Set Nat) ↔ ∃ x ∈ s, (x : Nat) = z := by
  simp

lemma no_monoAP_of_hasAP_eq_false
    {N k mask : Nat} {coloring : Nat → Bool} {color : Bool}
    (hk : 2 ≤ k) (hcheck : clear N k mask = true)
    (hmask : ∀ i < N, coloring i = color → mask.testBit i = true) :
    ¬ ∃ s : Finset (Icc 1 N),
        ({(x : Nat) | x ∈ s}).IsAPOfLength k ∧
          ∀ x ∈ s, certificateColoring N coloring x = boolColor color := by
  rintro ⟨s, hAP, hmono⟩
  rcases hAP with ⟨start, step, hWith⟩
  let T : Set Nat := {(x : Nat) | x ∈ s}
  have hT : T.IsAPOfLengthWith k start step := hWith
  have term_mem (i : Nat) (hi : i < k) : start + i * step ∈ T := by
    rw [hT.2]
    refine ⟨i, ?_, ?_⟩
    · exact_mod_cast hi
    · simp
  have start_mem : start ∈ T := by simpa using term_mem 0 (by omega)
  have last_mem : start + (k - 1) * step ∈ T := term_mem (k - 1) (by omega)
  rcases (mem_coe_finset_set_iff.mp start_mem) with ⟨x0, hx0s, hx0⟩
  rcases (mem_coe_finset_set_iff.mp last_mem) with ⟨xlast, hxlasts, hxlast⟩
  have hstart_lo : 1 ≤ start := by simpa [hx0] using x0.2.1
  have hstart_hi : start ≤ N := by simpa [hx0] using x0.2.2
  have hlast_hi : start + (k - 1) * step ≤ N := by simpa [hxlast] using xlast.2.2
  have hstep_pos : 0 < step := by
    by_contra hnot
    have hstep : step = 0 := Nat.eq_zero_of_not_pos hnot
    have hTsingle : T = {start} := by
      rw [hT.2]
      ext z
      constructor
      · rintro ⟨i, hi, rfl⟩
        simp [hstep]
      · intro hz
        have hz' : z = start := by simpa using hz
        subst z
        refine ⟨0, ?_, by simp [hstep]⟩
        exact_mod_cast (show 0 < k by omega)
    have hcard : (k : ℕ∞) = 1 := by
      rw [← hT.1, hTsingle]
      simp
    have : k = 1 := by exact_mod_cast hcard
    omega
  have hend0 : start - 1 + (k - 1) * step < N := by omega
  obtain ⟨i, hi, hmismatch⟩ :=
    mismatch hk hcheck hstep_pos hend0
  have hiterm : start + i * step ∈ T := term_mem i hi
  rcases (mem_coe_finset_set_iff.mp hiterm) with ⟨x, hxs, hx⟩
  have hxindex : x.1 - 1 = start - 1 + i * step := by
    have hxval : x.1 = start + i * step := hx
    omega
  have hcolor := hmono x hxs
  have hbool : coloring (start - 1 + i * step) = color := by
    apply boolColor_injective
    simpa [certificateColoring, hxindex] using hcolor
  have hbound := Nat.mul_le_mul_right step (show i ≤ k-1 by omega)
  have ht := hmask _ (by omega) hbool
  simp_all

end Green14.FunctionCertificateBridge

open Green14.FunctionCertificateBridge
namespace OMA.GreenCertificate
private def red : Nat := 0x20100000210480000400000020200120000040088002000104001000880002000400000034008800808100c00401000000086004000141002000001200080010100a400000040000102000980001a0040004040000002000401000420220800200014800008082400000800000040002100021001040000008000
private def blue : Nat := (2^1006-1) ^^^ red
private def coloring (i : Nat) : Bool := !(red.testBit i)
end OMA.GreenCertificate

open OMA.GreenCertificate in
theorem OMA.solution : type_of% @Green14.W_3_32_lower := by
  apply Green14.W_ge_succ_of_not_mem 3 32 1006 (by decide) (by decide)
  intro h
  rcases h (certificateColoring 1006 coloring) with hr | hb
  · apply no_monoAP_of_hasAP_eq_false (k := 3) (color := false) (mask := red)
      (by decide) (by decide +kernel) ?_ hr
    intro i _ hi
    simpa [coloring] using hi
  · apply no_monoAP_of_hasAP_eq_false (k := 32) (color := true) (mask := blue)
      (by decide) (by decide +kernel) ?_ hb
    intro i hi hc
    simpa [blue,Nat.testBit_xor,hi,coloring] using hc
