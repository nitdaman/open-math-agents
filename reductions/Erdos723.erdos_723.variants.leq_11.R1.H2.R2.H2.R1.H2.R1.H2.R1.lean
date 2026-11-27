import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1

/-! Split the indexed star search into intervals of the least attainable first partition. -/
-- Credit: @avivorly

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1

-- List the possible stars of the first group by pairing the highest remaining vertex.
-- The first partition is represented by the bits at the indices of its stars in that list.

def H1 : Prop :=
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  ¬ ∃ s, valid s ∧ (∀ t, valid t → key s ≤ key t) ∧ key s ≤ 0x1001000000000000000000020000000000000010000000040000000000080000000000000

def H2 : Prop :=
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  ¬ ∃ s, valid s ∧ (∀ t, valid t → key s ≤ key t) ∧ 0x1001000000000000000000020000000000000010000000040000000000080000000000000 < key s ∧ key s ≤ 0x4000000000800000000001000000000400000000000000000000200000002000000000000

def H3 : Prop :=
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  ¬ ∃ s, valid s ∧ (∀ t, valid t → key s ≤ key t) ∧ 0x4000000000800000000001000000000400000000000000000000200000002000000000000 < key s ∧ key s ≤ 0x8000100000000000000800000000001000000000000000000000100000000000000010000

def H4 : Prop :=
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  ¬ ∃ s, valid s ∧ (∀ t, valid t → key s ≤ key t) ∧ 0x8000100000000000000800000000001000000000000000000000100000000000000010000 < key s

lemma row_bit (table width row column : Nat) (inside : column < width) :
    (((table >>> (width*row)) &&& (2^width-1)).testBit column) =
      table.testBit (width*row+column) := by
  simp only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true inside, Bool.and_true, Nat.add_comm]

lemma minimum_key {α : Type} (valid : α → Prop) (key : α → Nat) (witness : α)
    (hw : valid witness) : ∃ s, valid s ∧ ∀ t, valid t → key s ≤ key t := by
  classical
  let attained (n : Nat) := ∃ s, valid s ∧ key s = n
  have some_key : ∃ n, attained n := ⟨key witness, witness, hw, rfl⟩
  obtain ⟨s, good, least⟩ := Nat.find_spec some_key
  refine ⟨s, good, fun t ht => ?_⟩
  rw [least]
  exact Nat.find_min' some_key ⟨t, ht, rfl⟩

set_option maxRecDepth 15000 in
theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1.H2 := by
  intro low lower upper high
  rintro ⟨s, incidence, pairs, partition, intersections⟩
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  have endpoint_exact (p : Fin 60) (m : Fin 15) : (endpoints p).testBit m.val =
      (0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat).testBit (15*p.val+m.val) := row_bit _ 15 p.val m.val m.isLt
  have witness : valid s := by
    refine ⟨incidence, ?_, partition, intersections⟩
    intro g i m needed
    simpa only [endpoint_exact] using pairs g i m needed
  change ¬ ∃ x, valid x ∧ (∀ t, valid t → key x ≤ key t) ∧ key x ≤ 0x1001000000000000000000020000000000000010000000040000000000080000000000000 at low
  change ¬ ∃ x, valid x ∧ (∀ t, valid t → key x ≤ key t) ∧
    0x1001000000000000000000020000000000000010000000040000000000080000000000000 < key x ∧ key x ≤ 0x4000000000800000000001000000000400000000000000000000200000002000000000000 at lower
  change ¬ ∃ x, valid x ∧ (∀ t, valid t → key x ≤ key t) ∧
    0x4000000000800000000001000000000400000000000000000000200000002000000000000 < key x ∧ key x ≤ 0x8000100000000000000800000000001000000000000000000000100000000000000010000 at upper
  change ¬ ∃ x, valid x ∧ (∀ t, valid t → key x ≤ key t) ∧ 0x8000100000000000000800000000001000000000000000000000100000000000000010000 < key x at high
  obtain ⟨best, good, minimal⟩ := minimum_key valid key s witness
  by_cases lower_than_first : key best ≤ 0x1001000000000000000000020000000000000010000000040000000000080000000000000
  · exact low ⟨best, good, minimal, lower_than_first⟩
  by_cases lower_than_second : key best ≤ 0x4000000000800000000001000000000400000000000000000000200000002000000000000
  · exact lower ⟨best, good, minimal, Nat.lt_of_not_ge lower_than_first, lower_than_second⟩
  by_cases lower_than_third : key best ≤ 0x8000100000000000000800000000001000000000000000000000100000000000000010000
  · exact upper ⟨best, good, minimal, Nat.lt_of_not_ge lower_than_second, lower_than_third⟩
  exact high ⟨best, good, minimal, Nat.lt_of_not_ge lower_than_third⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1
