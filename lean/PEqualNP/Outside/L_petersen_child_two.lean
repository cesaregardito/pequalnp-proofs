import Mathlib.Combinatorics.SimpleGraph.Basic

namespace PEqualNP.Outside.L_petersen_child_two

private def edges : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

private def adjacent (v w : Fin 10) : Prop :=
  v ≠ w ∧ ((v.val, w.val) ∈ edges ∨ (w.val, v.val) ∈ edges)

private def rows : List (Finset (Fin 10)) :=
  [{1,4,5}, {0,2,6}, {3,5,6}, {2,4,5,6}, {1,3,7}, {0,3,6,7},
   {4,6,7}, {2,4,8}, {0,7,8}, {1,4,7,8}, {0,3,9}, {2,5,9},
   {1,3,5,9}, {1,8,9}, {0,2,8,9}]

private def rowCoverage (I : Finset (Fin 10)) : Prop :=
    (∀ a ∈ I, ∀ c ∈ I, ¬ adjacent a c) →
    (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, adjacent a w) → I ∈ rows

private def mask (I : Finset (Fin 10)) : ℕ :=
  Nat.ofBits fun i : Fin 10 => decide (i ∈ I)

private theorem maskBit (I : Finset (Fin 10)) (i : Fin 10) :
    (mask I).testBit i.val = decide (i ∈ I) := Nat.testBit_ofBits_lt _ i.val i.isLt

private theorem maskInj {I J : Finset (Fin 10)} (h : mask I = mask J) : I = J := by
  ext i
  have hd := congrArg (fun m : ℕ => m.testBit i.val) h
  rw [maskBit, maskBit] at hd
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp [hI, hJ] at hd ⊢

private def independentB (m : ℕ) : Bool :=
  edges.all fun e => !(m.testBit e.1 && m.testBit e.2)

private def dominatesB (m : ℕ) : Bool :=
  (List.range 10).all fun w => m.testBit w || edges.any (fun e =>
    (decide (e.1 = w) && m.testBit e.2) || (decide (e.2 = w) && m.testBit e.1))

private def numericalRows : List ℕ :=
  [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

private theorem rowMasks : rows.map mask = numericalRows := by
  decide +kernel

private def checkMask (m : ℕ) : Bool :=
  !(independentB m && dominatesB m) || numericalRows.contains m

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkAll : (List.range 1024).all checkMask = true := by
  decide +kernel

private theorem edgeBound : ∀ e ∈ edges, e.1 < 10 ∧ e.2 < 10 ∧ e.1 ≠ e.2 := by
  decide

private theorem indepMask (I : Finset (Fin 10)) (h : ∀ a ∈ I, ∀ b ∈ I, ¬ adjacent a b) :
    independentB (mask I) = true := by
  refine List.all_eq_true.2 ?_
  intro e he
  obtain ⟨h1, h2, hne⟩ := edgeBound e he
  let a : Fin 10 := ⟨e.1, h1⟩
  let b : Fin 10 := ⟨e.2, h2⟩
  have hn : ¬ (a ∈ I ∧ b ∈ I) := by
    rintro ⟨ha, hb⟩
    exact h a ha b hb ⟨fun hab => hne (congrArg Fin.val hab), Or.inl he⟩
  change (!((mask I).testBit a.val && (mask I).testBit b.val)) = true
  rw [maskBit, maskBit]
  by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;> simp [ha, hb] at hn ⊢

private theorem domMask (I : Finset (Fin 10))
    (h : ∀ b : Fin 10, b ∉ I → ∃ a ∈ I, adjacent a b) : dominatesB (mask I) = true := by
  refine List.all_eq_true.2 ?_
  intro w hw
  let b : Fin 10 := ⟨w, List.mem_range.mp hw⟩
  by_cases hb : b ∈ I
  · rw [Bool.or_eq_true]
    exact Or.inl (by simpa [b, hb] using maskBit I b)
  · obtain ⟨a, ha, hadj⟩ := h b hb
    rw [Bool.or_eq_true]
    right
    apply List.any_eq_true.2
    rcases hadj.2 with hab | hba
    · refine ⟨(a.val, b.val), hab, ?_⟩
      have ht : (mask I).testBit a.val = true := by rw [maskBit]; simp [ha]
      simp [b, ht]
    · refine ⟨(b.val, a.val), hba, ?_⟩
      have ht : (mask I).testBit a.val = true := by rw [maskBit]; simp [ha]
      simp [b, ht]

private theorem complete : ∀ I : Finset (Fin 10), rowCoverage I := by
  intro I hi hd
  have hb : mask I < 1024 := Nat.ofBits_lt_two_pow _
  have hc := List.all_eq_true.1 checkAll (mask I) (List.mem_range.2 hb)
  have hm : mask I ∈ numericalRows := by
    simpa [checkMask, indepMask I hi, domMask I hd] using hc
  rw [← rowMasks, List.mem_map] at hm
  obtain ⟨J, hJ, hJI⟩ := hm
  exact maskInj hJI ▸ hJ

end PEqualNP.Outside.L_petersen_child_two

theorem PEqualNP.Outside.L_petersen_child_two :
    let H : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun a b : Fin 10 =>
      ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
        (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ)))
    ∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ H.Adj a c) →
      (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, H.Adj a w) →
      I ∈ ([{1,4,5}, {0,2,6}, {3,5,6}, {2,4,5,6}, {1,3,7}, {0,3,6,7},
        {4,6,7}, {2,4,8}, {0,7,8}, {1,4,7,8}, {0,3,9}, {2,5,9},
        {1,3,5,9}, {1,8,9}, {0,2,8,9}] : List (Finset (Fin 10))) := by
  exact PEqualNP.Outside.L_petersen_child_two.complete
