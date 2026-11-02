module

public import HakuiKoyori.PrimitiveMacroRuns

public section

/-!
# Primitive execution semantics for the concrete TR template

This module proves a closed-form, all-input execution theorem for the
literal instruction list emitted by `transferBlock`.  The proof uses
`AssistantMachine.step` through the common primitive interpreter `runN`;
it is not merely a theorem about the abstract arithmetic recurrence.
-/

namespace HakuiKoyori
namespace Compiler

open AssistantMachine

/-- Materialize the emitted TR block as an ordinary M1 program. -/
def concreteTR (m r destination : Nat) : Program :=
  (transferBlock m r (.offset destination)).map
    (relocateInstruction [] 0)

/-- The materialized program is exactly the documented primitive list. -/
theorem concreteTR_eq (m r destination : Nat) :
    concreteTR m r destination =
      [Instruction.decJump Counter.right (3 + r)] ++
        (List.replicate r (Instruction.inc Counter.left) ++
          ([Instruction.inc Counter.left, Instruction.decJump Counter.left destination] ++
            (List.replicate m (Instruction.inc Counter.left) ++
              [Instruction.inc Counter.left, Instruction.decJump Counter.left 0])) ) := by
  simp [concreteTR, transferBlock, identityJump,
    relocateInstruction, resolveTarget, List.append_assoc]

/-- A contiguous block of left-counter increments executes exactly as expected. -/
theorem runN_incLeft_segment
    (program : Program) (base count a b : Nat)
    (hget : ∀ i, i < count →
      program[base + i]? = some (Instruction.inc Counter.left)) :
    runN count program ⟨base, a, b⟩ =
      some ⟨base + count, a + count, b⟩ := by
  induction count generalizing base a with
  | zero =>
      simp [runN]
  | succ count ih =>
      have hfirst : program[base]? = some (Instruction.inc Counter.left) := by
        simpa using hget 0 (by omega)
      have hstep :
          AssistantMachine.step program ⟨base, a, b⟩ =
            some ⟨base + 1, a + 1, b⟩ := by
        simp [AssistantMachine.step, hfirst,
          AssistantMachine.readCounter, AssistantMachine.writeCounter,
          AssistantMachine.setPC]
      simp only [runN]
      rw [hstep]
      have htail : ∀ i, i < count →
          program[(base + 1) + i]? = some (Instruction.inc Counter.left) := by
        intro i hi
        have h := hget (i + 1) (by omega)
        have hindex : (base + 1) + i = base + (i + 1) := by omega
        rw [hindex]
        exact h
      have hrest := ih (base + 1) (a + 1) htail
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- Execute the two-instruction identity jump on the left counter. -/
theorem runN_identityJumpLeft
    (program : Program) (base destination a b : Nat)
    (hfirst : program[base]? = some (Instruction.inc Counter.left))
    (hsecond : program[base + 1]? =
      some (Instruction.decJump Counter.left destination)) :
    runN 2 program ⟨base, a, b⟩ =
      some ⟨destination, a, b⟩ := by
  simp [runN, AssistantMachine.step, hfirst, hsecond,
    AssistantMachine.readCounter, AssistantMachine.writeCounter,
    AssistantMachine.setPC]

/-- The initial TR test consumes one unit of B and jumps to the m-increment loop. -/
theorem concreteTR_positive_entry
    (m r destination a b : Nat) :
    AssistantMachine.step (concreteTR m r destination)
      ⟨0, a, b + 1⟩ =
        some ⟨3 + r, a, b⟩ := by
  rw [concreteTR_eq]
  simp [AssistantMachine.step, AssistantMachine.readCounter,
    AssistantMachine.writeCounter, AssistantMachine.setPC]

/-- The initial TR test falls through when B is zero. -/
theorem concreteTR_zero_entry
    (m r destination a : Nat) :
    AssistantMachine.step (concreteTR m r destination)
      ⟨0, a, 0⟩ = some ⟨1, a, 0⟩ := by
  rw [concreteTR_eq]
  simp [AssistantMachine.step, AssistantMachine.readCounter, AssistantMachine.setPC]

/-- The r-increment remainder segment occupies positions 1 through r. -/
theorem concreteTR_remainder_get
    (m r destination i : Nat) (hi : i < r) :
    (concreteTR m r destination)[1 + i]? =
      some (Instruction.inc Counter.left) := by
  let prefixR : Program := [Instruction.decJump Counter.right (3 + r)]
  have hshape :
      concreteTR m r destination =
        prefixR ++
          (List.replicate r (Instruction.inc Counter.left) ++
            ([Instruction.inc Counter.left, Instruction.decJump Counter.left destination] ++
              (List.replicate m (Instruction.inc Counter.left) ++
                [Instruction.inc Counter.left, Instruction.decJump Counter.left 0]))) := by
    simp [concreteTR, prefixR, transferBlock,
      identityJump, relocateInstruction, resolveTarget]
  have hlength : prefixR.length = 1 := by simp [prefixR]
  have hreplicateLength :
      (List.replicate r (Instruction.inc Counter.left)).length = r := by simp
  rw [hshape]
  change (prefixR ++
    (List.replicate r (Instruction.inc Counter.left) ++
      ([Instruction.inc Counter.left, Instruction.decJump Counter.left destination] ++
        (List.replicate m (Instruction.inc Counter.left) ++
          [Instruction.inc Counter.left, Instruction.decJump Counter.left 0]))))[1 + i]? =
      some (Instruction.inc Counter.left)
  rw [List.getElem?_append_right (l₁ := prefixR) (i := 1 + i)
    (by rw [hlength]; omega)]
  rw [show 1 + i - prefixR.length = i by rw [hlength]; omega]
  rw [List.getElem?_append_left
    (l₁ := List.replicate r (Instruction.inc Counter.left)) (i := i)
    (by rw [hreplicateLength]; exact hi)]
  exact List.getElem?_replicate_of_lt hi

/-- The m-increment transfer segment occupies positions 3+r through 3+r+m-1. -/
theorem concreteTR_transfer_get
    (m r destination i : Nat) (hi : i < m) :
    (concreteTR m r destination)[3 + r + i]? =
      some (Instruction.inc Counter.left) := by
  let prefixM : Program :=
    [Instruction.decJump Counter.right (3 + r)] ++
      (List.replicate r (Instruction.inc Counter.left) ++
        [Instruction.inc Counter.left, Instruction.decJump Counter.left destination])
  have hshape :
      concreteTR m r destination =
        prefixM ++
          (List.replicate m (Instruction.inc Counter.left) ++
            [Instruction.inc Counter.left, Instruction.decJump Counter.left 0]) := by
    simp [concreteTR, prefixM, transferBlock,
      identityJump, relocateInstruction, resolveTarget]
  have hlength : prefixM.length = 3 + r := by
    simp only [prefixM, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate]
    omega
  have hreplicateLength :
      (List.replicate m (Instruction.inc Counter.left)).length = m := by simp
  rw [hshape]
  change (prefixM ++
    (List.replicate m (Instruction.inc Counter.left) ++
      [Instruction.inc Counter.left, Instruction.decJump Counter.left 0]))[3 + r + i]? =
      some (Instruction.inc Counter.left)
  rw [List.getElem?_append_right (l₁ := prefixM) (i := 3 + r + i)
    (by rw [hlength]; omega)]
  rw [show 3 + r + i - prefixM.length = i by rw [hlength]; omega]
  rw [List.getElem?_append_left
    (l₁ := List.replicate m (Instruction.inc Counter.left)) (i := i)
    (by rw [hreplicateLength]; exact hi)]
  exact List.getElem?_replicate_of_lt hi

/-- The remainder identity jump starts immediately after the r increments. -/
theorem concreteTR_remainder_jump_get
    (m r destination : Nat) :
    (concreteTR m r destination)[1 + r]? = some (Instruction.inc Counter.left) ∧
    (concreteTR m r destination)[1 + r + 1]? =
      some (Instruction.decJump Counter.left destination) := by
  let prefixR : Program :=
    [Instruction.decJump Counter.right (3 + r)] ++ List.replicate r (Instruction.inc Counter.left)
  have hshape :
      concreteTR m r destination =
        prefixR ++
          ([Instruction.inc Counter.left, Instruction.decJump Counter.left destination] ++
            (List.replicate m (Instruction.inc Counter.left) ++
              [Instruction.inc Counter.left, Instruction.decJump Counter.left 0])) := by
    simp [concreteTR, prefixR, transferBlock,
      identityJump, relocateInstruction, resolveTarget]
  have hlength : prefixR.length = 1 + r := by
    simp [prefixR] <;> omega
  constructor
  · rw [hshape]
    change (prefixR ++
      ([Instruction.inc Counter.left, Instruction.decJump Counter.left destination] ++
        (List.replicate m (Instruction.inc Counter.left) ++
          [Instruction.inc Counter.left, Instruction.decJump Counter.left 0])))[1 + r]? =
        some (Instruction.inc Counter.left)
    rw [List.getElem?_append_right (l₁ := prefixR) (i := 1 + r)
      (by rw [hlength]; omega)]
    rw [show 1 + r - prefixR.length = 0 by rw [hlength]; omega]
    rfl
  · rw [hshape]
    change (prefixR ++
      ([Instruction.inc Counter.left, Instruction.decJump Counter.left destination] ++
        (List.replicate m (Instruction.inc Counter.left) ++
          [Instruction.inc Counter.left, Instruction.decJump Counter.left 0])))[1 + r + 1]? =
        some (Instruction.decJump Counter.left destination)
    rw [List.getElem?_append_right (l₁ := prefixR) (i := 1 + r + 1)
      (by rw [hlength]; omega)]
    rw [show 1 + r + 1 - prefixR.length = 1 by rw [hlength]; omega]
    rfl

/-- The final identity jump returns from the m-transfer loop to PC zero. -/
theorem concreteTR_final_jump_get
    (m r destination : Nat) :
    (concreteTR m r destination)[3 + r + m]? =
      some (Instruction.inc Counter.left) ∧
    (concreteTR m r destination)[3 + r + m + 1]? =
      some (Instruction.decJump Counter.left 0) := by
  let prefixEnd : Program :=
    [Instruction.decJump Counter.right (3 + r)] ++
      (List.replicate r (Instruction.inc Counter.left) ++
        ([Instruction.inc Counter.left, Instruction.decJump Counter.left destination] ++
          List.replicate m (Instruction.inc Counter.left)))
  have hshape :
      concreteTR m r destination =
        prefixEnd ++ [Instruction.inc Counter.left, Instruction.decJump Counter.left 0] := by
    simp [concreteTR, prefixEnd, transferBlock,
      identityJump, relocateInstruction, resolveTarget]
  have hlength : prefixEnd.length = 3 + r + m := by
    simp only [prefixEnd, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate] <;> omega
  constructor
  · rw [hshape]
    change (prefixEnd ++ [Instruction.inc Counter.left, Instruction.decJump Counter.left 0])
      [3 + r + m]? = some (Instruction.inc Counter.left)
    rw [List.getElem?_append_right (l₁ := prefixEnd)
      (i := 3 + r + m) (by rw [hlength]; omega)]
    rw [show 3 + r + m - prefixEnd.length = 0 by rw [hlength]; omega]
    rfl
  · rw [hshape]
    change (prefixEnd ++ [Instruction.inc Counter.left, Instruction.decJump Counter.left 0])
      [3 + r + m + 1]? = some (Instruction.decJump Counter.left 0)
    rw [List.getElem?_append_right (l₁ := prefixEnd)
      (i := 3 + r + m + 1) (by rw [hlength]; omega)]
    rw [show 3 + r + m + 1 - prefixEnd.length = 1 by rw [hlength]; omega]
    rfl

/-- One positive-B loop round of the literal TR code adds m to A and consumes one B. -/
theorem concreteTR_positive_round
    (m r destination a b : Nat) :
    runN (m + 3) (concreteTR m r destination)
      ⟨0, a, b + 1⟩ =
        some ⟨0, a + m, b⟩ := by
  have hfirst :
      runN 1 (concreteTR m r destination) ⟨0, a, b + 1⟩ =
        some ⟨3 + r, a, b⟩ := by
    simp [runN, concreteTR_positive_entry]
  have hbody :
      runN m (concreteTR m r destination)
        ⟨3 + r, a, b⟩ =
          some ⟨3 + r + m, a + m, b⟩ := by
    exact runN_incLeft_segment (concreteTR m r destination)
      (3 + r) m a b
      (fun i hi => concreteTR_transfer_get m r destination i hi)
  obtain ⟨hjump₁, hjump₂⟩ :=
    concreteTR_final_jump_get m r destination
  have htail :
      runN 2 (concreteTR m r destination)
        ⟨3 + r + m, a + m, b⟩ =
          some ⟨0, a + m, b⟩ := by
    exact runN_identityJumpLeft (concreteTR m r destination)
      (3 + r + m) 0 (a + m) b hjump₁
      (by
        convert hjump₂ using 1 <;> congr 1 <;> omega)
  calc
    runN (m + 3) (concreteTR m r destination)
        ⟨0, a, b + 1⟩ =
      runN (1 + (m + 2)) (concreteTR m r destination)
        ⟨0, a, b + 1⟩ := by congr 1 <;> omega
    _ =
      (runN 1 (concreteTR m r destination) ⟨0, a, b + 1⟩).bind
        (fun middle => runN (m + 2)
          (concreteTR m r destination) middle) :=
        runN_add 1 (m + 2) _ _
    _ = runN (m + 2) (concreteTR m r destination)
          ⟨3 + r, a, b⟩ := by simp [hfirst]
    _ =
      (runN m (concreteTR m r destination)
        ⟨3 + r, a, b⟩).bind
        (fun middle => runN 2 (concreteTR m r destination) middle) :=
        runN_add m 2 _ _
    _ = some ⟨0, a + m, b⟩ := by simp [hbody, htail]

/-- Repeated positive rounds consume all q units of B. -/
theorem concreteTR_outer_loop
    (m r destination a q : Nat) :
    runN (q * (m + 3)) (concreteTR m r destination)
      ⟨0, a, q⟩ =
        some ⟨0, a + m * q, 0⟩ := by
  induction q generalizing a with
  | zero =>
      simp [runN]
  | succ q ih =>
      have hround := concreteTR_positive_round m r destination a q
      have hrest := ih (a + m)
      have hcount : (q + 1) * (m + 3) =
          (m + 3) + q * (m + 3) := by ring
      calc
        runN ((q + 1) * (m + 3)) (concreteTR m r destination)
            ⟨0, a, q + 1⟩ =
          (runN (m + 3) (concreteTR m r destination)
              ⟨0, a, q + 1⟩).bind
            (fun middle => runN (q * (m + 3))
              (concreteTR m r destination) middle) := by
                rw [hcount]
                exact runN_add (m + 3) (q * (m + 3))
                  (concreteTR m r destination) ⟨0, a, q + 1⟩
        _ = runN (q * (m + 3)) (concreteTR m r destination)
              ⟨0, a + m, q⟩ := by simp [hround]
        _ = some ⟨0, a + m + m * q, 0⟩ := hrest
        _ = some ⟨0, a + m * (q + 1), 0⟩ := by
              simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The zero-B branch adds the finite residue r and exits at destination. -/
theorem concreteTR_remainder_run
    (m r destination a : Nat) :
    runN (r + 3) (concreteTR m r destination)
      ⟨0, a, 0⟩ =
        some ⟨destination, a + r, 0⟩ := by
  have hfirst :
      runN 1 (concreteTR m r destination) ⟨0, a, 0⟩ =
        some ⟨1, a, 0⟩ := by
    simp [runN, concreteTR_zero_entry]
  have hbody :
      runN r (concreteTR m r destination) ⟨1, a, 0⟩ =
        some ⟨1 + r, a + r, 0⟩ := by
    exact runN_incLeft_segment (concreteTR m r destination)
      1 r a 0 (fun i hi => concreteTR_remainder_get m r destination i hi)
  obtain ⟨hjump₁, hjump₂⟩ :=
    concreteTR_remainder_jump_get m r destination
  have htail :
      runN 2 (concreteTR m r destination)
        ⟨1 + r, a + r, 0⟩ =
          some ⟨destination, a + r, 0⟩ := by
    exact runN_identityJumpLeft (concreteTR m r destination)
      (1 + r) destination (a + r) 0 hjump₁
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hjump₂)
  calc
    runN (r + 3) (concreteTR m r destination) ⟨0, a, 0⟩ =
      runN (1 + (r + 2)) (concreteTR m r destination)
        ⟨0, a, 0⟩ := by congr 1 <;> omega
    _ =
      (runN 1 (concreteTR m r destination) ⟨0, a, 0⟩).bind
        (fun middle => runN (r + 2) (concreteTR m r destination) middle) :=
        runN_add 1 (r + 2) _ _
    _ = runN (r + 2) (concreteTR m r destination)
          ⟨1, a, 0⟩ := by simp [hfirst]
    _ =
      (runN r (concreteTR m r destination) ⟨1, a, 0⟩).bind
        (fun middle => runN 2 (concreteTR m r destination) middle) :=
        runN_add r 2 _ _
    _ = some ⟨destination, a + r, 0⟩ := by simp [hbody, htail]

/-- All-input primitive correctness and exact cost of the emitted TR block. -/
theorem concreteTR_correct_run
    (m r destination a q : Nat) :
    runN (q * (m + 3) + r + 3) (concreteTR m r destination)
      ⟨0, a, q⟩ =
        some ⟨destination, a + m * q + r, 0⟩ := by
  have houter := concreteTR_outer_loop m r destination a q
  have htail := concreteTR_remainder_run m r destination (a + m * q)
  have hcount :
      q * (m + 3) + r + 3 =
        q * (m + 3) + (r + 3) := by omega
  calc
    runN (q * (m + 3) + r + 3) (concreteTR m r destination)
        ⟨0, a, q⟩ =
      (runN (q * (m + 3)) (concreteTR m r destination)
          ⟨0, a, q⟩).bind
        (fun middle => runN (r + 3) (concreteTR m r destination) middle) := by
          rw [hcount]
          exact runN_add (q * (m + 3)) (r + 3)
            (concreteTR m r destination) ⟨0, a, q⟩
    _ = some ⟨destination, a + m * q + r, 0⟩ := by
          simp [houter, htail]

end Compiler
end HakuiKoyori
