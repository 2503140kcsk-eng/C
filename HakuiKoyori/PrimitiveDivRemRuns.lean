module

public import HakuiKoyori.PrimitiveTransferRuns

public section

/-!
# Concrete terminal execution for the DIVREM generator

The quotient/remainder generator ends in a three-instruction loop-back tail.
This file proves that the literal relocated tail executes exactly as intended
inside an arbitrary pre/suffix context of the target program.
-/

namespace HakuiKoyori
namespace Compiler

open AssistantMachine

/-- Lookup in a middle list segment, at its absolute index after a pre. -/
theorem getElem?_middle
    (pre middle suffix : Program) (i : Nat)
    (hi : i < middle.length) :
    (pre ++ (middle ++ suffix))[pre.length + i]? = middle[i]? := by
  rw [List.getElem?_append_right
    (l₁ := pre) (l₂ := middle ++ suffix)
    (i := pre.length + i) (by omega)]
  have hindex : pre.length + i - pre.length = i := by omega
  rw [hindex]
  exact List.getElem?_append_left
    (l₁ := middle) (l₂ := suffix) (i := i) hi

/-- Two increments and a positive decrement-jump loop back to the root PC. -/
theorem runN_right_loop_segment
    (pre suffix : Program) (root a b : Nat) :
    runN 3
      (pre ++
        ([Instruction.inc .right, Instruction.inc .right,
          Instruction.decJump .right root] ++ suffix))
      ⟨pre.length, a, b⟩ =
      some ⟨root, a, b + 1⟩ := by
  let middle : Program :=
    [Instruction.inc .right, Instruction.inc .right,
      Instruction.decJump .right root]
  have h0 :
      (pre ++ (middle ++ suffix))[pre.length]? =
        some (Instruction.inc .right) := by
    simpa [middle] using
      (getElem?_middle pre middle suffix 0 (by simp [middle]))
  have h1 :
      (pre ++ (middle ++ suffix))[pre.length + 1]? =
        some (Instruction.inc .right) := by
    simpa [middle] using
      (getElem?_middle pre middle suffix 1 (by simp [middle]))
  have h2 :
      (pre ++ (middle ++ suffix))[pre.length + 2]? =
        some (Instruction.decJump .right root) := by
    simpa [middle] using
      (getElem?_middle pre middle suffix 2 (by simp [middle]))
  have hs0 :
      AssistantMachine.step (pre ++ (middle ++ suffix))
        ⟨pre.length, a, b⟩ =
        some ⟨pre.length + 1, a, b + 1⟩ := by
    simp [AssistantMachine.step, h0, AssistantMachine.readCounter,
      AssistantMachine.writeCounter, AssistantMachine.setPC]
  have hs1 :
      AssistantMachine.step (pre ++ (middle ++ suffix))
        ⟨pre.length + 1, a, b + 1⟩ =
        some ⟨pre.length + 2, a, b + 2⟩ := by
    simp [AssistantMachine.step, h1, AssistantMachine.readCounter,
      AssistantMachine.writeCounter, AssistantMachine.setPC]
  have hs2 :
      AssistantMachine.step (pre ++ (middle ++ suffix))
        ⟨pre.length + 2, a, b + 2⟩ =
        some ⟨root, a, b + 1⟩ := by
    simp [AssistantMachine.step, h2, AssistantMachine.readCounter,
      AssistantMachine.writeCounter, AssistantMachine.setPC]
  calc
    runN 3 (pre ++ (middle ++ suffix)) ⟨pre.length, a, b⟩ =
        (runN 1 (pre ++ (middle ++ suffix)) ⟨pre.length, a, b⟩).bind
          (fun next => runN 2 (pre ++ (middle ++ suffix)) next) := by
            simpa using runN_add 1 2 (pre ++ (middle ++ suffix))
              ⟨pre.length, a, b⟩
    _ = some ⟨root, a, b + 1⟩ := by
      simp [runN, hs0, hs1, hs2]

/-- At every nested offset, relocation leaves the DIVREM loop-back at root. -/
theorem divRemAux_terminal_code
    (blocks : List TemplateBlock) (root offset p residue : Nat)
    (destinationDiv destinationNondiv : JumpTarget) :
    (rebaseBlock offset
      (divRemAux p destinationDiv destinationNondiv 0 residue)).map
        (relocateInstruction blocks root) =
      [Instruction.inc .right, Instruction.inc .right,
        Instruction.decJump .right root] := by
  simp [divRemAux, rebaseBlock, rebaseInstruction, rebaseTarget, relocateInstruction, resolveTarget]

/-- The actual relocated DIVREM terminal tail runs in exactly three steps. -/
theorem runN_divRemAux_terminal_segment
    (blocks : List TemplateBlock) (root offset p residue : Nat)
    (destinationDiv destinationNondiv : JumpTarget)
    (pre suffix : Program) (a b : Nat) :
    runN 3
      (pre ++
        (((rebaseBlock offset
          (divRemAux p destinationDiv destinationNondiv 0 residue)).map
            (relocateInstruction blocks root)) ++ suffix))
      ⟨pre.length, a, b⟩ =
      some ⟨root, a, b + 1⟩ := by
  rw [divRemAux_terminal_code]
  exact runN_right_loop_segment pre suffix root a b


/-- A replicated instruction segment can be addressed inside a surrounding program. -/
theorem getElem?_replicate_segment
    {α : Type} (pre suffix : List α) (count index : Nat)
    (instruction : α) (hindex : index < count) :
    (pre ++ (List.replicate count instruction ++ suffix))[pre.length + index]? =
      some instruction := by
  rw [List.getElem?_append_right
    (l₁ := pre) (l₂ := List.replicate count instruction ++ suffix)
    (i := pre.length + index) (by omega)]
  have hsub : pre.length + index - pre.length = index := by omega
  rw [hsub]
  rw [List.getElem?_append_left
    (l₁ := List.replicate count instruction) (l₂ := suffix)
    (i := index) (by simp; omega)]
  exact List.getElem?_replicate_of_lt hindex

/-- The actual emitted TR handler after its enclosing DIVREM offset is applied. -/
def relocatedTRHandler (blocks : List TemplateBlock) (root m r destinationPC : Nat) :
    Program :=
  (rebaseBlock 1
    (transferBlock m r (.sourcePC destinationPC))).map
      (relocateInstruction blocks root)

/-- Exact instruction list of the nested and relocated TR handler. -/
theorem relocatedTRHandler_eq
    (blocks : List TemplateBlock) (root m r destinationPC : Nat) :
    relocatedTRHandler blocks root m r destinationPC =
      [Instruction.decJump Counter.right (root + 1 + (3 + r))] ++
        (List.replicate r (Instruction.inc Counter.left) ++
          ([Instruction.inc Counter.left,
            Instruction.decJump Counter.left
              (resolveTarget blocks root (.sourcePC destinationPC))] ++
            (List.replicate m (Instruction.inc Counter.left) ++
              [Instruction.inc Counter.left,
               Instruction.decJump Counter.left (root + 1)]))) := by
  simp [relocatedTRHandler, transferBlock, rebaseBlock,
    rebaseInstruction, rebaseTarget, identityJump, relocateInstruction,
    resolveTarget, Nat.add_assoc]

/-- The nested, relocated TR handler has the same finite length as its template. -/
theorem relocatedTRHandler_length
    (blocks : List TemplateBlock) (root m r destinationPC : Nat) :
    (relocatedTRHandler blocks root m r destinationPC).length =
      m + r + 5 := by
  rw [relocatedTRHandler_eq]
  simp
  omega

/--
Execution theorem for the literal relocated TR handler inside an arbitrary
program pre/suffix. This is the bridge from the symbolic DIVREM handler
to the all-input primitive theorem runN_transfer_correct_at.
-/
theorem runN_relocatedTRHandler
    (blocks : List TemplateBlock) (root m r destinationPC : Nat)
    (pre suffix : Program) (a q : Nat)
    (hprefix : pre.length = root + 1) :
    runN (q * (m + 3) + r + 3)
      (pre ++
        (relocatedTRHandler blocks root m r destinationPC ++ suffix))
      ⟨root + 1, a, q⟩ =
      some ⟨resolveTarget blocks root (.sourcePC destinationPC),
        a + m * q + r, 0⟩ := by
  let entry : Instruction :=
    .decJump .right (root + 1 + (3 + r))
  let residueCode : Program := List.replicate r (.inc .left)
  let jumpInc : Instruction := .inc .left
  let jump : Instruction :=
    .decJump .left (resolveTarget blocks root (.sourcePC destinationPC))
  let transferCode : Program := List.replicate m (.inc .left)
  let finalInc : Instruction := .inc .left
  let finalJump : Instruction := .decJump .left (root + 1)
  let handler : Program := relocatedTRHandler blocks root m r destinationPC
  let program : Program := pre ++ (handler ++ suffix)
  have hhandler :
      handler =
        [entry] ++
          (residueCode ++
            ([jumpInc, jump] ++
              (transferCode ++ [finalInc, finalJump]))) := by
    simpa [handler, entry, residueCode, jumpInc, jump, transferCode,
      finalInc, finalJump] using
        relocatedTRHandler_eq blocks root m r destinationPC
  have hlen : handler.length = m + r + 5 := by
    rw [relocatedTRHandler_length]
  have hEntryRaw : handler[0]? = some entry := by
    rw [hhandler]
    have h := getElem?_replicate_segment
      ([] : Program)
      (residueCode ++ ([jumpInc, jump] ++
        (transferCode ++ [finalInc, finalJump])))
      1 0 entry (by omega)
    simpa [entry] using h
  have hResidueRaw : ∀ i, i < r →
      handler[1 + i]? = some (Instruction.inc .left) := by
    intro i hi
    rw [hhandler]
    have h := getElem?_replicate_segment
      [entry]
      ([jumpInc, jump] ++ (transferCode ++ [finalInc, finalJump]))
      r i (Instruction.inc .left) hi
    simpa [entry, Nat.add_assoc] using h
  have hJumpIncRaw :
      handler[1 + r]? = some jumpInc := by
    rw [hhandler]
    let pre : Program := [entry] ++ residueCode
    let suffix : Program := [jump] ++ (transferCode ++ [finalInc, finalJump])
    have h := getElem?_middle pre [jumpInc] suffix 0 (by simp)
    have hmiddle :
        (pre ++ ([jumpInc] ++ suffix))[pre.length]? = some jumpInc := by
      simpa using h
    have hlist :
        [entry] ++ (residueCode ++ ([jumpInc, jump] ++
          (transferCode ++ [finalInc, finalJump]))) =
          pre ++ ([jumpInc] ++ suffix) := by
      simp [pre, suffix, List.append_assoc]
    have hindex : 1 + r = pre.length := by
      simp [pre, residueCode]
      omega
    rw [hlist, hindex]
    exact hmiddle
  have hJumpRaw : handler[1 + r + 1]? = some jump := by
    rw [hhandler]
    let pre : Program := [entry] ++ residueCode ++ [jumpInc]
    let suffix : Program := transferCode ++ [finalInc, finalJump]
    have h := getElem?_middle pre [jump] suffix 0 (by simp)
    have hmiddle :
        (pre ++ ([jump] ++ suffix))[pre.length]? = some jump := by
      simpa using h
    have hlist :
        [entry] ++ (residueCode ++ ([jumpInc, jump] ++
          (transferCode ++ [finalInc, finalJump]))) =
          pre ++ ([jump] ++ suffix) := by
      simp [pre, suffix, List.append_assoc]
    have hindex : 1 + r + 1 = pre.length := by
      simp [pre, residueCode]
      omega
    rw [hlist, hindex]
    exact hmiddle
  have hTransferRaw : ∀ i, i < m →
      handler[3 + r + i]? = some (Instruction.inc .left) := by
    intro i hi
    rw [hhandler]
    have h := getElem?_replicate_segment
      ([entry] ++ residueCode ++ [jumpInc, jump])
      [finalInc, finalJump]
      m i (Instruction.inc .left) hi
    simpa [entry, residueCode, jumpInc, jump, transferCode,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have hFinalIncRaw :
      handler[3 + r + m]? = some finalInc := by
    rw [hhandler]
    have h := getElem?_replicate_segment
      ([entry] ++ residueCode ++ [jumpInc, jump] ++ transferCode)
      [finalJump] 1 0 finalInc (by omega)
    simpa [entry, residueCode, jumpInc, jump, transferCode,
      finalInc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have hFinalJumpRaw :
      handler[4 + r + m]? = some finalJump := by
    rw [hhandler]
    have h := getElem?_replicate_segment
      ([entry] ++ residueCode ++ [jumpInc, jump] ++
        transferCode ++ [finalInc])
      [] 1 0 finalJump (by omega)
    simpa [entry, residueCode, jumpInc, jump, transferCode,
      finalInc, finalJump, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have hEmbed (i : Nat) (hi : i < handler.length) :
      program[pre.length + i]? = handler[i]? := by
    simpa [program] using getElem?_middle pre handler suffix i hi
  have hEntry :
      program[pre.length]? =
        some (Instruction.decJump .right (pre.length + 3 + r)) := by
    have h := hEmbed 0 (by rw [hlen]; omega)
    have h' : program[pre.length]? = handler[0]? := by simpa using h
    have haddr : root + 1 + (3 + r) = pre.length + 3 + r := by omega
    change handler[0]? =
      some (Instruction.decJump .right (root + 1 + (3 + r))) at hEntryRaw
    rw [haddr] at hEntryRaw
    exact h'.trans hEntryRaw
  have hResidue : ∀ i, i < r →
      program[pre.length + 1 + i]? =
        some (Instruction.inc .left) := by
    intro i hi
    have h := hEmbed (1 + i) (by rw [hlen]; omega)
    have hraw := hResidueRaw i hi
    have hindex : pre.length + 1 + i = pre.length + (1 + i) := by omega
    rw [hindex]
    exact h.trans hraw
  have hJumpInc :
      program[pre.length + 1 + r]? =
        some (Instruction.inc .left) := by
    have h := hEmbed (1 + r) (by rw [hlen]; omega)
    have hraw := hJumpIncRaw
    have hindex : pre.length + 1 + r = pre.length + (1 + r) := by omega
    rw [hindex]
    exact h.trans hraw
  have hJump :
      program[pre.length + 1 + r + 1]? =
        some (Instruction.decJump .left
          (resolveTarget blocks root (.sourcePC destinationPC))) := by
    have h := hEmbed (1 + r + 1) (by rw [hlen]; omega)
    have hraw := hJumpRaw
    have hindex :
        pre.length + 1 + r + 1 = pre.length + (1 + r + 1) := by omega
    rw [hindex]
    exact h.trans hraw
  have hTransfer : ∀ i, i < m →
      program[pre.length + 3 + r + i]? =
        some (Instruction.inc .left) := by
    intro i hi
    have h := hEmbed (3 + r + i) (by rw [hlen]; omega)
    have hraw := hTransferRaw i hi
    have hindex :
        pre.length + 3 + r + i =
          pre.length + (3 + r + i) := by omega
    rw [hindex]
    exact h.trans hraw
  have hFinalInc :
      program[pre.length + 3 + r + m]? =
        some (Instruction.inc .left) := by
    have h := hEmbed (3 + r + m) (by rw [hlen]; omega)
    have hraw := hFinalIncRaw
    have hindex :
        pre.length + 3 + r + m = pre.length + (3 + r + m) := by omega
    rw [hindex]
    exact h.trans hraw
  have hFinalJump :
      program[pre.length + 3 + r + m + 1]? =
        some (Instruction.decJump .left (pre.length + 0)) := by
    have h := hEmbed (4 + r + m) (by rw [hlen]; omega)
    have hraw := hFinalJumpRaw
    have hindex :
        pre.length + 3 + r + m + 1 =
          pre.length + (4 + r + m) := by omega
    rw [hindex]
    simpa [finalJump, hprefix] using h.trans hraw
  have hrun := runN_transfer_correct_at
    program pre.length m r
      (resolveTarget blocks root (.sourcePC destinationPC)) a q
      hEntry hResidue hJumpInc hJump hTransfer hFinalInc hFinalJump
  simpa [program, hprefix] using hrun

end Compiler
end HakuiKoyori
