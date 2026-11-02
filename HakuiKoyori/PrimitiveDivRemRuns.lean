module

public import HakuiKoyori.PrimitiveTransferRuns

public section

/-!
# Concrete terminal execution for the DIVREM generator

The quotient/remainder generator ends in a three-instruction loop-back tail.
This file proves that the literal relocated tail executes exactly as intended
inside an arbitrary prefix/suffix context of the target program.
-/

namespace HakuiKoyori
namespace Compiler

open AssistantMachine

/-- Lookup in a middle list segment, at its absolute index after a prefix. -/
theorem getElem?_middle
    (prefix middle suffix : Program) (i : Nat)
    (hi : i < middle.length) :
    (prefix ++ (middle ++ suffix))[prefix.length + i]? = middle[i]? := by
  rw [List.getElem?_append_right
    (l₁ := prefix) (l₂ := middle ++ suffix)
    (i := prefix.length + i) (by omega)]
  have hindex : prefix.length + i - prefix.length = i := by omega
  rw [hindex]
  exact List.getElem?_append_left
    (l₁ := middle) (l₂ := suffix) (i := i) hi

/-- Two increments and a positive decrement-jump loop back to the root PC. -/
theorem runN_right_loop_segment
    (prefix suffix : Program) (root a b : Nat) :
    runN 3
      (prefix ++
        ([Instruction.inc .right, Instruction.inc .right,
          Instruction.decJump .right root] ++ suffix))
      ⟨prefix.length, a, b⟩ =
      some ⟨root, a, b + 1⟩ := by
  let middle : Program :=
    [Instruction.inc .right, Instruction.inc .right,
      Instruction.decJump .right root]
  have h0 :
      (prefix ++ (middle ++ suffix))[prefix.length]? =
        some (Instruction.inc .right) := by
    simpa [middle] using
      (getElem?_middle prefix middle suffix 0 (by simp [middle]))
  have h1 :
      (prefix ++ (middle ++ suffix))[prefix.length + 1]? =
        some (Instruction.inc .right) := by
    simpa [middle] using
      (getElem?_middle prefix middle suffix 1 (by simp [middle]))
  have h2 :
      (prefix ++ (middle ++ suffix))[prefix.length + 2]? =
        some (Instruction.decJump .right root) := by
    simpa [middle] using
      (getElem?_middle prefix middle suffix 2 (by simp [middle]))
  have hs0 :
      AssistantMachine.step (prefix ++ (middle ++ suffix))
        ⟨prefix.length, a, b⟩ =
        some ⟨prefix.length + 1, a, b + 1⟩ := by
    simp [AssistantMachine.step, h0, AssistantMachine.readCounter,
      AssistantMachine.writeCounter, AssistantMachine.setPC]
  have hs1 :
      AssistantMachine.step (prefix ++ (middle ++ suffix))
        ⟨prefix.length + 1, a, b + 1⟩ =
        some ⟨prefix.length + 2, a, b + 2⟩ := by
    simp [AssistantMachine.step, h1, AssistantMachine.readCounter,
      AssistantMachine.writeCounter, AssistantMachine.setPC]
  have hs2 :
      AssistantMachine.step (prefix ++ (middle ++ suffix))
        ⟨prefix.length + 2, a, b + 2⟩ =
        some ⟨root, a, b + 1⟩ := by
    simp [AssistantMachine.step, h2, AssistantMachine.readCounter,
      AssistantMachine.writeCounter, AssistantMachine.setPC]
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
  simp [divRemAux, rebaseBlock, relocateInstruction, resolveTarget]

/-- The actual relocated DIVREM terminal tail runs in exactly three steps. -/
theorem runN_divRemAux_terminal_segment
    (blocks : List TemplateBlock) (root offset p residue : Nat)
    (destinationDiv destinationNondiv : JumpTarget)
    (prefix suffix : Program) (a b : Nat) :
    runN 3
      (prefix ++
        (((rebaseBlock offset
          (divRemAux p destinationDiv destinationNondiv 0 residue)).map
            (relocateInstruction blocks root)) ++ suffix))
      ⟨prefix.length, a, b⟩ =
      some ⟨root, a, b + 1⟩ := by
  rw [divRemAux_terminal_code]
  exact runN_right_loop_segment prefix suffix root a b

end Compiler
end HakuiKoyori
