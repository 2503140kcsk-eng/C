module

public import HakuiKoyori.PrimitiveDivRemRuns
public import HakuiKoyori.EmissionSemantics

public section

/-!
# Normalized layout of the generated DIVREM instruction block

The original DIVREM generator nests and rebases the remaining residue handlers.
This module gives an equivalent accumulator-based presentation in which every
test PC is a cumulative offset.  The equivalence is proved, rather than
assuming that nested labels are correct from inspection.
-/

namespace HakuiKoyori
namespace Compiler

open AssistantMachine

/-- Multiplier used by the handler for a particular Euclidean residue. -/
def divRemStageMultiplier (p residue : Nat) : Nat :=
  if residue = 0 then 1 else p

/-- Number of instructions from one residue test to the next test. -/
def divRemStageSpan (p residue : Nat) : Nat :=
  divRemStageMultiplier p residue + residue + 6

/-- Cumulative local address of residue test `i`, starting at residue `start`. -/
def divRemStageOffset (p start : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 =>
      divRemStageOffset p start i + divRemStageSpan p (start + i)

/-- Shifting the first residue out of a test-offset sequence. -/
theorem divRemStageOffset_succ (p start i : Nat) :
    divRemStageOffset p start (i + 1) =
      divRemStageSpan p start + divRemStageOffset p (start + 1) i := by
  induction i with
  | zero =>
      simp [divRemStageOffset]
  | succ i ih =>
      calc
        divRemStageOffset p start (i + 2) =
            divRemStageOffset p start (i + 1) +
              divRemStageSpan p (start + (i + 1)) := by
                rfl
        _ = (divRemStageSpan p start +
              divRemStageOffset p (start + 1) i) +
              divRemStageSpan p (start + (i + 1)) := by
                rw [ih]
        _ = divRemStageSpan p start +
              (divRemStageOffset p (start + 1) i +
                divRemStageSpan p ((start + 1) + i)) := by
                have hindex : start + (i + 1) = (start + 1) + i := by omega
                rw [hindex]
                omega
        _ = divRemStageSpan p start +
              divRemStageOffset p (start + 1) (i + 1) := by
                rfl

/-- Every test-to-test span is positive, even for an empty or zero divisor. -/
theorem divRemStageSpan_pos (p residue : Nat) :
    0 < divRemStageSpan p residue := by
  simp [divRemStageSpan, divRemStageMultiplier]

/-- Cumulative test offsets are monotone in their finite index. -/
theorem divRemStageOffset_mono (p start : Nat) {i j : Nat}
    (hij : i ≤ j) :
    divRemStageOffset p start i ≤ divRemStageOffset p start j := by
  induction hij with
  | refl =>
      exact Nat.le_refl _
  | @step j hij ih =>
      have hstep :
          divRemStageOffset p start j <
            divRemStageOffset p start (j + 1) := by
        simp only [divRemStageOffset]
        exact Nat.lt_add_of_pos_right (divRemStageSpan_pos p (start + j))
      exact le_trans ih (Nat.le_of_lt hstep)

/-- Each actual handler has exactly the length used in the offset recurrence. -/
theorem divRemStageSpan_eq_handler_length
    (p residue : Nat) (destination : JumpTarget) :
    divRemStageSpan p residue =
      1 + (rebaseBlock 1
        (transferBlock (divRemStageMultiplier p residue) residue destination)).length := by
  rw [rebaseBlock_length, transferBlock_length]
  simp [divRemStageSpan, Nat.add_assoc]
  omega

/--
Accumulator presentation of the nested DIVREM generator.  `offset` is the
absolute local offset from the beginning of the entire DIVREM block; all
local jump labels are therefore already expressed relative to that root.
-/
def divRemAuxFrom (p : Nat)
    (destinationDiv destinationNondiv : JumpTarget) :
    Nat → Nat → Nat → TemplateBlock
  | 0, _, _ =>
      [TemplateInstruction.inc Counter.right,
       TemplateInstruction.inc Counter.right,
       TemplateInstruction.decJump Counter.right .blockStart]
  | fuel + 1, residue, offset =>
      let multiplier := divRemStageMultiplier p residue
      let destination :=
        if residue = 0 then destinationDiv else destinationNondiv
      let handler :=
        rebaseBlock (offset + 1)
          (transferBlock multiplier residue destination)
      let nextOffset := offset + divRemStageSpan p residue
      [TemplateInstruction.decJump Counter.left (.offset nextOffset)] ++
        handler ++
        divRemAuxFrom p destinationDiv destinationNondiv
          fuel (residue + 1) nextOffset

/--
The accumulator presentation is extensionally equal to the existing nested
rebase generator.  This is the key algebraic normalization step.
-/
theorem divRemAuxFrom_eq_rebase
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget) :
    ∀ (fuel residue offset : Nat),
      divRemAuxFrom p destinationDiv destinationNondiv fuel residue offset =
        rebaseBlock offset
          (divRemAux p destinationDiv destinationNondiv fuel residue) := by
  intro fuel
  induction fuel with
  | zero =>
      intro residue offset
      simp [divRemAuxFrom, divRemAux, rebaseBlock]
  | succ fuel ih =>
      intro residue offset
      let multiplier := divRemStageMultiplier p residue
      let destination :=
        if residue = 0 then destinationDiv else destinationNondiv
      let oldHandler := rebaseBlock 1
        (transferBlock multiplier residue destination)
      let newHandler := rebaseBlock (offset + 1)
        (transferBlock multiplier residue destination)
      let oldNextOffset := 1 + oldHandler.length
      let newNextOffset := offset + divRemStageSpan p residue
      have hspan : divRemStageSpan p residue = oldNextOffset := by
        dsimp [oldNextOffset, oldHandler, multiplier, destination]
        exact (divRemStageSpan_eq_handler_length
          p residue destination).symm
      have htest :
          TemplateInstruction.decJump Counter.left (.offset newNextOffset) =
            rebaseInstruction offset
              (TemplateInstruction.decJump Counter.left (.offset oldNextOffset)) := by
        simp [newNextOffset, oldNextOffset, rebaseInstruction,
          rebaseTarget, hspan]
      have hhandler :
          newHandler = rebaseBlock offset oldHandler := by
        dsimp [newHandler, oldHandler]
        rw [rebaseBlock_comp]
        simp [Nat.add_assoc]
      have hrest :
          divRemAuxFrom p destinationDiv destinationNondiv
              fuel (residue + 1) newNextOffset =
            rebaseBlock offset
              (rebaseBlock oldNextOffset
                (divRemAux p destinationDiv destinationNondiv fuel
                  (residue + 1))) := by
        calc
          divRemAuxFrom p destinationDiv destinationNondiv
              fuel (residue + 1) newNextOffset =
            rebaseBlock newNextOffset
              (divRemAux p destinationDiv destinationNondiv fuel
                (residue + 1)) :=
              ih (residue + 1) newNextOffset
          _ = rebaseBlock offset
              (rebaseBlock oldNextOffset
                (divRemAux p destinationDiv destinationNondiv fuel
                  (residue + 1))) := by
                rw [rebaseBlock_comp]
                simp [newNextOffset, oldNextOffset, hspan,
                  Nat.add_assoc]
      simp only [divRemAuxFrom, divRemAux]
      simp only [rebaseBlock, List.map_append, List.map_cons]
      rw [htest, hhandler, hrest]
      rfl

/-- Rebase by zero is the identity map on a template block. -/
theorem divRemLayout_rebaseBlock_zero (block : TemplateBlock) :
    rebaseBlock 0 block = block := by
  have hinstruction : rebaseInstruction 0 = id := by
    funext instruction
    cases instruction with
    | inc which => rfl
    | decJump which target =>
        cases target <;> simp [rebaseInstruction, rebaseTarget]
  simp [rebaseBlock, hinstruction]

/-- The complete DIVREM block is the normalized accumulator presentation. -/
theorem divRemBlock_eq_divRemAuxFrom
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget) :
    divRemBlock p destinationDiv destinationNondiv =
      divRemAuxFrom p destinationDiv destinationNondiv p 0 0 := by
  unfold divRemBlock
  have h := divRemAuxFrom_eq_rebase
    p destinationDiv destinationNondiv p 0 0
  rw [divRemLayout_rebaseBlock_zero] at h
  exact h.symm

/-- Length of the normalized nested generator, including its three-instruction tail. -/
theorem divRemAuxFrom_length
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget) :
    ∀ (fuel residue offset : Nat),
      (divRemAuxFrom p destinationDiv destinationNondiv
        fuel residue offset).length =
        divRemStageOffset p residue fuel + 3 := by
  intro fuel
  induction fuel with
  | zero =>
      intro residue offset
      simp [divRemAuxFrom, divRemStageOffset]
  | succ fuel ih =>
      intro residue offset
      rw [divRemAuxFrom]
      simp only [List.length_append, List.length_cons, List.length_nil]
      have hspan :
          1 + (rebaseBlock (offset + 1)
            (transferBlock (divRemStageMultiplier p residue) residue
              (if residue = 0 then destinationDiv else destinationNondiv))).length =
            divRemStageSpan p residue := by
        rw [rebaseBlock_length, transferBlock_length]
        simp [divRemStageSpan, Nat.add_assoc]
        omega
      rw [ih (residue + 1) (offset + divRemStageSpan p residue)]
      rw [divRemStageOffset_succ]
      omega

/-- Every residue test is located at its cumulative offset in the normalized block. -/
theorem divRemAuxFrom_test_lookup
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget)
    (fuel residue offset i : Nat) (hi : i < fuel) :
    (divRemAuxFrom p destinationDiv destinationNondiv
      fuel residue offset)[divRemStageOffset p residue i]? =
      some (TemplateInstruction.decJump Counter.left
        (.offset (offset + divRemStageOffset p residue (i + 1)))) := by
  induction fuel generalizing residue offset i with
  | zero =>
      omega
  | succ fuel ih =>
      cases i with
      | zero =>
          simp [divRemAuxFrom, divRemStageOffset]
      | succ i =>
          let multiplier := divRemStageMultiplier p residue
          let destination :=
            if residue = 0 then destinationDiv else destinationNondiv
          let handler := rebaseBlock (offset + 1)
            (transferBlock multiplier residue destination)
          let stagePrefix : TemplateBlock :=
            [TemplateInstruction.decJump Counter.left
              (.offset (offset + divRemStageSpan p residue))] ++ handler
          let rest := divRemAuxFrom p destinationDiv destinationNondiv
            fuel (residue + 1) (offset + divRemStageSpan p residue)
          have hprefix :
              stagePrefix.length = divRemStageSpan p residue := by
            simp [stagePrefix, handler, rebaseBlock_length,
              transferBlock_length, divRemStageSpan, divRemStageMultiplier,
              Nat.add_assoc]
            omega
          have hshape :
              divRemAuxFrom p destinationDiv destinationNondiv
                  (fuel + 1) residue offset =
                stagePrefix ++ rest := by
            simp [divRemAuxFrom, stagePrefix, rest, List.append_assoc]
          have hindex :
              divRemStageOffset p residue (i + 1) =
                divRemStageSpan p residue +
                  divRemStageOffset p (residue + 1) i := by
            exact divRemStageOffset_succ p residue i
          rw [hshape, hindex]
          rw [List.getElem?_append_right (l₁ := stagePrefix) (l₂ := rest)
            (i := divRemStageSpan p residue +
              divRemStageOffset p (residue + 1) i)
            (by rw [hprefix]; omega)]
          rw [show
            divRemStageSpan p residue +
                divRemStageOffset p (residue + 1) i -
              stagePrefix.length =
                divRemStageOffset p (residue + 1) i by
              rw [hprefix]]
          have hrec := ih (residue + 1)
            (offset + divRemStageSpan p residue) i (by omega)
          have hnext :
              offset + divRemStageSpan p residue +
                  divRemStageOffset p (residue + 1) (i + 1) =
                offset + divRemStageOffset p residue (i + 2) := by
            rw [divRemStageOffset_succ p residue (i + 1)]
            omega
          simpa [rest, hnext, Nat.add_assoc] using hrec

/-- The original nested generator has the expected exact code length. -/
theorem divRemBlock_length
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget) :
    (divRemBlock p destinationDiv destinationNondiv).length =
      divRemStageOffset p 0 p + 3 := by
  rw [divRemBlock_eq_divRemAuxFrom]
  exact divRemAuxFrom_length p destinationDiv destinationNondiv p 0 0

/-- Exact symbolic address of every residue-test instruction in DIVREM. -/
theorem divRemBlock_test_lookup
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget)
    (i : Nat) (hi : i < p) :
    (divRemBlock p destinationDiv destinationNondiv)
        [divRemStageOffset p 0 i]? =
      some (TemplateInstruction.decJump Counter.left
        (.offset (divRemStageOffset p 0 (i + 1)))) := by
  rw [divRemBlock_eq_divRemAuxFrom]
  simpa [Nat.zero_add] using
    (divRemAuxFrom_test_lookup p destinationDiv destinationNondiv
      p 0 0 i hi)

/-- The test instruction's address is strictly inside the DIVREM block. -/
theorem divRemBlock_test_offset_lt_length
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget)
    (i : Nat) (hi : i < p) :
    divRemStageOffset p 0 i <
      (divRemBlock p destinationDiv destinationNondiv).length := by
  rw [divRemBlock_length]
  have hstep :
      divRemStageOffset p 0 i <
        divRemStageOffset p 0 (i + 1) := by
    rw [divRemStageOffset]
    exact Nat.lt_add_of_pos_right (divRemStageSpan_pos p i)
  have hmono :
      divRemStageOffset p 0 (i + 1) ≤ divRemStageOffset p 0 p :=
    divRemStageOffset_mono p 0 (Nat.succ_le_of_lt hi)
  omega

/--
The whole-program emitter preserves the concrete test instruction and
relocates its local jump to the correct absolute target address.
-/
theorem emitBlocks_divRem_test_lookup
    (blocks : List TemplateBlock) (pc : Nat)
    (block : TemplateBlock)
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget)
    (hblock : blocks[pc]? = some block)
    (hdiv : block = divRemBlock p destinationDiv destinationNondiv)
    (i : Nat) (hi : i < p) :
    (emitBlocks blocks)
        [blockStart blocks pc + divRemStageOffset p 0 i]? =
      some (Instruction.decJump Counter.left
        (blockStart blocks pc + divRemStageOffset p 0 (i + 1))) := by
  have hindex :
      divRemStageOffset p 0 i < block.length := by
    rw [hdiv]
    exact divRemBlock_test_offset_lt_length
      p destinationDiv destinationNondiv i hi
  have hlookup := emitBlocks_lookup blocks pc block
    (divRemStageOffset p 0 i) hblock hindex
  rw [hdiv, divRemBlock_test_lookup] at hlookup
  simpa [relocateInstruction, resolveTarget, Nat.add_assoc] using hlookup

end Compiler
end HakuiKoyori
