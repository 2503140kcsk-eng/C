module

public import HakuiKoyori.CompilerCore

/-!
# Concrete low-level instruction templates (M2)

This module turns the fixed-constant arithmetic macros into literal lists
of the existing two-counter ISA. Labels are templates: local offsets are
rebased when blocks are nested, and source program counters are resolved
only after all block lengths are known.

The semantic/termination theorems are intentionally not asserted here yet.
The file is a concrete code generator layer, not a compiler-correctness proof.
-/

universe u

namespace HakuiKoyori
namespace Compiler

open AssistantMachine

/-- A jump destination before final whole-program relocation. -/
inductive JumpTarget where
  /-- Offset relative to the current nested block. -/
  | offset (index : Nat)
  /-- Entry address of the enclosing arithmetic macro (not rebased). -/
  | blockStart
  /-- Entry address of a source three-register instruction block. -/
  | sourcePC (pc : Nat)
deriving DecidableEq, Repr

/-- One target instruction whose jump label is still symbolic. -/
inductive TemplateInstruction where
  | inc (which : Counter)
  | decJump (which : Counter) (target : JumpTarget)
deriving DecidableEq, Repr

abbrev TemplateBlock := List TemplateInstruction

/-- Rebase only labels internal to a nested block. -/
def rebaseTarget (base : Nat) : JumpTarget → JumpTarget
  | .offset k => .offset (base + k)
  | .blockStart => .blockStart
  | .sourcePC pc => .sourcePC pc

/-- Rebase one instruction while preserving external source labels. -/
def rebaseInstruction (base : Nat) : TemplateInstruction → TemplateInstruction
  | .inc which => .inc which
  | .decJump which target => .decJump which (rebaseTarget base target)

/-- Rebase every local label in a nested code block. -/
def rebaseBlock (base : Nat) (block : TemplateBlock) : TemplateBlock :=
  block.map (rebaseInstruction base)

@[simp] theorem rebaseTarget_offset (base k : Nat) :
    rebaseTarget base (.offset k) = .offset (base + k) := rfl

@[simp] theorem rebaseTarget_blockStart (base : Nat) :
    rebaseTarget base .blockStart = .blockStart := rfl

@[simp] theorem rebaseTarget_sourcePC (base pc : Nat) :
    rebaseTarget base (.sourcePC pc) = .sourcePC pc := rfl

@[simp] theorem rebaseBlock_length (base : Nat) (block : TemplateBlock) :
    (rebaseBlock base block).length = block.length := by
  simp [rebaseBlock]

/-- Identity jump using only the selected counter's two primitive instructions. -/
def identityJump (which : Counter) (target : JumpTarget) : TemplateBlock :=
  [.inc which, .decJump which target]

/--
Multiply the left counter by p, starting with right = 0.
The exit target is symbolic and the block uses only inc/decJump.
-/
def mulBlock (p : Nat) (destination : JumpTarget) : TemplateBlock :=
  [ .decJump .left (.offset 7)
  , .decJump .right (.offset 4)
  , .inc .left
  , .decJump .left destination
  , .inc .left
  , .inc .left
  , .decJump .left (.offset 1)
  ] ++
  List.replicate p (.inc .right) ++
  identityJump .right (.offset 0)

/-- The literal MUL block has p+9 primitive instructions. -/
theorem mulBlock_length (p : Nat) (destination : JumpTarget) :
    (mulBlock p destination).length = p + 9 := by
  simp [mulBlock, identityJump]

/--
Transfer block: on entry left=0 and right=q, return left=m*q+r and right=0.
This block is a code template; its loop proof is a separate obligation.
-/
def transferBlock (m r : Nat) (destination : JumpTarget) : TemplateBlock :=
  [.decJump .right (.offset (3 + r))] ++
  List.replicate r (.inc .left) ++
  identityJump .left destination ++
  List.replicate m (.inc .left) ++
  identityJump .left (.offset 0)

/-- The literal transfer block has m+r+5 primitive instructions. -/
theorem transferBlock_length (m r : Nat) (destination : JumpTarget) :
    (transferBlock m r destination).length = m + r + 5 := by
  simp [transferBlock, identityJump]
  omega

/--
Build the quotient/remainder zero-test block.

On entry (left,right)=(N,0), the block exits at destinationDiv with
(N/p,0) iff p divides N, and at destinationNondiv otherwise with (N,0).
The p finite-control tests distinguish the residue; every nested transfer
block is rebased before concatenation.
-/
def divRemAux (p : Nat) (destinationDiv destinationNondiv : JumpTarget) :
    Nat → Nat → TemplateBlock
  | 0, _ =>
      [.inc .right, .inc .right, .decJump .right .blockStart]
  | fuel + 1, residue =>
      let multiplier := if residue = 0 then 1 else p
      let destination := if residue = 0 then destinationDiv else destinationNondiv
      let handler := rebaseBlock 1 (transferBlock multiplier residue destination)
      let nextOffset := 1 + handler.length
      let rest := rebaseBlock nextOffset
        (divRemAux p destinationDiv destinationNondiv fuel (residue + 1))
      [.decJump .left (.offset nextOffset)] ++ handler ++ rest

/-- Complete p-residue quotient/remainder block. -/
def divRemBlock (p : Nat) (destinationDiv destinationNondiv : JumpTarget) :
    TemplateBlock :=
  divRemAux p destinationDiv destinationNondiv p 0

/-- A finite block list can be enumerated with its source PC. -/
def enumerateBlocks {α : Type u} : List α → Nat → List (Nat × α)
  | [], _ => []
  | x :: xs, n => (n, x) :: enumerateBlocks xs (n + 1)

/-- The global start address of source block pc. -/
def blockStart (blocks : List TemplateBlock) (pc : Nat) : Nat :=
  ((blocks.take pc).map List.length).sum

/-- The complete length of a flattened block list. -/
def blocksLength (blocks : List TemplateBlock) : Nat :=
  (blocks.map List.length).sum

/-- Resolve a local label or source PC to its final absolute instruction index. -/
def resolveTarget (blocks : List TemplateBlock) (base : Nat) (target : JumpTarget) : Nat :=
  match target with
  | .offset k => base + k
  | .blockStart => base
  | .sourcePC pc =>
      if pc < blocks.length then blockStart blocks pc else blocksLength blocks

/-- Relocate one symbolic instruction into the actual M1 target ISA. -/
def relocateInstruction (blocks : List TemplateBlock) (base : Nat) :
    TemplateInstruction → Instruction
  | .inc which => .inc which
  | .decJump which target => .decJump which (resolveTarget blocks base target)

/-- Relocate and flatten all blocks, preserving their source order. -/
def emitBlocks (blocks : List TemplateBlock) : List Instruction :=
  (enumerateBlocks blocks 0).flatMap fun (pc, block) =>
    block.map (relocateInstruction blocks (blockStart blocks pc))

/-- Prime assigned to each virtual register in the M2 representation. -/
def registerPrime : Register3 → Nat
  | Register3.r0 => 2
  | Register3.r1 => 3
  | Register3.r2 => 5

/-- Compile one virtual three-register instruction to a symbolic two-counter block. -/
def compileInstruction3 (pc : Nat) : Instruction3 → TemplateBlock
  | Instruction3.inc which =>
      mulBlock (registerPrime which) (.sourcePC (pc + 1))
  | Instruction3.decJump which target =>
      divRemBlock (registerPrime which) (.sourcePC target) (.sourcePC (pc + 1))

/-- Symbolic block sequence produced for a complete finite three-register program. -/
def compileBlocks3 (program : Program3) : List TemplateBlock :=
  (enumerateBlocks (α := Instruction3) program 0).map fun (pc, instruction) =>
    compileInstruction3 pc instruction

/-- Whole-program compiler into the existing two-counter instruction datatype. -/
def compileProgram3 (program : Program3) : Program :=
  emitBlocks (compileBlocks3 program)

end Compiler
end HakuiKoyori
