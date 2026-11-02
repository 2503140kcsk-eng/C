module

public import HakuiKoyori.LowLevelMacros

public section

/-!
# Execution-level lookup bridge for flattened template blocks

The symbolic compiler first rebases local labels and then flattens nested
blocks into the target instruction list.  This module proves that the
flattened list contains exactly the relocated instruction at every valid
source-block offset.  It is the lookup lemma needed to instantiate primitive
macro run theorems inside a whole emitted program.
-/

namespace HakuiKoyori
namespace Compiler

/-- Recursive presentation of the existing enumerate/flatMap emitter. -/
def emitBlocksFrom (whole : List TemplateBlock) :
    Nat → List TemplateBlock → List Instruction
  | _, [] => []
  | pc, block :: rest =>
      (block.map (relocateInstruction whole (blockStart whole pc)) : List Instruction) ++
        (emitBlocksFrom whole (pc + 1) rest : List Instruction)

/-- The enumerate/flatMap emitter is extensionally the recursive emitter. -/
theorem enumerateBlocks_flatMap_eq (whole : List TemplateBlock) :
    ∀ (blocks : List TemplateBlock) (start : Nat),
      (enumerateBlocks blocks start).flatMap
        (fun (pc, block) =>
          block.map (relocateInstruction whole (blockStart whole pc))) =
        emitBlocksFrom whole start blocks := by
  intro blocks
  induction blocks with
  | nil =>
      intro start
      rfl
  | cons block rest ih =>
      intro start
      simp [enumerateBlocks, emitBlocksFrom, ih]

/-- The public emitter has the same output as the recursive presentation. -/
theorem emitBlocks_eq_emitBlocksFrom (blocks : List TemplateBlock) :
    emitBlocks blocks = emitBlocksFrom blocks 0 blocks := by
  unfold emitBlocks
  exact enumerateBlocks_flatMap_eq blocks blocks 0

/--
Lookup in a recursively flattened suffix: a valid instruction at offset j
inside source block i occurs at the corresponding cumulative output offset.
The source PC is start+i, while the output offset is the prefix sum in the
suffix list.
-/
theorem emitBlocksFrom_lookup (whole : List TemplateBlock) (start : Nat) :
    ∀ (blocks : List TemplateBlock) (i : Nat)
      (block : TemplateBlock) (j : Nat),
      blocks[i]? = some block →
      j < block.length →
      (emitBlocksFrom whole start blocks)[prefixLength blocks i + j]? =
        Option.map
          (relocateInstruction whole (blockStart whole (start + i)))
          (block[j]?) := by
  intro blocks
  induction blocks with
  | nil =>
      intro i block j hblock hj
      simp at hblock
  | cons head tail ih =>
      intro i block j hblock hj
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hblock
          subst block
          simp only [emitBlocksFrom, prefixLength, Nat.zero_add]
          rw [List.getElem?_append_left]
          · simp [List.getElem?_map, Nat.add_zero]
          · simpa using hj
      | succ i =>
          have hblock' : tail[i]? = some block := by
            simpa using hblock
          have hpc : start + (i + 1) = (start + 1) + i := by omega
          simp only [emitBlocksFrom, prefixLength]
          rw [List.getElem?_append_right (by omega)]
          have h := ih (start + 1) i block j hblock' hj
          simpa [hpc, Nat.add_assoc] using h

/--
Lookup bridge for the actual whole-program emitter.  It connects symbolic
block offsets to the concrete Instruction list consumed by AssistantMachine.step.
-/
theorem emitBlocks_lookup (blocks : List TemplateBlock) (i : Nat)
    (block : TemplateBlock) (j : Nat)
    (hblock : blocks[i]? = some block) (hj : j < block.length) :
    (emitBlocks blocks)[blockStart blocks i + j]? =
      Option.map
        (relocateInstruction blocks (blockStart blocks i))
        (block[j]?) := by
  rw [emitBlocks_eq_emitBlocksFrom]
  simpa [blockStart, Nat.zero_add] using
    emitBlocksFrom_lookup blocks 0 blocks i block j hblock hj

end Compiler
end HakuiKoyori
