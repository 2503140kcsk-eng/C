module

public import HakuiKoyori.CompilerCore

public section

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
@[expose]
def rebaseTarget (base : Nat) : JumpTarget → JumpTarget
  | .offset k => .offset (base + k)
  | .blockStart => .blockStart
  | .sourcePC pc => .sourcePC pc

/-- Rebase one instruction while preserving external source labels. -/
@[expose]
def rebaseInstruction (base : Nat) : TemplateInstruction → TemplateInstruction
  | .inc which => .inc which
  | .decJump which target => .decJump which (rebaseTarget base target)

/-- Rebase every local label in a nested code block. -/
@[expose]
def rebaseBlock (base : Nat) (block : TemplateBlock) : TemplateBlock :=
  block.map (rebaseInstruction base)

@[simp] theorem rebaseTarget_offset (base k : Nat) :
    rebaseTarget base (.offset k) = .offset (base + k) := rfl

@[simp] theorem rebaseTarget_blockStart (base : Nat) :
    rebaseTarget base .blockStart = .blockStart := rfl

@[simp] theorem rebaseTarget_sourcePC (base pc : Nat) :
    rebaseTarget base (.sourcePC pc) = .sourcePC pc := rfl


/-- Identity jump using only the selected counter's two primitive instructions. -/
@[expose]
def identityJump (which : Counter) (target : JumpTarget) : TemplateBlock :=
  [.inc which, .decJump which target]

/-!
An unconditional jump is not a primitive instruction in the selected ISA.
The following theorem checks its two-instruction implementation directly
against the actual M1 transition function.
-/

/-- The identity-jump block preserves both counter values and reaches its target. -/
theorem identityJump_correct (which : Counter) (target a b : Nat) :
    ∃ middle : Configuration,
      step [.inc which, .decJump which target] ⟨0, a, b⟩ = some middle ∧
      step [.inc which, .decJump which target] middle =
        some ⟨target, a, b⟩ := by
  cases which with
  | left =>
      refine ⟨⟨1, a + 1, b⟩, ?_, ?_⟩
      · rfl
      · rfl
  | right =>
      refine ⟨⟨1, a, b + 1⟩, ?_, ?_⟩
      · rfl
      · rfl

/--
Multiply the left counter by p, starting with right = 0.
The exit target is symbolic and the block uses only inc/decJump.
-/
@[expose]
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
@[expose]
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
@[expose]
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
@[expose]
def divRemBlock (p : Nat) (destinationDiv destinationNondiv : JumpTarget) :
    TemplateBlock :=
  divRemAux p destinationDiv destinationNondiv p 0

/-- A finite block list can be enumerated with its source PC. -/
def enumerateBlocks {α : Type u} : List α → Nat → List (Nat × α)
  | [], _ => []
  | x :: xs, n => (n, x) :: enumerateBlocks xs (n + 1)

/-- Recursive prefix sum of lengths of the first source blocks. -/
@[expose]
def prefixLength : List TemplateBlock → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | block :: rest, pc + 1 => block.length + prefixLength rest pc

/-- The global start address of source block pc. -/
@[expose]
def blockStart (blocks : List TemplateBlock) (pc : Nat) : Nat :=
  prefixLength blocks pc

/-- The complete length of a flattened block list. -/
@[expose]
def blocksLength (blocks : List TemplateBlock) : Nat :=
  (blocks.map List.length).sum

/-- Resolve a local label or source PC to its final absolute instruction index. -/
@[expose]
def resolveTarget (blocks : List TemplateBlock) (base : Nat) (target : JumpTarget) : Nat :=
  match target with
  | .offset k => base + k
  | .blockStart => base
  | .sourcePC pc =>
      if pc < blocks.length then blockStart blocks pc else blocksLength blocks

@[simp] theorem resolveTarget_offset (blocks : List TemplateBlock)
    (base offset : Nat) :
    resolveTarget blocks base (.offset offset) = base + offset := rfl

@[simp] theorem resolveTarget_blockStart (blocks : List TemplateBlock)
    (base : Nat) :
    resolveTarget blocks base .blockStart = base := rfl

@[simp] theorem resolveTarget_sourcePC (blocks : List TemplateBlock)
    (base pc : Nat) :
    resolveTarget blocks base (.sourcePC pc) =
      if pc < blocks.length then blockStart blocks pc else blocksLength blocks := rfl

/-- Relocate one symbolic instruction into the actual M1 target ISA. -/
@[expose]
def relocateInstruction (blocks : List TemplateBlock) (base : Nat) :
    TemplateInstruction → Instruction
  | .inc which => .inc which
  | .decJump which target => .decJump which (resolveTarget blocks base target)

/-- Mapping relocation over a block preserves lookup and relocates the selected instruction. -/
@[simp] theorem relocateBlock_getElem? (blocks : List TemplateBlock)
    (base : Nat) (block : TemplateBlock) (i : Nat) :
    (block.map (relocateInstruction blocks base))[i]? =
      Option.map (relocateInstruction blocks base) (block[i]?) := by
  simp

/-- Looking up a rebased and then relocated nested instruction is pointwise composition. -/
theorem relocateRebasedBlock_getElem? (blocks : List TemplateBlock)
    (base nestedOffset : Nat) (block : TemplateBlock) (i : Nat) :
    ((rebaseBlock nestedOffset block).map
      (relocateInstruction blocks base))[i]? =
        Option.map
          (fun instruction =>
            relocateInstruction blocks base
              (rebaseInstruction nestedOffset instruction))
          (block[i]?) := by
  simp [rebaseBlock]
  rfl



/-- Rebased block lookup is the mapped lookup of the original instruction. -/
@[simp] theorem rebaseBlock_getElem? (base : Nat)
    (block : TemplateBlock) (i : Nat) :
    (rebaseBlock base block)[i]? =
      Option.map (rebaseInstruction base) (block[i]?) := by
  simp [rebaseBlock]


@[simp] theorem rebaseBlock_length (base : Nat) (block : TemplateBlock) :
    (rebaseBlock base block).length = block.length := by
  simp [rebaseBlock]

/-- Relocate and flatten all blocks, preserving their source order. -/
@[expose]
def emitBlocks (blocks : List TemplateBlock) : List Instruction :=
  (enumerateBlocks blocks 0).flatMap fun (pc, block) =>
    block.map (relocateInstruction blocks (blockStart blocks pc))


/-!

/-!
## Relocation semantics for nested labels

These lemmas keep the three label classes distinct: local offsets are shifted,
the enclosing macro's block-start label is fixed, and source-PC labels remain
external until the whole-program block table is known.
-/

/-- Rebase followed by target resolution adds the nested offset only to local labels. -/
theorem resolveTarget_rebase (blocks : List TemplateBlock)
    (base nestedOffset : Nat) (target : JumpTarget) :
    resolveTarget blocks base (rebaseTarget nestedOffset target) =
      match target with
      | .offset k => base + nestedOffset + k
      | .blockStart => base
      | .sourcePC pc =>
          if pc < blocks.length then blockStart blocks pc else blocksLength blocks := by
  cases target <;> simp [rebaseTarget, resolveTarget, Nat.add_assoc]

/-- A nested local jump is relocated to the enclosing base plus its accumulated offset. -/
theorem relocateInstruction_rebase_offset
    (blocks : List TemplateBlock) (base nestedOffset k : Nat)
    (which : Counter) :
    relocateInstruction blocks base
      (rebaseInstruction nestedOffset (.decJump which (.offset k))) =
        .decJump which (base + nestedOffset + k) := by
  simp [rebaseInstruction, rebaseTarget, relocateInstruction,
    resolveTarget, Nat.add_assoc]

/-- The enclosing macro-start label is invariant under nested rebasing. -/
theorem relocateInstruction_rebase_blockStart
    (blocks : List TemplateBlock) (base nestedOffset : Nat)
    (which : Counter) :
    relocateInstruction blocks base
      (rebaseInstruction nestedOffset (.decJump which .blockStart)) =
        .decJump which base := by
  rfl

/-- Source-PC labels are unaffected by nested rebasing and resolve globally. -/
theorem relocateInstruction_rebase_sourcePC
    (blocks : List TemplateBlock) (base nestedOffset pc : Nat)
    (which : Counter) :
    relocateInstruction blocks base
      (rebaseInstruction nestedOffset (.decJump which (.sourcePC pc))) =
        .decJump which
          (if pc < blocks.length then blockStart blocks pc else blocksLength blocks) := by
  rfl

## Flattening length and terminal-address bridge

These lemmas establish that relocation changes labels but not block sizes,
and that the address immediately after the emitted program is the sum of
the source-block lengths.  They do not yet establish instruction-by-instruction
operational preservation; that requires the separate lookup/simulation lemma.
-/

/-- Enumerating and relocating a list of blocks preserves its total length. -/
private theorem enumerateBlocks_relocated_length
    (whole : List TemplateBlock) :
    ∀ (blocks : List TemplateBlock) (start : Nat),
      ((enumerateBlocks blocks start).flatMap
        (fun (pc, block) =>
          block.map (relocateInstruction whole (blockStart whole pc)))).length =
        (blocks.map List.length).sum := by
  intro blocks
  induction blocks with
  | nil =>
      intro start
      simp [enumerateBlocks]
  | cons block rest ih =>
      intro start
      simp only [enumerateBlocks, List.flatMap_cons,
        List.length_append, List.length_map]
      rw [ih (start + 1)]
      simp

/-- Flattening all blocks preserves the sum of their source lengths. -/
theorem emitBlocks_length (blocks : List TemplateBlock) :
    (emitBlocks blocks).length = blocksLength blocks := by
  unfold emitBlocks blocksLength
  exact enumerateBlocks_relocated_length blocks blocks 0

/-- The prefix length at the terminal source PC is the complete target length. -/
theorem prefixLength_terminal (blocks : List TemplateBlock) :
    prefixLength blocks blocks.length = blocksLength blocks := by
  induction blocks with
  | nil =>
      simp [prefixLength, blocksLength]
  | cons block rest ih =>
      simp [prefixLength, blocksLength, ih]

/-- The emitted program ends exactly at the address assigned to the terminal PC. -/
theorem emitBlocks_terminal_address (blocks : List TemplateBlock) :
    (emitBlocks blocks).length = blockStart blocks blocks.length := by
  rw [emitBlocks_length]
  change blocksLength blocks = prefixLength blocks blocks.length
  exact (prefixLength_terminal blocks).symm

/-- Prime assigned to each virtual register in the M2 representation. -/
@[expose]
def registerPrime : _root_.HakuiKoyori.Compiler.Register3 → Nat
  | _root_.HakuiKoyori.Compiler.Register3.r0 => 2
  | _root_.HakuiKoyori.Compiler.Register3.r1 => 3
  | _root_.HakuiKoyori.Compiler.Register3.r2 => 5

/-- Compile one virtual three-register instruction to a symbolic two-counter block. -/
@[expose]
def compileInstruction3 (pc : Nat) :
    _root_.HakuiKoyori.Compiler.Instruction3 → TemplateBlock
  | _root_.HakuiKoyori.Compiler.Instruction3.inc which =>
      mulBlock (registerPrime which) (.sourcePC (pc + 1))
  | _root_.HakuiKoyori.Compiler.Instruction3.decJump which target =>
      divRemBlock (registerPrime which) (.sourcePC target) (.sourcePC (pc + 1))

/-- Symbolic block sequence produced for a complete finite three-register program. -/
@[expose]
def compileBlocks3 (program : _root_.HakuiKoyori.Compiler.Program3) : List TemplateBlock :=
  (enumerateBlocks (α := _root_.HakuiKoyori.Compiler.Instruction3) program 0).map
    fun (pc, instruction) =>
    compileInstruction3 pc instruction

/-- Whole-program compiler into the existing two-counter instruction datatype. -/
@[expose]
def compileProgram3 (program : _root_.HakuiKoyori.Compiler.Program3) : Program :=
  emitBlocks (compileBlocks3 program)


/-!
## Relocation algebra and source-block address discipline

Nested templates must compose their offsets associatively.  Whole-program
source addresses are prefix sums of block lengths; they are monotone in
general, and strictly increasing for valid source PCs when every emitted
source block is nonempty.
-/

/-- Rebase composition is associative on local offsets and fixes external labels. -/
theorem rebaseTarget_comp (outer inner : Nat) (target : JumpTarget) :
    rebaseTarget outer (rebaseTarget inner target) =
      rebaseTarget (outer + inner) target := by
  cases target <;> simp [rebaseTarget, Nat.add_assoc]

/-- Rebase composition for individual symbolic instructions. -/
theorem rebaseInstruction_comp (outer inner : Nat)
    (instruction : TemplateInstruction) :
    rebaseInstruction outer (rebaseInstruction inner instruction) =
      rebaseInstruction (outer + inner) instruction := by
  cases instruction with
  | inc which => rfl
  | decJump which target =>
      simp [rebaseInstruction, rebaseTarget_comp]

/-- Rebase composition for whole nested blocks. -/
theorem rebaseBlock_comp (outer inner : Nat) (block : TemplateBlock) :
    rebaseBlock outer (rebaseBlock inner block) =
      rebaseBlock (outer + inner) block := by
  induction block with
  | nil => rfl
  | cons instruction rest ih =>
      change
        rebaseInstruction outer (rebaseInstruction inner instruction) ::
          rebaseBlock outer (rebaseBlock inner rest) =
        rebaseInstruction (outer + inner) instruction ::
          rebaseBlock (outer + inner) rest
      rw [rebaseInstruction_comp, ih]

/-- The implementation's blockStart is exactly the recursive prefix sum. -/
theorem blockStart_eq_prefixLength (blocks : List TemplateBlock) (pc : Nat) :
    blockStart blocks pc = prefixLength blocks pc := rfl

/-- Source block starts are nondecreasing, even when some blocks are empty. -/
theorem prefixLength_mono (blocks : List TemplateBlock) {i j : Nat}
    (hij : i ≤ j) :
    prefixLength blocks i ≤ prefixLength blocks j := by
  induction blocks generalizing i j with
  | nil =>
      simp [prefixLength]
  | cons block rest ih =>
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j =>
              simp only [prefixLength]
              exact Nat.zero_le _
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simp only [prefixLength]
              exact Nat.add_le_add_left
                (ih (Nat.le_of_succ_le_succ hij)) _

/--
If all source blocks are nonempty, prefix lengths strictly increase for
indices within the source program.  The upper-bound premise is essential:
indices beyond the end all denote the same halt address.
-/
theorem prefixLength_strict (blocks : List TemplateBlock)
    (hpos : ∀ block ∈ blocks, 0 < block.length)
    {i j : Nat} (hij : i < j) (hj : j ≤ blocks.length) :
    prefixLength blocks i < prefixLength blocks j := by
  induction blocks generalizing i j with
  | nil =>
      simp at hj
      omega
  | cons block rest ih =>
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ j =>
              have hblock := hpos block (by simp)
              simp only [prefixLength]
              omega
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              have htail : ∀ b ∈ rest, 0 < b.length := by
                intro b hb
                exact hpos b (by simp [hb])
              have hj' : j ≤ rest.length := by
                simp at hj
                omega
              simp only [prefixLength]
              exact Nat.add_lt_add_left
                (ih htail (Nat.lt_of_succ_lt_succ hij) hj') _


/-- Enumerating a finite source list preserves its length. -/
theorem enumerateBlocks_length {α : Type u} (xs : List α) (start : Nat) :
    (enumerateBlocks xs start).length = xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
      simp [enumerateBlocks, ih]

/-- The compiler emits exactly one target block for each source instruction. -/
theorem compileBlocks3_length
    (program : _root_.HakuiKoyori.Compiler.Program3) :
    (compileBlocks3 program).length = program.length := by
  simp [compileBlocks3, enumerateBlocks_length]

/-- Compilation keeps the source instruction count as the number of blocks. -/
theorem compileProgram3_block_count
    (program : _root_.HakuiKoyori.Compiler.Program3) :
    (compileBlocks3 program).length = program.length :=
  compileBlocks3_length program

/-- The actual block-start function inherits the strict source-PC ordering. -/
theorem blockStart_strict (blocks : List TemplateBlock)
    (hpos : ∀ block ∈ blocks, 0 < block.length)
    {i j : Nat} (hij : i < j) (hj : j ≤ blocks.length) :
    blockStart blocks i < blockStart blocks j := by
  rw [blockStart_eq_prefixLength, blockStart_eq_prefixLength]
  exact prefixLength_strict blocks hpos hij hj

/-- Every generated multiplication block is nonempty. -/
theorem mulBlock_length_pos (p : Nat) (destination : JumpTarget) :
    0 < (mulBlock p destination).length := by
  rw [mulBlock_length]
  omega

/-- Every generated quotient/remainder block is nonempty, including p=0. -/
theorem divRemBlock_length_pos (p : Nat)
    (destinationDiv destinationNondiv : JumpTarget) :
    0 < (divRemBlock p destinationDiv destinationNondiv).length := by
  cases p with
  | zero =>
      simp [divRemBlock, divRemAux]
  | succ p =>
      simp [divRemBlock, divRemAux]

/-- Every virtual instruction compiles to a nonempty target block. -/
theorem compileInstruction3_length_pos (pc : Nat)
    (instruction : _root_.HakuiKoyori.Compiler.Instruction3) :
    0 < (compileInstruction3 pc instruction).length := by
  cases instruction with
  | inc which =>
      change 0 < (mulBlock (registerPrime which) (.sourcePC (pc + 1))).length
      exact mulBlock_length_pos _ _
  | decJump which target =>
      change 0 < (divRemBlock (registerPrime which)
        (.sourcePC target) (.sourcePC (pc + 1))).length
      exact divRemBlock_length_pos _ _ _

/-- All blocks emitted for a three-register program are nonempty. -/
theorem compileBlocks3_all_nonempty
    (program : _root_.HakuiKoyori.Compiler.Program3) :
    ∀ block ∈ compileBlocks3 program, 0 < block.length := by
  intro block hmem
  unfold compileBlocks3 at hmem
  rcases List.mem_map.mp hmem with ⟨⟨pc, instruction⟩, _, hblock⟩
  subst block
  exact compileInstruction3_length_pos pc instruction

/-- Distinct valid source PCs receive distinct relocated block starts. -/
theorem compileBlocks3_blockStart_strict
    (program : _root_.HakuiKoyori.Compiler.Program3)
    {i j : Nat} (hij : i < j) (hj : j ≤ program.length) :
    blockStart (compileBlocks3 program) i <
      blockStart (compileBlocks3 program) j := by
  apply blockStart_strict
  · exact compileBlocks3_all_nonempty program
  · exact hij
  · simpa [compileBlocks3_length] using hj


/-!
## Exact DIVREM block-size invariants

The quotient/remainder block is a finite chain of residue handlers followed
by a three-instruction loop-back tail.  The following equations expose its
exact layout, which is needed before proving execution-level relocation.
-/

/-- Triangular numbers, defined by their successor recurrence. -/
def divRemTriangular : Nat → Nat
  | 0 => 0
  | n + 1 => divRemTriangular n + n

/-- Exact recursive length predicted by the DIVREM generator. -/
def divRemAuxLength (p : Nat) : Nat → Nat → Nat
  | 0, _ => 3
  | fuel + 1, residue =>
      (if residue = 0 then 1 else p) + residue + 6 +
        divRemAuxLength p fuel (residue + 1)

/-- The generated DIVREM auxiliary block has its predicted length. -/
theorem divRemAux_length_exact
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget)
    (fuel residue : Nat) :
    (divRemAux p destinationDiv destinationNondiv fuel residue).length =
      divRemAuxLength p fuel residue := by
  induction fuel generalizing residue with
  | zero =>
      simp [divRemAux, divRemAuxLength]
  | succ fuel ih =>
      simp [divRemAux, divRemAuxLength, rebaseBlock_length,
        transferBlock_length, ih] <;> omega

/-- For a positive starting residue, every handler uses multiplier p. -/
theorem divRemAuxLength_pos_residue
    (p fuel residue : Nat) (hresidue : 0 < residue) :
    divRemAuxLength p fuel residue =
      3 + fuel * (p + residue + 6) + divRemTriangular fuel := by
  induction fuel generalizing residue with
  | zero =>
      simp [divRemAuxLength, divRemTriangular]
  | succ fuel ih =>
      simp only [divRemAuxLength, if_neg (by omega)]
      rw [ih (residue + 1) (by omega)]
      simp only [divRemTriangular]
      ring

/-- Closed size formula for a nonempty DIVREM chain starting at residue zero. -/
theorem divRemAuxLength_zero_succ
    (p fuel : Nat) :
    divRemAuxLength p (fuel + 1) 0 =
      10 + fuel * (p + 6) + divRemTriangular (fuel + 1) := by
  simp only [divRemAuxLength, if_pos rfl]
  rw [divRemAuxLength_pos_residue p fuel 1 (by omega)]
  simp only [divRemTriangular]
  ring

/-- The complete p-residue DIVREM block has the exact recursive size. -/
theorem divRemBlock_length_exact
    (p : Nat) (destinationDiv destinationNondiv : JumpTarget) :
    (divRemBlock p destinationDiv destinationNondiv).length =
      divRemAuxLength p p 0 := by
  unfold divRemBlock
  exact divRemAux_length_exact p destinationDiv destinationNondiv p 0

/-- Closed exact length of DIVREM for every positive divisor p. -/
theorem divRemBlock_length_closed
    {p : Nat} (hp : 0 < p)
    (destinationDiv destinationNondiv : JumpTarget) :
    (divRemBlock p destinationDiv destinationNondiv).length =
      10 + (p - 1) * (p + 6) + divRemTriangular p := by
  rw [divRemBlock_length_exact]
  cases p with
  | zero =>
      omega
  | succ n =>
      simpa using (divRemAuxLength_zero_succ (Nat.succ n) n)


end Compiler
end HakuiKoyori
