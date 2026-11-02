import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.List

/-!
# Assistant-machine model (M1)

A self-contained deterministic two-counter machine. Programs are finite lists of
instructions. A natural-number code is obtained from Mathlib's constructive
Encodable instance for finite lists; malformed codes are decoded to the empty
program, so the decoder is total.

Instruction semantics:
* inc r: increment counter r and advance the program counter.
* decJump r q: if r is zero, advance the program counter; otherwise
  decrement r and jump to q.
Falling off the end of a program halts. The left counter is the output register.
-/

namespace HakuiKoyori
namespace AssistantMachine

/-- The two addressable natural-number counters of the machine. -/
inductive Counter where
  | left
  | right
deriving DecidableEq, Repr

/-- The complete instruction set of the selected CM2 machine. -/
inductive Instruction where
  | inc (which : Counter)
  | decJump (which : Counter) (target : Nat)
deriving DecidableEq, Repr

def encodeCounter : Counter → Nat
  | .left => 0
  | .right => 1

/-- Total: every natural number is interpreted as one of the two counters. -/
def decodeCounter (n : Nat) : Counter :=
  if n = 0 then .left else .right

/-- A canonical natural-number code for a single instruction. -/
def encodeInstruction : Instruction → Nat
  | .inc which => Nat.pair 0 (Nat.pair (encodeCounter which) 0)
  | .decJump which target =>
      Nat.pair 1 (Nat.pair (encodeCounter which) target)

/-- A total decoder for instruction codes; unused tags are interpreted as decJump. -/
def decodeInstruction (n : Nat) : Instruction :=
  let outer := Nat.unpair n
  let args := Nat.unpair outer.2
  let which := decodeCounter args.1
  if outer.1 = 0 then .inc which else .decJump which args.2

/-- Instruction encoding is lossless on well-formed instructions. -/
theorem decodeInstruction_encodeInstruction (i : Instruction) :
    decodeInstruction (encodeInstruction i) = i := by
  cases i with
  | inc which =>
      cases which <;>
        simp [decodeInstruction, encodeInstruction, encodeCounter, decodeCounter]
  | decJump which target =>
      cases which <;>
        simp [decodeInstruction, encodeInstruction, encodeCounter, decodeCounter]

/-- Every natural number decodes to an instruction, and encoding then decoding is exact. -/
instance : Encodable Instruction where
  encode := encodeInstruction
  decode := fun n => some (decodeInstruction n)
  encodek := by
    intro i
    simp [decodeInstruction_encodeInstruction]

/-- A machine program is a finite instruction list. -/
abbrev Program := List Instruction

/-- Canonical natural-number code of a finite program. -/
def encodeProgram (p : Program) : Nat :=
  Encodable.encode p

/--
Total program decoder. Invalid list codes, if any, are mapped to the empty
program; every valid program is recovered exactly from its canonical code.
-/
def decodeProgram (n : Nat) : Program :=
  (Encodable.decode n : Option Program).getD []

theorem decodeProgram_encodeProgram (p : Program) :
    decodeProgram (encodeProgram p) = p := by
  simp [decodeProgram, encodeProgram]

@[simp] theorem decodeProgram_zero : decodeProgram 0 = [] := by
  simp [decodeProgram]

/-- A complete machine configuration: program counter and two counters. -/
structure Configuration where
  pc : Nat
  left : Nat
  right : Nat
deriving DecidableEq, Repr

def readCounter (c : Configuration) : Counter → Nat
  | .left => c.left
  | .right => c.right

def writeCounter (c : Configuration) (which : Counter) (value : Nat) :
    Configuration :=
  match which with
  | .left => { c with left := value }
  | .right => { c with right := value }

def setPC (c : Configuration) (next : Nat) : Configuration :=
  { c with pc := next }

/--
Deterministic partial transition function. none means that the machine has
halted because its program counter is outside the finite instruction list.
-/
def step (p : Program) (c : Configuration) : Option Configuration :=
  match p[c.pc]? with
  | none => none
  | some (.inc which) =>
      some (setPC (writeCounter c which (readCounter c which + 1)) (c.pc + 1))
  | some (.decJump which target) =>
      if readCounter c which = 0 then
        some (setPC c (c.pc + 1))
      else
        some (setPC (writeCounter c which (readCounter c which - 1)) target)

/-- The transition function has at most one successor from each configuration. -/
theorem step_deterministic {p : Program} {c a b : Configuration}
    (ha : step p c = some a) (hb : step p c = some b) : a = b := by
  have h : some a = some b := ha.symm.trans hb
  exact Option.some.inj h

/-- Input n is placed in the left counter; the right counter starts at zero. -/
def initialConfiguration (input : Nat) : Configuration :=
  ⟨0, input, 0⟩

/--
A finite run, indexed by its exact number of transitions. The inductive
derivation is the finite execution trace; no infinite object is used.
-/
inductive Run (p : Program) : Configuration → Nat → Configuration → Prop where
  | nil (c : Configuration) : Run p c 0 c
  | cons {c next final : Configuration} {k : Nat}
      (hstep : step p c = some next)
      (htail : Run p next k final) :
      Run p c (k + 1) final

/--
Two finite runs from the same start that both end in terminal configurations
must have the same final configuration.
-/
theorem terminal_final_unique
    {p : Program} {start final₁ final₂ : Configuration}
    {k₁ k₂ : Nat}
    (h₁ : Run p start k₁ final₁)
    (h₂ : Run p start k₂ final₂)
    (halt₁ : step p final₁ = none)
    (halt₂ : step p final₂ = none) :
    final₁ = final₂ := by
  induction h₁ generalizing k₂ final₂ with
  | nil =>
      cases h₂ with
      | nil => rfl
      | cons hstep₂ _ => simp [halt₁] at hstep₂
  | cons hstep₁ htail₁ ih =>
      cases h₂ with
      | nil => simp [halt₂] at hstep₁
      | cons hstep₂ htail₂ =>
          have hnext := Option.some.inj (hstep₁.symm.trans hstep₂)
          cases hnext
          exact ih htail₂ halt₁ halt₂

/-- The machine halts with output n when a finite run reaches a terminal state. -/
def HaltsWithOutput (p : Program) (input output : Nat) : Prop :=
  ∃ (steps : Nat) (final : Configuration),
    Run p (initialConfiguration input) steps final ∧
    step p final = none ∧ final.left = output

/-- A program that falls off its end immediately returns its input unchanged. -/
theorem empty_program_halts (input : Nat) :
    HaltsWithOutput [] input input := by
  refine ⟨0, initialConfiguration input, Run.nil _, ?_, rfl⟩
  simp [step]

/-- A machine and input cannot have two different halting outputs. -/
theorem halts_output_unique {p : Program} {input out₁ out₂ : Nat}
    (h₁ : HaltsWithOutput p input out₁)
    (h₂ : HaltsWithOutput p input out₂) : out₁ = out₂ := by
  rcases h₁ with ⟨k₁, final₁, run₁, halt₁, output₁⟩
  rcases h₂ with ⟨k₂, final₂, run₂, halt₂, output₂⟩
  have hfinal := terminal_final_unique run₁ run₂ halt₁ halt₂
  exact output₁.symm.trans ((congrArg Configuration.left hfinal).trans output₂)

/--
The partial halting-output map, made noncomputable by classical choice.
Uniqueness above guarantees that the chosen witness cannot change the value.
-/
noncomputable def haltingOutput? (p : Program) (input : Nat) : Option Nat :=
  if h : ∃ output, HaltsWithOutput p input output then
    some (Classical.choose h)
  else
    none

theorem haltingOutput?_of_halts {p : Program} {input output : Nat}
    (h : HaltsWithOutput p input output) :
    haltingOutput? p input = some output := by
  classical
  unfold haltingOutput?
  have hex : ∃ output', HaltsWithOutput p input output' := ⟨output, h⟩
  rw [dif_pos hex]
  have hchoose : Classical.choose hex = output :=
    halts_output_unique (Classical.choose_spec hex) h
  simp [hchoose]

/-- The explicit finite catalogue of all natural codes up to a bound. -/
def codesUpTo (bound : Nat) : List Nat :=
  List.range (bound + 1)

/--
Maximum halting output among codes 0,...,bound on a fixed input.
The recursion visits each code once and uses zero for non-halting programs.
-/
def maxHaltOutput : Nat → Nat → Nat
  | 0, input => (haltingOutput? (decodeProgram 0) input).getD 0
  | bound + 1, input =>
      max ((haltingOutput? (decodeProgram (bound + 1)) input).getD 0)
        (maxHaltOutput bound input)

/-- Every halting output in the finite code catalogue is bounded by its maximum. -/
theorem halting_output_le_maxHaltOutput
    {bound code input output : Nat}
    (hcode : code ≤ bound)
    (h : HaltsWithOutput (decodeProgram code) input output) :
    output ≤ maxHaltOutput bound input := by
  induction bound with
  | zero =>
      have hcode0 : code = 0 := Nat.eq_zero_of_le_zero hcode
      subst code
      simp [maxHaltOutput, haltingOutput?_of_halts h]
  | succ bound ih =>
      rcases Nat.eq_or_lt_of_le hcode with heq | hlt
      · subst code
        simp [maxHaltOutput, haltingOutput?_of_halts h]
      · exact le_trans (ih (Nat.le_of_lt_succ hlt) h) (Nat.le_max_right _ _)

/-- The finite Busy Beaver output function for this exact machine coding. -/
def busyBeaver (bound input : Nat) : Nat :=
  maxHaltOutput bound input + 1

/-- Diagonal property: the Busy Beaver value exceeds every halting output in its catalogue. -/
theorem busyBeaver_exceeds_catalogue
    {bound code input output : Nat}
    (hcode : code ≤ bound)
    (h : HaltsWithOutput (decodeProgram code) input output) :
    output < busyBeaver bound input := by
  exact Nat.lt_succ_of_le (halting_output_le_maxHaltOutput hcode h)

/-- Code zero is the empty program, which halts immediately and returns its input. -/
theorem codeZero_halts_identity (input : Nat) :
    HaltsWithOutput (decodeProgram 0) input input := by
  rw [decodeProgram_zero]
  exact empty_program_halts input

/-- The catalogue always contains a machine that returns the input unchanged. -/
theorem busyBeaver_gt_input (bound input : Nat) :
    input < busyBeaver bound input := by
  exact busyBeaver_exceeds_catalogue (Nat.zero_le bound)
    (codeZero_halts_identity input)

end AssistantMachine
end HakuiKoyori
