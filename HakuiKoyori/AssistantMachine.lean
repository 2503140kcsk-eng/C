module

public import Mathlib.Data.Nat.Pairing
public import Mathlib.Logic.Equiv.List
public import Mathlib.Logic.Encodable.Basic

public section

/-!
# Assistant-machine model (M1)

A deterministic two-counter machine. Programs are finite lists of instructions.
The machine description and every finite execution trace have natural-number
codes. Decoders are total: malformed program/trace codes decode to the empty list.

Instruction semantics:
* inc r: increment counter r and advance the program counter.
* decJump r q: if r is zero, advance the program counter; otherwise decrement r
  and jump to q.
Falling off the end of a program halts. The left counter is the output register.
-/

namespace HakuiKoyori
namespace AssistantMachine

/-- The two addressable natural-number counters. -/
inductive Counter where
  | left
  | right
deriving DecidableEq, Repr

/-- The complete instruction set of the selected two-counter machine. -/
inductive Instruction where
  | inc (which : Counter)
  | decJump (which : Counter) (target : Nat)
deriving DecidableEq, Repr

def encodeCounter : Counter → Nat
  | .left => 0
  | .right => 1

/-- Total decoder: zero selects the left counter; every other code selects right. -/
def decodeCounter (n : Nat) : Counter :=
  if n = 0 then .left else .right

/-- Canonical natural-number code for one instruction. -/
def encodeInstruction : Instruction → Nat
  | .inc which => Nat.pair 0 (Nat.pair (encodeCounter which) 0)
  | .decJump which target =>
      Nat.pair 1 (Nat.pair (encodeCounter which) target)

/-- Total decoder for instructions; unused tags are interpreted as decJump. -/
def decodeInstruction (n : Nat) : Instruction :=
  let outer := Nat.unpair n
  let args := Nat.unpair outer.2
  let which := decodeCounter args.1
  if outer.1 = 0 then .inc which else .decJump which args.2

/-- Encoding followed by decoding recovers every instruction. -/
theorem decodeInstruction_encodeInstruction (i : Instruction) :
    decodeInstruction (encodeInstruction i) = i := by
  cases i with
  | inc which =>
      cases which <;>
        simp [decodeInstruction, encodeInstruction, encodeCounter, decodeCounter]
  | decJump which target =>
      cases which <;>
        simp [decodeInstruction, encodeInstruction, encodeCounter, decodeCounter]

instance : Encodable Instruction where
  encode := encodeInstruction
  decode := fun n => some (decodeInstruction n)
  encodek := by
    intro i
    simp [decodeInstruction_encodeInstruction]

/-- A program is a finite instruction list. -/
abbrev Program := List Instruction

/-- Canonical code of a finite program, using Mathlib's list encoding. -/
def encodeProgram (p : Program) : Nat :=
  Encodable.encode p

/-- Total program decoder; malformed codes denote the empty program. -/
def decodeProgram (n : Nat) : Program :=
  (Encodable.decode n : Option Program).getD []

theorem decodeProgram_encodeProgram (p : Program) :
    decodeProgram (encodeProgram p) = p := by
  simp [decodeProgram, encodeProgram]

@[simp] theorem decodeProgram_zero : decodeProgram 0 = [] := by
  simp [decodeProgram]

/-- A complete machine configuration. -/
structure Configuration where
  pc : Nat
  left : Nat
  right : Nat
deriving DecidableEq, Repr

/-- Pairing-based natural-number encoding of a configuration. -/
def encodeConfiguration (c : Configuration) : Nat :=
  Nat.pair c.pc (Nat.pair c.left c.right)

/-- Total decoder for configurations. -/
def decodeConfiguration (n : Nat) : Configuration :=
  let p := Nat.unpair n
  let q := Nat.unpair p.2
  ⟨p.1, q.1, q.2⟩

instance : Encodable Configuration where
  encode := encodeConfiguration
  decode := fun n => some (decodeConfiguration n)
  encodek := by
    intro c
    cases c
    simp [encodeConfiguration, decodeConfiguration]

/-- A finite trace is a list of complete configurations. -/
abbrev Trace := List Configuration

/-- Encode a finite execution trace as one natural number. -/
def encodeTrace (trace : Trace) : Nat :=
  Encodable.encode trace

/-- Total trace decoder; malformed codes denote the empty trace. -/
def decodeTrace (code : Nat) : Trace :=
  (Encodable.decode code : Option Trace).getD []

theorem decodeTrace_encodeTrace (trace : Trace) :
    decodeTrace (encodeTrace trace) = trace := by
  simp [decodeTrace, encodeTrace]

/-- Read the selected counter from a configuration. -/
@[expose]
def readCounter (c : Configuration) : Counter → Nat
  | .left => c.left
  | .right => c.right

/-- Update one selected counter, leaving the other fields unchanged. -/
@[expose]
def writeCounter (c : Configuration) (which : Counter) (value : Nat) :
    Configuration :=
  match which with
  | .left => { c with left := value }
  | .right => { c with right := value }

@[expose]
def setPC (c : Configuration) (next : Nat) : Configuration :=
  { c with pc := next }

/--
Deterministic partial transition function. none means that the program
counter is outside the finite instruction list, so the machine has halted.
-/
@[expose]
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
A finite, explicitly stored execution trace. The trace includes its initial
configuration and its terminal configuration. Each nonterminal entry has
exactly the successor prescribed by step; the final entry has no successor.
-/
inductive ExecutionTrace (p : Program) :
    Configuration → Trace → Configuration → Type where
  | halt (c : Configuration) (hhalt : step p c = none) :
      ExecutionTrace p c [c] c
  | cons {c next final : Configuration} {tail : Trace}
      (hstep : step p c = some next)
      (htail : ExecutionTrace p next tail final) :
      ExecutionTrace p c (c :: tail) final

/-- Determinism implies that a starting configuration has at most one trace endpoint. -/
theorem trace_final_unique
    {p : Program} {start final₁ final₂ : Configuration}
    {trace₁ trace₂ : Trace}
    (h₁ : ExecutionTrace p start trace₁ final₁)
    (h₂ : ExecutionTrace p start trace₂ final₂) :
    final₁ = final₂ := by
  induction h₁ generalizing trace₂ final₂ with
  | halt c hhalt =>
      cases h₂ with
      | halt _ _ => rfl
      | cons hstep _ => simp [hhalt] at hstep
  | cons hstep₁ htail₁ ih =>
      cases h₂ with
      | halt _ hhalt₂ => simp [hstep₁] at hhalt₂
      | cons hstep₂ htail₂ =>
          have hnext := step_deterministic hstep₁ hstep₂
          cases hnext
          exact ih htail₂

/--
A machine halts with output output iff there is a natural-number code for a
finite trace beginning at the prescribed input, following every transition,
and ending at a terminal configuration whose left counter is output.
-/
def HaltsWithOutput (p : Program) (input output : Nat) : Prop :=
  ∃ traceCode : Nat, ∃ final : Configuration,
    Nonempty (ExecutionTrace p (initialConfiguration input) (decodeTrace traceCode) final) ∧
    final.left = output

/-- The empty program halts immediately and returns its input unchanged. -/
theorem empty_program_halts (input : Nat) :
    HaltsWithOutput [] input input := by
  refine ⟨encodeTrace [initialConfiguration input], initialConfiguration input, ?_, rfl⟩
  constructor
  rw [decodeTrace_encodeTrace]
  exact ExecutionTrace.halt _ (by simp [step])

/-- The same machine and input cannot have two different halting outputs. -/
theorem halts_output_unique {p : Program} {input out₁ out₂ : Nat}
    (h₁ : HaltsWithOutput p input out₁)
    (h₂ : HaltsWithOutput p input out₂) : out₁ = out₂ := by
  rcases h₁ with ⟨code₁, final₁, run₁, output₁⟩
  rcases h₂ with ⟨code₂, final₂, run₂, output₂⟩
  rcases run₁ with ⟨trace₁⟩
  rcases run₂ with ⟨trace₂⟩
  have hfinal := trace_final_unique trace₁ trace₂
  exact output₁.symm.trans ((congrArg Configuration.left hfinal).trans output₂)

/--
The partial halting-output map, made noncomputable by classical choice.
The uniqueness theorem guarantees that the chosen witness cannot change
the output value.
-/
noncomputable def haltingOutput? (p : Program) (input : Nat) : Option Nat := by
  classical
  exact if h : ∃ output, HaltsWithOutput p input output then
    some (Classical.choose h)
  else
    none

theorem haltingOutput?_of_halts {p : Program} {input output : Nat}
    (h : HaltsWithOutput p input output) :
    haltingOutput? p input = some output := by
  classical
  unfold haltingOutput?
  have hex : ∃ output', HaltsWithOutput p input output' := ⟨output, h⟩
  rw [dite_eq_left hex]
  have hchoose : Classical.choose hex = output :=
    halts_output_unique (Classical.choose_spec hex) h
  simp [hchoose]

/-- The finite catalogue of every natural-number code from zero through bound. -/
def codesUpTo (bound : Nat) : List Nat :=
  List.range (bound + 1)

/--
Maximum halting output among all codes 0,...,bound on a fixed input.
This function is noncomputable because deciding which programs halt is
noncomputable; its value is nevertheless a uniquely specified finite maximum.
-/
noncomputable def maxHaltOutput : Nat → Nat → Nat
  | 0, input => (haltingOutput? (decodeProgram 0) input).getD 0
  | bound + 1, input =>
      max ((haltingOutput? (decodeProgram (bound + 1)) input).getD 0)
        (maxHaltOutput bound input)

/-- Every halting output in the bounded finite catalogue is at most its maximum. -/
theorem halting_output_le_maxHaltOutput
    {bound code input output : Nat}
    (hcode : code ≤ bound)
    (h : HaltsWithOutput (decodeProgram code) input output) :
    output ≤ maxHaltOutput bound input := by
  induction bound generalizing code with
  | zero =>
      have hcode0 : code = 0 := Nat.eq_zero_of_le_zero hcode
      subst code
      rw [decodeProgram_zero] at h
      simp [maxHaltOutput, haltingOutput?_of_halts h]
  | succ bound ih =>
      rcases Nat.eq_or_lt_of_le hcode with heq | hlt
      · subst code
        simp [maxHaltOutput, haltingOutput?_of_halts h]
      · exact le_trans (ih (Nat.le_of_lt_succ hlt) h) (Nat.le_max_right _ _)

/-- Finite Busy Beaver output function for this exact machine coding. -/
noncomputable def busyBeaver (bound input : Nat) : Nat :=
  maxHaltOutput bound input + 1

/-- The diagonal value exceeds every halting output in its finite catalogue. -/
theorem busyBeaver_exceeds_catalogue
    {bound code input output : Nat}
    (hcode : code ≤ bound)
    (h : HaltsWithOutput (decodeProgram code) input output) :
    output < busyBeaver bound input := by
  exact Nat.lt_succ_of_le (halting_output_le_maxHaltOutput hcode h)

/-- Code zero denotes the empty program, which immediately returns its input. -/
theorem codeZero_halts_identity (input : Nat) :
    HaltsWithOutput (decodeProgram 0) input input := by
  rw [decodeProgram_zero]
  exact empty_program_halts input

/-- The catalogue contains a machine that returns the input unchanged. -/
theorem busyBeaver_gt_input (bound input : Nat) :
    input < busyBeaver bound input := by
  exact busyBeaver_exceeds_catalogue (Nat.zero_le bound)
    (codeZero_halts_identity input)

end AssistantMachine
end HakuiKoyori
