module

public import HakuiKoyori.StackSemantics
public import HakuiKoyori.CompilerCore

public section

/-!
# A finite, typed source model for the M2 tape compiler

StackSemantics.lean gives the elementary Nat-valued tape equations.  A
compiler, however, must consume a finite transition table.  This module
packages states and symbols as Fin types and proves that its typed step
agrees exactly with the existing explicit-current Nat semantics.

The current cell is a field of the configuration.  The left and right stack
codes contain only cells strictly on the corresponding side of the head.
-/

namespace HakuiKoyori
namespace Compiler

/-- A finite Turing action cannot leave the declared state or alphabet. -/
structure FiniteTMAction (stateCount alphabetSize : Nat) where
  nextState : Fin stateCount
  writeSymbol : Fin alphabetSize
  move : TapeMove

/-- A finite deterministic one-tape TM with blank symbol coded by zero. -/
structure FiniteTuringMachine where
  stateCount : Nat
  alphabetSize : Nat
  stateCount_pos : 0 < stateCount
  alphabetSize_pos : 0 < alphabetSize
  transition :
    Fin stateCount → Fin alphabetSize →
      Option (FiniteTMAction stateCount alphabetSize)

/-- Configuration whose state and explicit current symbol are in finite types. -/
structure FiniteTMConfiguration (M : FiniteTuringMachine) where
  state : Fin M.stateCount
  leftStack : Nat
  current : Fin M.alphabetSize
  rightStack : Nat

/-- Forget the Fin proofs while retaining the existing stack representation. -/
def toNatTMConfiguration {M : FiniteTuringMachine}
    (c : FiniteTMConfiguration M) : TMConfiguration :=
  { state := c.state.val
    leftStack := c.leftStack
    current := c.current.val
    rightStack := c.rightStack }

/-- Embed the finite transition table into the Nat-valued semantic interface. -/
def finiteTMDelta (M : FiniteTuringMachine) : TMDelta :=
  fun q a =>
    if hq : q < M.stateCount then
      if ha : a < M.alphabetSize then
        match M.transition ⟨q, hq⟩ ⟨a, ha⟩ with
        | none => none
        | some action =>
            some
              { nextState := action.nextState.val
                writeSymbol := action.writeSymbol.val
                move := action.move }
      else none
    else none

/-- The typed operational semantics, retaining the current symbol explicitly. -/
def finiteTMStep (M : FiniteTuringMachine)
    (c : FiniteTMConfiguration M) :
    Option (FiniteTMConfiguration M) :=
  match M.transition c.state c.current with
  | none => none
  | some action =>
      match action.move with
      | .stay =>
          some
            { state := action.nextState
              leftStack := c.leftStack
              current := action.writeSymbol
              rightStack := c.rightStack }
      | .right =>
          let popped := stackPop M.alphabetSize c.rightStack
          some
            { state := action.nextState
              leftStack :=
                stackPush M.alphabetSize action.writeSymbol.val c.leftStack
              current := ⟨popped.1, Nat.mod_lt _ M.alphabetSize_pos⟩
              rightStack := popped.2 }
      | .left =>
          let popped := stackPop M.alphabetSize c.leftStack
          some
            { state := action.nextState
              leftStack := popped.2
              current := ⟨popped.1, Nat.mod_lt _ M.alphabetSize_pos⟩
              rightStack :=
                stackPush M.alphabetSize action.writeSymbol.val c.rightStack }

/-- The finite typed TM step is deterministic. -/
theorem finiteTMStep_deterministic
    {M : FiniteTuringMachine} {c : FiniteTMConfiguration M}
    {a b : FiniteTMConfiguration M}
    (ha : finiteTMStep M c = some a)
    (hb : finiteTMStep M c = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- Halting is exactly an undefined transition-table entry. -/
theorem finiteTMStep_none_iff
    {M : FiniteTuringMachine} {c : FiniteTMConfiguration M} :
    finiteTMStep M c = none ↔ M.transition c.state c.current = none := by
  cases h : M.transition c.state c.current with
  | none => simp [finiteTMStep, h]
  | some action =>
      cases hm : action.move <;> simp [finiteTMStep, h, hm]

/--
Commuting theorem: erase the Fin proofs before or after one step and the
result is identical.  Thus the finite typed model is not a second, divergent
semantics; it is a finite-input restriction of StackSemantics.turingStep.
-/
theorem finiteTMStep_toNat_compatible
    (M : FiniteTuringMachine) (c : FiniteTMConfiguration M) :
    turingStep M.alphabetSize (finiteTMDelta M)
        (toNatTMConfiguration c) =
      Option.map toNatTMConfiguration (finiteTMStep M c) := by
  cases h : M.transition c.state c.current with
  | none =>
      simp [finiteTMStep, finiteTMDelta, turingStep,
        toNatTMConfiguration, c.state.isLt, c.current.isLt, h]
  | some action =>
      cases hm : action.move with
      | stay =>
          simp [finiteTMStep, finiteTMDelta, turingStep,
            toNatTMConfiguration, c.state.isLt, c.current.isLt, h, hm]
      | right =>
          simp [finiteTMStep, finiteTMDelta, turingStep,
            toNatTMConfiguration, c.state.isLt, c.current.isLt, h, hm,
            stackPop]
      | left =>
          simp [finiteTMStep, finiteTMDelta, turingStep,
            toNatTMConfiguration, c.state.isLt, c.current.isLt, h, hm,
            stackPop]

/-!
## Explicit unary input codec and bootstrap

The TM head symbol is explicit in FiniteTMConfiguration. A fixed M1 entry
PC cannot depend on whether the input is empty, so the initial symbol is
encoded in the virtual scratch exponent and decoded by one bootstrap
instruction. After bootstrap, the scratch register is zero and the
finite-control PC records the current symbol.
-/

/-- The finite alphabet is relabelled so blank is 0 and unary input/output is 1. -/
structure UnaryInputSpec (M : FiniteTuringMachine) where
  unarySymbol : Fin M.alphabetSize
  unarySymbol_val_eq_one : unarySymbol.val = 1

/-- Blank is the alphabet digit zero. -/
def blankSymbol (M : FiniteTuringMachine) : Fin M.alphabetSize :=
  ⟨0, M.alphabetSize_pos⟩

/-- The code of a stack containing exactly n copies of the unary symbol 1. -/
def unaryStackCode (M : FiniteTuringMachine)
    (U : UnaryInputSpec M) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      stackPush M.alphabetSize U.unarySymbol.val
        (unaryStackCode M U n)

/-- The successor equation for the unary stack code. -/
@[simp] theorem unaryStackCode_succ
    (M : FiniteTuringMachine) (U : UnaryInputSpec M) (n : Nat) :
    unaryStackCode M U (n + 1) =
      1 + M.alphabetSize * unaryStackCode M U n := by
  simp [unaryStackCode, U.unarySymbol_val_eq_one]

/-- A pop from a nonempty unary stack returns 1 and the remaining tail. -/
theorem stackPop_unaryStackCode_succ
    (M : FiniteTuringMachine) (U : UnaryInputSpec M) (n : Nat) :
    stackPop M.alphabetSize (unaryStackCode M U (n + 1)) =
      (1, unaryStackCode M U n) := by
  simpa [unaryStackCode, U.unarySymbol_val_eq_one] using
    stackPop_stackPush M.alphabetSize U.unarySymbol.val
      (unaryStackCode M U n) M.alphabetSize_pos U.unarySymbol.isLt

/-- The typed source input with the head cell stored in current, not in either stack. -/
def unaryInputConfiguration (M : FiniteTuringMachine)
    (q0 : Fin M.stateCount) (U : UnaryInputSpec M) :
    Nat → FiniteTMConfiguration M
  | 0 =>
      { state := q0
        leftStack := 0
        current := blankSymbol M
        rightStack := 0 }
  | n + 1 =>
      { state := q0
        leftStack := 0
        current := U.unarySymbol
        rightStack := unaryStackCode M U n }

/-- The initial virtual registers before the fixed-PC bootstrap instruction. -/
def unaryInputRegisters (M : FiniteTuringMachine)
    (U : UnaryInputSpec M) : Nat → Registers3
  | 0 => ⟨0, 0, 0⟩
  | n + 1 => ⟨1, 0, unaryStackCode M U n⟩

/-- Exact M1 numeric code for the unary input, before bootstrap. -/
def unaryInputCode (M : FiniteTuringMachine)
    (U : UnaryInputSpec M) (n : Nat) : Nat :=
  let r := unaryInputRegisters M U n
  primeCode r.r0 r.r1 r.r2

@[simp] theorem unaryInputCode_zero
    (M : FiniteTuringMachine) (U : UnaryInputSpec M) :
    unaryInputCode M U 0 = 1 := by
  simp [unaryInputCode, unaryInputRegisters, primeCode]

@[simp] theorem unaryInputCode_succ
    (M : FiniteTuringMachine) (U : UnaryInputSpec M) (n : Nat) :
    unaryInputCode M U (n + 1) =
      2 * 5 ^ unaryStackCode M U n := by
  simp [unaryInputCode, unaryInputRegisters, primeCode]

/-- The first 3-register instruction decodes the input head symbol. -/
def unaryBootstrapInstruction (unaryPC : Nat) : Instruction3 :=
  .decJump .r0 unaryPC

/-- Empty input takes the zero branch and leaves the scratch/register code empty. -/
theorem unaryBootstrap_empty
    (M : FiniteTuringMachine) (U : UnaryInputSpec M)
    (unaryPC : Nat) (tail : Program3) :
    step3 (unaryBootstrapInstruction unaryPC :: tail)
      ⟨0, unaryInputRegisters M U 0⟩ =
      some ⟨1, unaryInputRegisters M U 0⟩ := by
  simp [step3, unaryBootstrapInstruction, unaryInputRegisters,
    read3, write3, setPC3]

/-- Nonempty unary input is decoded to current symbol 1 and a zero scratch register. -/
theorem unaryBootstrap_nonempty
    (M : FiniteTuringMachine) (U : UnaryInputSpec M)
    (unaryPC n : Nat) (tail : Program3) :
    step3 (unaryBootstrapInstruction unaryPC :: tail)
      ⟨0, unaryInputRegisters M U (n + 1)⟩ =
      some ⟨unaryPC, ⟨0, 0, unaryStackCode M U n⟩⟩ := by
  simp [step3, unaryBootstrapInstruction, unaryInputRegisters,
    read3, write3, setPC3]


end Compiler
end HakuiKoyori
