module

public import HakuiKoyori.StackSemantics

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

end Compiler
end HakuiKoyori
