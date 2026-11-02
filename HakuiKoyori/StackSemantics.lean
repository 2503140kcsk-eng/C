module

public import HakuiKoyori.MacroSemantics

@[expose] public section

/-!
# Arithmetic stack semantics for the TM compiler

A finite stack is represented least-significant/top digit first in a base-b
natural number.  A push of digit d onto stack code s is d + b*s.
A pop returns the Euclidean remainder as the top digit and the quotient as
the remaining stack code.  Valid digits lie below b.
-/

namespace HakuiKoyori
namespace Compiler

/-- Push one alphabet digit onto a base-b stack code. -/
def stackPush (base digit restCode : Nat) : Nat :=
  digit + base * restCode

/-- Pop returns (top digit, remaining stack code). -/
def stackPop (base stackCode : Nat) : Nat × Nat :=
  (stackCode % base, stackCode / base)

/-- Encode a list with its head at the top of the stack. -/
def encodeStack (base : Nat) : List Nat → Nat
  | [] => 0
  | digit :: rest => stackPush base digit (encodeStack base rest)

/-- All symbols in a stack alphabet are valid base-b digits. -/
def StackDigitsValid (base : Nat) (symbols : List Nat) : Prop :=
  ∀ digit ∈ symbols, digit < base

/--
Exact arithmetic inverse: when digit < base and base > 0, pop(push(d, s))
returns the original digit and tail code.
-/
theorem stackPop_stackPush (base digit restCode : Nat)
    (hbase : 0 < base) (hdigit : digit < base) :
    stackPop base (stackPush base digit restCode) = (digit, restCode) := by
  apply Prod.ext
  · change (digit + base * restCode) % base = digit
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hdigit
  · change (digit + base * restCode) / base = restCode
    rw [Nat.add_mul_div_left _ _ hbase]
    rw [Nat.div_eq_of_lt hdigit]
    simp

/-- Empty stack has blank digit zero and empty tail. -/
@[simp] theorem stackPop_empty (base : Nat) (_hbase : 0 < base) :
    stackPop base 0 = (0, 0) := by
  simp [stackPop]

/--
For every valid encoded stack, one pop recovers its top digit and the code
of its tail.  The empty stack is represented by zero and pops as blank/empty.
-/
theorem encodeStack_pop (base : Nat) (symbols : List Nat)
    (hbase : 0 < base)
    (hvalid : StackDigitsValid base symbols) :
    stackPop base (encodeStack base symbols) =
      match symbols with
      | [] => (0, 0)
      | digit :: rest => (digit, encodeStack base rest) := by
  cases symbols with
  | nil =>
      simp [encodeStack, stackPop]
  | cons digit rest =>
      have hdigit : digit < base := hvalid digit (by simp)
      simpa [encodeStack] using
        stackPop_stackPush base digit (encodeStack base rest) hbase hdigit

/--
The stack-push arithmetic is exactly the macro-level MUL followed by digit
addition.  This is a refinement at the arithmetic macro boundary, not yet
a proof that the generated primitive instruction list executes it.
-/
def stackPushViaMUL (base digit restCode : Nat) : Nat :=
  (MUL base restCode).1 + digit

theorem stackPushViaMUL_correct (base digit restCode : Nat) :
    stackPushViaMUL base digit restCode =
      stackPush base digit restCode := by
  simp [stackPushViaMUL, stackPush, MUL_correct, Nat.add_comm]


/-!
## Single-tape deterministic Turing-machine semantics

The tape is split around the current cell.  The left and right stacks store
cells nearest-first; an empty stack denotes an unbounded blank tail.  The
current cell is explicit.  Moving right pushes the written cell onto the
left stack and pops the right stack; moving left is symmetric.
-/

/-- Direction of a single-tape Turing-machine head movement. -/
inductive TapeMove where
  | left
  | right
  | stay
deriving DecidableEq, Repr

/-- One transition-table entry: new state, symbol written, and head movement. -/
structure TMAction where
  nextState : Nat
  writeSymbol : Nat
  move : TapeMove
deriving DecidableEq, Repr

/-- A deterministic transition table; none means that the machine halts. -/
abbrev TMDelta := Nat → Nat → Option TMAction

/-- Tape configuration with the two sides represented by arithmetic stack codes. -/
structure TMConfiguration where
  state : Nat
  leftStack : Nat
  current : Nat
  rightStack : Nat
deriving DecidableEq, Repr

/--
One transition of the encoded single-tape Turing machine.  The base is the
stack alphabet radix; the blank symbol is zero.
-/
def turingStep (base : Nat) (delta : TMDelta)
    (configuration : TMConfiguration) : Option TMConfiguration :=
  match delta configuration.state configuration.current with
  | none => none
  | some action =>
      match action.move with
      | .stay =>
          some { state := action.nextState
                 leftStack := configuration.leftStack
                 current := action.writeSymbol
                 rightStack := configuration.rightStack }
      | .right =>
          let popped := stackPop base configuration.rightStack
          some { state := action.nextState
                 leftStack := stackPush base action.writeSymbol configuration.leftStack
                 current := popped.1
                 rightStack := popped.2 }
      | .left =>
          let popped := stackPop base configuration.leftStack
          some { state := action.nextState
                 leftStack := popped.2
                 current := popped.1
                 rightStack := stackPush base action.writeSymbol configuration.rightStack }

/-- The encoded Turing-machine transition is deterministic. -/
theorem turingStep_deterministic {base : Nat} {delta : TMDelta}
    {configuration next₁ next₂ : TMConfiguration}
    (h₁ : turingStep base delta configuration = some next₁)
    (h₂ : turingStep base delta configuration = some next₂) :
    next₁ = next₂ := by
  exact Option.some.inj (h₁.symm.trans h₂)

/-- The encoded Turing machine halts exactly when its transition table is undefined. -/
theorem turingStep_none_iff {base : Nat} {delta : TMDelta}
    {configuration : TMConfiguration} :
    turingStep base delta configuration = none ↔
      delta configuration.state configuration.current = none := by
  constructor
  · intro hstep
    cases hdelta : delta configuration.state configuration.current with
    | none => rfl
    | some action =>
        cases action.move <;>
          simp [turingStep, hdelta] at hstep <;>
          contradiction
  · intro hdelta
    rw [hdelta]
    rfl

/-- One step with a stay action only changes the state and current symbol. -/
theorem turingStep_stay {base : Nat} {delta : TMDelta}
    {configuration : TMConfiguration} {action : TMAction}
    (h : delta configuration.state configuration.current = some action)
    (hm : action.move = .stay) :
    turingStep base delta configuration =
      some { state := action.nextState
             leftStack := configuration.leftStack
             current := action.writeSymbol
             rightStack := configuration.rightStack } := by
  simp [turingStep, h, hm]

/-- One step to the right pushes the written symbol left and pops the right stack. -/
theorem turingStep_right {base : Nat} {delta : TMDelta}
    {configuration : TMConfiguration} {action : TMAction}
    (h : delta configuration.state configuration.current = some action)
    (hm : action.move = .right) :
    turingStep base delta configuration =
      some { state := action.nextState
             leftStack := stackPush base action.writeSymbol configuration.leftStack
             current := (stackPop base configuration.rightStack).1
             rightStack := (stackPop base configuration.rightStack).2 } := by
  simp [turingStep, h, hm]

/-- One step to the left pushes the written symbol right and pops the left stack. -/
theorem turingStep_left {base : Nat} {delta : TMDelta}
    {configuration : TMConfiguration} {action : TMAction}
    (h : delta configuration.state configuration.current = some action)
    (hm : action.move = .left) :
    turingStep base delta configuration =
      some { state := action.nextState
             leftStack := (stackPop base configuration.leftStack).2
             current := (stackPop base configuration.leftStack).1
             rightStack := stackPush base action.writeSymbol configuration.rightStack } := by
  simp [turingStep, h, hm]


end Compiler
end HakuiKoyori
