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
@[simp] theorem stackPop_empty (base : Nat) (hbase : 0 < base) :
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

end Compiler
end HakuiKoyori
