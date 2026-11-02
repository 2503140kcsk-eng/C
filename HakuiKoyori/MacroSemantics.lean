module

public import HakuiKoyori.LowLevelMacros

@[expose] public section

/-!
# Abstract operational semantics for MUL and TR

This file formalizes the loop-header semantics of the concrete instruction
templates in LowLevelMacros.lean.  One transition below denotes one complete
return to a macro loop header, not one primitive ISA instruction.  The
refinement theorem connecting these macro transitions to AssistantMachine.step
is a separate obligation and is deliberately not claimed here.
-/

namespace HakuiKoyori
namespace Compiler

/-- The values of the two physical counters at a macro boundary. -/
abbrev CounterPair := Nat × Nat

/--
One outer MUL iteration consumes one unit of the data counter and adds the
fixed factor to the scratch counter.
-/
def mulOuterRound (factor : Nat) (s : CounterPair) : CounterPair :=
  (s.1 - 1, s.2 + factor)

/--
After k completed outer iterations, A = input-k and B = factor*k.
This is the invariant at visits to the MUL outer-loop header.
-/
def mulOuterState (factor input k : Nat) : CounterPair :=
  (input - k, factor * k)

/-- One transfer iteration consumes one unit of B and adds one unit to A. -/
def mulTransferRound (s : CounterPair) : CounterPair :=
  (s.1 + 1, s.2 - 1)

/-- After k completed transfer iterations, A=k and B=factor*input-k. -/
def mulTransferState (factor input k : Nat) : CounterPair :=
  (k, factor * input - k)

/--
Execute the abstract MUL outer loop.  Recursion is on the current value of A,
which is exactly the first loop's termination variant.
-/
def mulOuterRun (factor : Nat) : Nat → Nat → CounterPair
  | 0, b => (0, b)
  | a + 1, b => mulOuterRun factor a (b + factor)

/--
Execute the abstract MUL transfer loop.  Recursion is on B, the second
loop's termination variant.
-/
def mulTransferRun : Nat → Nat → CounterPair
  | a, 0 => (a, 0)
  | a, b + 1 => mulTransferRun (a + 1) b

/--
The macro-level execution semantics of MUL(factor): starting from (input,0),
consume A into B in the first loop, then transfer B back into A.
-/
def MUL (factor input : Nat) : CounterPair :=
  let (a, b) := mulOuterRun factor input 0
  mulTransferRun a b

/-- The outer-loop recurrence preserves the stated affine invariant. -/
theorem mul_outer_loop_invariant_step {factor input k : Nat}
    (hk : k < input) :
    mulOuterState factor input (k + 1) =
      mulOuterRound factor (mulOuterState factor input k) := by
  simp [mulOuterState, mulOuterRound, Nat.mul_succ]
  omega

/-- The transfer-loop recurrence preserves its stated affine invariant. -/
theorem mul_transfer_loop_invariant_step {factor input k : Nat}
    (hk : k < factor * input) :
    mulTransferState factor input (k + 1) =
      mulTransferRound (mulTransferState factor input k) := by
  simp [mulTransferState, mulTransferRound]
  omega

@[simp] theorem mul_outer_loop_initial (factor input : Nat) :
    mulOuterState factor input 0 = (input, 0) := by
  simp [mulOuterState]

@[simp] theorem mul_outer_loop_exit (factor input : Nat) :
    mulOuterState factor input input = (0, factor * input) := by
  simp [mulOuterState]

@[simp] theorem mul_transfer_loop_initial (factor input : Nat) :
    mulTransferState factor input 0 = (0, factor * input) := by
  simp [mulTransferState]

@[simp] theorem mul_transfer_loop_exit (factor input : Nat) :
    mulTransferState factor input (factor * input) = (factor * input, 0) := by
  simp [mulTransferState]

/-- Closed form for the first MUL loop, including its full loop invariant. -/
theorem mulOuterRun_spec (factor input b : Nat) :
    mulOuterRun factor input b = (0, b + factor * input) := by
  induction input with
  | zero =>
      simp [mulOuterRun]
  | succ input ih =>
      simp only [mulOuterRun]
      rw [ih]
      simp only [Nat.mul_succ, Prod.mk.injEq]
      constructor
      · rfl
      · omega

/-- Closed form for the second MUL loop. -/
theorem mulTransferRun_spec (a b : Nat) :
    mulTransferRun a b = (a + b, 0) := by
  induction b generalizing a with
  | zero =>
      simp [mulTransferRun]
  | succ b ih =>
      simp only [mulTransferRun]
      rw [ih]
      simp only [Prod.mk.injEq]
      constructor
      · omega
      · rfl

/-- Kernel-checked macro-level correctness of MUL. -/
theorem MUL_correct (factor input : Nat) :
    MUL factor input = (factor * input, 0) := by
  simp [MUL, mulOuterRun_spec, mulTransferRun_spec]

/-- The first MUL loop strictly decreases A on each completed back-edge. -/
theorem mul_outer_variant_decreases (a : Nat) (h : 0 < a) :
    a - 1 < a := by
  omega

/-- The second MUL loop strictly decreases B on each completed back-edge. -/
theorem mul_transfer_variant_decreases (b : Nat) (h : 0 < b) :
    b - 1 < b := by
  omega

/--
The abstract TR loop consumes one unit of B and adds m units to A.  When B
reaches zero, the finite-control remainder r is added and the macro exits.
-/
def trLoopRound (m : Nat) (s : CounterPair) : CounterPair :=
  (s.1 + m, s.2 - 1)

/-- After k full TR iterations, A = m*k and B = q-k. -/
def trLoopState (m q k : Nat) : CounterPair :=
  (m * k, q - k)

/--
Execute TR(m,r) from a general pair (a,q).  The recursion parameter q is the
right-counter value and therefore the loop's termination variant.
-/
def trRun (m r : Nat) : Nat → Nat → CounterPair
  | a, 0 => (a + r, 0)
  | a, b + 1 => trRun m r (a + m) b

/-- Macro-level execution semantics of TR(m,r), from input (0,q). -/
def TR (m r q : Nat) : CounterPair :=
  trRun m r 0 q

/-- The TR loop recurrence preserves its stated quotient invariant. -/
theorem tr_loop_invariant_step {m q k : Nat}
    (hk : k < q) :
    trLoopState m q (k + 1) =
      trLoopRound m (trLoopState m q k) := by
  simp [trLoopState, trLoopRound, Nat.mul_succ]
  omega

@[simp] theorem tr_loop_initial (m q : Nat) :
    trLoopState m q 0 = (0, q) := by
  simp [trLoopState]

@[simp] theorem tr_loop_exit (m q : Nat) :
    trLoopState m q q = (m * q, 0) := by
  simp [trLoopState]

/-- Exact closed-form semantics of the TR loop, including the remainder. -/
theorem trRun_spec (m r a q : Nat) :
    trRun m r a q = (a + m * q + r, 0) := by
  induction q generalizing a with
  | zero =>
      simp [trRun]
  | succ q ih =>
      simp only [trRun]
      rw [ih]
      simp only [Nat.mul_succ, Prod.mk.injEq]
      constructor
      · omega
      · rfl

/-- Kernel-checked macro-level correctness of TR(m,r). -/
theorem TR_correct (m r q : Nat) :
    TR m r q = (m * q + r, 0) := by
  simpa [TR] using trRun_spec m r 0 q

/-- Every non-final TR back-edge strictly decreases B. -/
theorem tr_loop_variant_decreases (b : Nat) (h : 0 < b) :
    b - 1 < b := by
  omega

end Compiler
end HakuiKoyori
