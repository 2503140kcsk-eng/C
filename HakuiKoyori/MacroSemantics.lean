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
    (_hk : k < input) :
    mulOuterState factor input (k + 1) =
      mulOuterRound factor (mulOuterState factor input k) := by
  simp [mulOuterState, mulOuterRound, Nat.mul_succ]
  omega

/-- The transfer-loop recurrence preserves its stated affine invariant. -/
theorem mul_transfer_loop_invariant_step {factor input k : Nat}
    (_hk : k < factor * input) :
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
  induction input generalizing b with
  | zero =>
      simp [mulOuterRun]
  | succ input ih =>
      simp only [mulOuterRun]
      rw [ih (b + factor)]
      simp only [Nat.mul_succ, Prod.mk.injEq]
      constructor
      · trivial
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
      · trivial

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
    (_hk : k < q) :
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


/-!
## DIVREM: quotient/remainder phase semantics

The concrete instruction generator in LowLevelMacros.lean removes groups of p
units from A, increments B once per group, then scans the final residue in
finite control.  If the residue is zero it transfers B to A with TR(1,0);
otherwise it restores the original value with TR(p,r).  The definitions below
formalize each loop-header invariant and the combined result.
-/

/-- After k complete groups, A = input-p*k and B = k. -/
def divRemGroupState (p input k : Nat) : CounterPair :=
  (input - p * k, k)

/-- One complete quotient-group iteration consumes p from A and increments B. -/
def divRemGroupRound (s : CounterPair) (p : Nat) : CounterPair :=
  (s.1 - p, s.2 + 1)

/--
The group-loop invariant is preserved whenever another complete group fits
inside the remaining data counter.
-/
theorem divRem_group_loop_invariant_step {p input k : Nat}
    (_hfit : p * (k + 1) ≤ input) :
    divRemGroupState p input (k + 1) =
      divRemGroupRound (divRemGroupState p input k) p := by
  simp [divRemGroupState, divRemGroupRound, Nat.mul_succ]
  omega

@[simp] theorem divRem_group_loop_initial (p input : Nat) :
    divRemGroupState p input 0 = (input, 0) := by
  simp [divRemGroupState]

/-- The group loop exits with the Euclidean remainder in A and quotient in B. -/
theorem divRem_group_loop_exit (p input : Nat) :
    divRemGroupState p input (input / p) = (input % p, input / p) := by
  have h := Nat.mod_add_div input p
  simp [divRemGroupState]
  omega

/-- The remainder left at the end of the group loop is smaller than p. -/
theorem divRem_group_remainder_bound {p input : Nat} (hp : 0 < p) :
    input % p < p :=
  Nat.mod_lt input hp

/-- A successful group iteration strictly decreases A for every p>0. -/
theorem divRem_group_variant_decreases {p a : Nat}
    (hp : 0 < p) (hfit : p ≤ a) :
    a - p < a := by
  omega

/-- After j positive residue tests, A = remainder-j and B remains quotient. -/
def divRemResidueState (remainder quotient j : Nat) : CounterPair :=
  (remainder - j, quotient)

/-- A positive residue test decrements A once and leaves B untouched. -/
def divRemResidueRound (s : CounterPair) : CounterPair :=
  (s.1 - 1, s.2)

/-- The residue-scan invariant is preserved while the current test is positive. -/
theorem divRem_residue_loop_invariant_step {remainder quotient j : Nat}
    (_hpositive : j < remainder) :
    divRemResidueState remainder quotient (j + 1) =
      divRemResidueRound (divRemResidueState remainder quotient j) := by
  simp [divRemResidueState, divRemResidueRound]
  omega

@[simp] theorem divRem_residue_loop_initial (remainder quotient : Nat) :
    divRemResidueState remainder quotient 0 = (remainder, quotient) := by
  simp [divRemResidueState]

@[simp] theorem divRem_residue_loop_exit (remainder quotient : Nat) :
    divRemResidueState remainder quotient remainder = (0, quotient) := by
  simp [divRemResidueState]

/-- Each positive residue-test back-edge strictly decreases A. -/
theorem divRem_residue_variant_decreases (a : Nat)
    (hpositive : 0 < a) : a - 1 < a := by
  omega

/-- The final TR handler selected by the finite-control remainder test. -/
def divRemHandler (p remainder quotient : Nat) : CounterPair :=
  if remainder = 0 then TR 1 0 quotient else TR p remainder quotient

/--
If the residue is zero, the handler returns the quotient.  Otherwise it
reconstructs p*quotient+remainder, i.e. the original input.
-/
theorem divRem_handler_correct (p remainder quotient : Nat) :
    divRemHandler p remainder quotient =
      if remainder = 0 then (quotient, 0)
      else (p * quotient + remainder, 0) := by
  by_cases hr : remainder = 0
  · simp [divRemHandler, hr, TR_correct]
  · simp [divRemHandler, hr, TR_correct]

/--
Macro-level semantics of the whole quotient/remainder zero-test block.
Its precondition is p>0; the result is the quotient exactly when the
remainder vanishes, and otherwise the original input is restored.
-/
def DIVREM (p input : Nat) : CounterPair :=
  divRemHandler p (input % p) (input / p)

/-- Kernel-checked correctness of the abstract DIVREM macro. -/
theorem DIVREM_correct {p input : Nat} (_hp : 0 < p) :
    DIVREM p input =
      if input % p = 0 then (input / p, 0) else (input, 0) := by
  unfold DIVREM
  by_cases hr : input % p = 0
  · simp [divRemHandler, hr, TR_correct]
  · have hdiv := Nat.mod_add_div input p
    simp [divRemHandler, hr, TR_correct]
    omega


end Compiler
end HakuiKoyori
