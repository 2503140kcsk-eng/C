import HakuiKoyori.AssistantMachine
import HakuiKoyori.Simulation
import HakuiKoyori.CompilerCore
import HakuiKoyori.LowLevelMacros

/- 
  Hakui Koyori Number — milestone 0 plus the M1 machine extension.
  M0 remains a finite set-theory-free diagonal construction over a small
  arithmetic language. M1 adds an explicit two-counter machine Busy Beaver
  candidate; its verification status is the GitHub Actions status of this commit.
-/

namespace HakuiKoyori

/-- Apply a total unary function a finite number of times. -/
def iterateNat (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => f (iterateNat f k x)

/--
A finite arithmetic assistant program.

* input          : return the input
* zero / one     : constants
* successor      : add one
* double         : multiply by two
* square         : square the value
* selfPower      : raise the value to itself
* repeatAtInput  : apply the inner program n times at input n
-/
inductive AssistantCode where
  | input
  | zero
  | one
  | successor (inner : AssistantCode)
  | double (inner : AssistantCode)
  | square (inner : AssistantCode)
  | selfPower (inner : AssistantCode)
  | repeatAtInput (inner : AssistantCode)
deriving DecidableEq, Repr

/-- Syntax depth of an assistant program. -/
def depth : AssistantCode → Nat
  | .input => 0
  | .zero => 0
  | .one => 0
  | .successor p => depth p + 1
  | .double p => depth p + 1
  | .square p => depth p + 1
  | .selfPower p => depth p + 1
  | .repeatAtInput p => depth p + 1

/-- Total semantics of the arithmetic assistant language. -/
def evaluate : AssistantCode → Nat → Nat
  | .input, n => n
  | .zero, _ => 0
  | .one, _ => 1
  | .successor p, n => evaluate p n + 1
  | .double p, n => 2 * evaluate p n
  | .square p, n => evaluate p n * evaluate p n
  | .selfPower p, n => evaluate p n ^ evaluate p n
  | .repeatAtInput p, n => iterateNat (evaluate p) n n

/-- Apply every one-step laboratory operation to a finite catalogue. -/
def extendCatalogue (xs : List AssistantCode) : List AssistantCode :=
  xs.map AssistantCode.successor ++
  xs.map AssistantCode.double ++
  xs.map AssistantCode.square ++
  xs.map AssistantCode.selfPower ++
  xs.map AssistantCode.repeatAtInput

/--
The finite catalogue A_n of all codes of syntax depth at most n.
Each stage retains the previous assistants and adds every one-step extension.
-/
def assistants : Nat → List AssistantCode
  | 0 => [.input, .zero, .one]
  | n + 1 => assistants n ++ extendCatalogue (assistants n)

/-- Every program occurs in the catalogue at its own syntax depth. -/
theorem mem_assistants_at_depth (p : AssistantCode) :
    p ∈ assistants (depth p) := by
  induction p with
  | input => simp [depth, assistants]
  | zero => simp [depth, assistants]
  | one => simp [depth, assistants]
  | successor p ih => simp [depth, assistants, extendCatalogue, ih]
  | double p ih => simp [depth, assistants, extendCatalogue, ih]
  | square p ih => simp [depth, assistants, extendCatalogue, ih]
  | selfPower p ih => simp [depth, assistants, extendCatalogue, ih]
  | repeatAtInput p ih => simp [depth, assistants, extendCatalogue, ih]

/-- The catalogue is monotone in its depth bound. -/
theorem assistants_mono {m n : Nat} (h : m ≤ n) :
    ∀ {p : AssistantCode}, p ∈ assistants m → p ∈ assistants n := by
  induction h with
  | refl =>
      intro p hp
      exact hp
  | @step n h ih =>
      intro p hp
      change p ∈ assistants n ++ extendCatalogue (assistants n)
      exact List.mem_append.mpr (Or.inl (ih hp))

/-- Every program with depth at most n is in A_n. -/
theorem mem_assistants_of_depth_le (p : AssistantCode) {n : Nat}
    (h : depth p ≤ n) : p ∈ assistants n :=
  assistants_mono h (mem_assistants_at_depth p)

/-- Maximum of a finite list of natural numbers. -/
def maxNatList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxNatList xs)

/-- Every member of a finite list is at most its maximum. -/
theorem member_le_maxNatList (x : Nat) :
    ∀ xs : List Nat, x ∈ xs → x ≤ maxNatList xs := by
  intro xs
  induction xs with
  | nil =>
      intro hx
      cases hx
  | cons y ys ih =>
      intro hx
      rcases List.mem_cons.mp hx with hxy | hys
      · rw [hxy]
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hys) (Nat.le_max_right _ _)

/-- Largest output among the finite assistant catalogue A_n, at input n. -/
def maximumAssistantOutput (n : Nat) : Nat :=
  maxNatList ((assistants n).map (fun p => evaluate p n))

/-- The diagonal output: one more than every output in A_n at input n. -/
def diagonal (n : Nat) : Nat :=
  maximumAssistantOutput n + 1

/--
Diagonal dominance: every assistant program of depth at most n has
strictly smaller output at n than diagonal n.
-/
theorem diagonal_gt_assistant (n : Nat) (p : AssistantCode)
    (h : p ∈ assistants n) :
    evaluate p n < diagonal n := by
  unfold diagonal maximumAssistantOutput
  apply Nat.lt_succ_of_le
  apply member_le_maxNatList
  exact List.mem_map.mpr ⟨p, h, rfl⟩

/-- A finite tower used as the initial research input. -/
def tenTower : Nat → Nat
  | 0 => 1
  | n + 1 => 10 ^ tenTower n

/-- First harvest: diagonalize all assistant programs up to depth 10↑↑10. -/
def firstHarvest : Nat :=
  diagonal (tenTower 10)

/-- Milestone-0 HKN candidate: diagonalize again at the first harvest. -/
def hakuiKoyoriNumber : Nat :=
  diagonal firstHarvest

/--
M0 main theorem: HKN_0 exceeds every program in this explicit arithmetic
language whose syntax depth is at most firstHarvest, evaluated at firstHarvest.
-/
theorem hakuiKoyoriNumber_dominates_catalogue
    (p : AssistantCode) (h : depth p ≤ firstHarvest) :
    evaluate p firstHarvest < hakuiKoyoriNumber := by
  unfold hakuiKoyoriNumber
  exact diagonal_gt_assistant firstHarvest p
    (mem_assistants_of_depth_le p h)

/-- HKN_0 exceeds the identity assistant at the first-harvest input. -/
theorem hakuiKoyoriNumber_gt_identity_at_firstHarvest :
    evaluate AssistantCode.input firstHarvest < hakuiKoyoriNumber :=
  hakuiKoyoriNumber_dominates_catalogue AssistantCode.input (Nat.zero_le _)

/--
M1 candidate: one more than every halting output of a machine whose natural
program code is at most HKN_0, on input HKN_0.
-/
noncomputable def hakuiKoyoriNumber1 : Nat :=
  AssistantMachine.busyBeaver hakuiKoyoriNumber hakuiKoyoriNumber

/-- M1 diagonal theorem: the new candidate is strictly greater than HKN_0. -/
theorem hakuiKoyoriNumber1_gt_hakuiKoyoriNumber :
    hakuiKoyoriNumber < hakuiKoyoriNumber1 := by
  unfold hakuiKoyoriNumber1
  exact AssistantMachine.busyBeaver_gt_input
    hakuiKoyoriNumber hakuiKoyoriNumber

/--
Every halting machine with code at most HKN_0, when run on input HKN_0,
produces an output strictly below HKN_1.
-/
theorem hakuiKoyoriNumber1_dominates_bounded_machine_catalogue
    (code output : Nat) (hcode : code ≤ hakuiKoyoriNumber)
    (hhalts :
      AssistantMachine.HaltsWithOutput
        (AssistantMachine.decodeProgram code)
        hakuiKoyoriNumber output) :
    output < hakuiKoyoriNumber1 := by
  unfold hakuiKoyoriNumber1
  exact AssistantMachine.busyBeaver_exceeds_catalogue hcode hhalts

end HakuiKoyori
