/-
  Hakui Koyori Number — milestone 0
  A finite, set-theory-free diagonal construction over a small arithmetic
  language of total unary programs.

  This file intentionally makes no claim about the Large Number Garden Number.
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

/--
Milestone-0 Hakui Koyori Number candidate:
diagonalize again at the first harvest.
-/
def hakuiKoyoriNumber : Nat :=
  diagonal firstHarvest

/--
Main theorem: HKN_0 exceeds every program in this explicit arithmetic
language whose syntax depth is at most firstHarvest, evaluated at firstHarvest.
-/
theorem hakuiKoyoriNumber_dominates_catalogue
    (p : AssistantCode) (h : depth p ≤ firstHarvest) :
    evaluate p firstHarvest < hakuiKoyoriNumber := by
  unfold hakuiKoyoriNumber
  exact diagonal_gt_assistant firstHarvest p
    (mem_assistants_of_depth_le p h)

/-- In particular, the candidate is strictly greater than its first harvest. -/
theorem hakuiKoyoriNumber_gt_firstHarvest :
    firstHarvest < hakuiKoyoriNumber := by
  have hmem : AssistantCode.input ∈ assistants firstHarvest :=
    mem_assistants_of_depth_le AssistantCode.input (Nat.zero_le _)
  have h := diagonal_gt_assistant firstHarvest AssistantCode.input hmem
  simpa [evaluate, hakuiKoyoriNumber] using h

end HakuiKoyori
