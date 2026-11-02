module

public import HakuiKoyori.AssistantMachine
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Ring

public section

/-!
# Compiler foundations (M2)

This module introduces the three-register source machine used as an
intermediate representation between a tape machine and the existing
two-counter target machine.

The prime-power representation is

  code(a,b,c) = 2^a * 3^b * 5^c.

The theorems below establish the arithmetic part of the representation:
incrementing a virtual register multiplies the code by its assigned prime;
decrementing a positive virtual register divides out that prime; and
divisibility by 2, 3, and 5 tests the corresponding virtual register exactly.

This is a verified foundation, not yet the emitted low-level compiler.
In particular, this file does not claim that the arithmetic identities
alone implement the required loops using AssistantMachine.Instruction.
-/

namespace HakuiKoyori
namespace Compiler

/-- The three virtual registers of the intermediate machine. -/
inductive Register3 where
  | r0
  | r1
  | r2
deriving DecidableEq, Repr

/-- The values stored in the three virtual registers. -/
structure Registers3 where
  r0 : Nat
  r1 : Nat
  r2 : Nat
deriving DecidableEq, Repr

/-- Read one virtual register. -/
@[expose]
def read3 (r : Registers3) : Register3 → Nat
  | .r0 => r.r0
  | .r1 => r.r1
  | .r2 => r.r2

/-- Update one virtual register. -/
@[expose]
def write3 (r : Registers3) (which : Register3) (value : Nat) : Registers3 :=
  match which with
  | .r0 => { r with r0 := value }
  | .r1 => { r with r1 := value }
  | .r2 => { r with r2 := value }

/-- Intermediate instruction set: increment and conditional decrement/jump. -/
inductive Instruction3 where
  | inc (which : Register3)
  | decJump (which : Register3) (target : Nat)
deriving DecidableEq, Repr

/-- A finite intermediate program. -/
abbrev Program3 := List Instruction3

/-- A complete intermediate-machine configuration. -/
structure Configuration3 where
  pc : Nat
  regs : Registers3
deriving DecidableEq, Repr

/-- Set the intermediate program counter. -/
def setPC3 (c : Configuration3) (next : Nat) : Configuration3 :=
  { c with pc := next }

/--
Deterministic partial operational semantics for the three-register machine.
Falling off the finite instruction list is halting.
-/
@[expose]
def step3 (p : Program3) (c : Configuration3) : Option Configuration3 :=
  match p[c.pc]? with
  | none => none
  | some (.inc which) =>
      some
        { pc := c.pc + 1
          regs := write3 c.regs which (read3 c.regs which + 1) }
  | some (.decJump which target) =>
      if read3 c.regs which = 0 then
        some (setPC3 c (c.pc + 1))
      else
        some
          { pc := target
            regs := write3 c.regs which (read3 c.regs which - 1) }

/-- The intermediate transition function is deterministic. -/
theorem step3_deterministic {p : Program3} {c a b : Configuration3}
    (ha : step3 p c = some a) (hb : step3 p c = some b) : a = b := by
  have h : some a = some b := ha.symm.trans hb
  exact Option.some.inj h

/--
Prime-power encoding of the three virtual counters.
The physical target's first counter stores this number at macro boundaries;
the second physical counter is intended to be zero at those boundaries.
-/
@[expose]
def primeCode (a b c : Nat) : Nat :=
  2 ^ a * (3 ^ b * 5 ^ c)

/-- The encoding is always a positive natural number. -/
theorem primeCode_pos (a b c : Nat) : 0 < primeCode a b c := by
  unfold primeCode
  exact Nat.mul_pos (Nat.pow_pos (by decide))
    (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))

/-- Incrementing virtual register 0 multiplies the code by 2. -/
theorem primeCode_inc_r0 (a b c : Nat) :
    primeCode (a + 1) b c = primeCode a b c * 2 := by
  change 2 ^ (a + 1) * (3 ^ b * 5 ^ c)
    = (2 ^ a * (3 ^ b * 5 ^ c)) * 2
  rw [Nat.pow_succ]
  ring

/-- Incrementing virtual register 1 multiplies the code by 3. -/
theorem primeCode_inc_r1 (a b c : Nat) :
    primeCode a (b + 1) c = primeCode a b c * 3 := by
  change 2 ^ a * (3 ^ (b + 1) * 5 ^ c)
    = (2 ^ a * (3 ^ b * 5 ^ c)) * 3
  rw [Nat.pow_succ]
  ring

/-- Incrementing virtual register 2 multiplies the code by 5. -/
theorem primeCode_inc_r2 (a b c : Nat) :
    primeCode a b (c + 1) = primeCode a b c * 5 := by
  change 2 ^ a * (3 ^ b * 5 ^ (c + 1))
    = (2 ^ a * (3 ^ b * 5 ^ c)) * 5
  rw [Nat.pow_succ]
  ring

/-- Decrementing a positive virtual register 0 divides its code by 2. -/
theorem primeCode_dec_r0 {a b c : Nat} (h : 0 < a) :
    primeCode a b c = primeCode (a - 1) b c * 2 := by
  have hs : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
  calc
    primeCode a b c = primeCode (a - 1 + 1) b c := by rw [hs]
    _ = primeCode (a - 1) b c * 2 := primeCode_inc_r0 (a - 1) b c

/-- Decrementing a positive virtual register 1 divides its code by 3. -/
theorem primeCode_dec_r1 {a b c : Nat} (h : 0 < b) :
    primeCode a b c = primeCode a (b - 1) c * 3 := by
  have hs : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
  calc
    primeCode a b c = primeCode a (b - 1 + 1) c := by rw [hs]
    _ = primeCode a (b - 1) c * 3 := primeCode_inc_r1 a (b - 1) c

/-- Decrementing a positive virtual register 2 divides its code by 5. -/
theorem primeCode_dec_r2 {a b c : Nat} (h : 0 < c) :
    primeCode a b c = primeCode a b (c - 1) * 5 := by
  have hs : c - 1 + 1 = c := Nat.sub_add_cancel (by omega)
  calc
    primeCode a b c = primeCode a b (c - 1 + 1) := by rw [hs]
    _ = primeCode a b (c - 1) * 5 := primeCode_inc_r2 a b (c - 1)

/-- Powers of 3 are odd. -/
theorem three_pow_mod_two (n : Nat) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Nat.pow_succ, Nat.mul_mod, ih]

/-- Powers of 5 are odd. -/
theorem five_pow_mod_two (n : Nat) : 5 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Nat.pow_succ, Nat.mul_mod, ih]

/--
When virtual register 0 is zero, the prime-power code is odd.
This is the non-divisibility direction needed by the low-level zero test.
-/
theorem primeCode_zero_r0_mod_two (b c : Nat) :
    primeCode 0 b c % 2 = 1 := by
  simp [primeCode, Nat.mul_mod, three_pow_mod_two, five_pow_mod_two]

/-- The code is divisible by 2 exactly when virtual register 0 is positive. -/
theorem two_dvd_primeCode_iff (a b c : Nat) :
    2 ∣ primeCode a b c ↔ 0 < a := by
  constructor
  · intro hd
    by_contra hpos
    have ha : a = 0 := by omega
    have hd' : 2 ∣ primeCode 0 b c := by simpa [ha] using hd
    have hz := Nat.mod_eq_zero_of_dvd hd'
    have ho := primeCode_zero_r0_mod_two b c
    omega
  · intro ha
    cases a with
    | zero => omega
    | succ n =>
        refine ⟨2 ^ n * (3 ^ b * 5 ^ c), ?_⟩
        change 2 ^ (n + 1) * (3 ^ b * 5 ^ c)
          = 2 * (2 ^ n * (3 ^ b * 5 ^ c))
        rw [Nat.pow_succ]
        ring


/-- A prime other than 2 cannot divide a power of 2. -/
theorem not_three_dvd_two_pow (n : Nat) : ¬ 3 ∣ 2 ^ n := by
  intro h
  have hp : Nat.Prime 3 := by decide
  have h' : 3 ∣ 2 := hp.dvd_of_dvd_pow h
  exact (by decide : ¬ 3 ∣ 2) h'

/-- Three cannot divide any power of 5. -/
theorem not_three_dvd_five_pow (n : Nat) : ¬ 3 ∣ 5 ^ n := by
  intro h
  have hp : Nat.Prime 3 := by decide
  have h' : 3 ∣ 5 := hp.dvd_of_dvd_pow h
  exact (by decide : ¬ 3 ∣ 5) h'

/-- Five cannot divide any power of 2. -/
theorem not_five_dvd_two_pow (n : Nat) : ¬ 5 ∣ 2 ^ n := by
  intro h
  have hp : Nat.Prime 5 := by decide
  have h' : 5 ∣ 2 := hp.dvd_of_dvd_pow h
  exact (by decide : ¬ 5 ∣ 2) h'

/-- Five cannot divide any power of 3. -/
theorem not_five_dvd_three_pow (n : Nat) : ¬ 5 ∣ 3 ^ n := by
  intro h
  have hp : Nat.Prime 5 := by decide
  have h' : 5 ∣ 3 := hp.dvd_of_dvd_pow h
  exact (by decide : ¬ 5 ∣ 3) h'

/-- The code is divisible by 3 exactly when virtual register 1 is positive. -/
theorem three_dvd_primeCode_iff (a b c : Nat) :
    3 ∣ primeCode a b c ↔ 0 < b := by
  constructor
  · intro hd
    by_contra hb
    have hb0 : b = 0 := by omega
    have hprod : 3 ∣ 2 ^ a * 5 ^ c := by
      simpa [primeCode, hb0] using hd
    have hp : Nat.Prime 3 := by decide
    rcases hp.dvd_mul.mp hprod with h2 | h5
    · exact not_three_dvd_two_pow a h2
    · exact not_three_dvd_five_pow c h5
  · intro hb
    cases b with
    | zero => omega
    | succ n =>
        refine ⟨2 ^ a * (3 ^ n * 5 ^ c), ?_⟩
        change 2 ^ a * (3 ^ (n + 1) * 5 ^ c)
          = 3 * (2 ^ a * (3 ^ n * 5 ^ c))
        rw [Nat.pow_succ]
        ring

/-- The code is divisible by 5 exactly when virtual register 2 is positive. -/
theorem five_dvd_primeCode_iff (a b c : Nat) :
    5 ∣ primeCode a b c ↔ 0 < c := by
  constructor
  · intro hd
    by_contra hc
    have hc0 : c = 0 := by omega
    have hprod : 5 ∣ 2 ^ a * 3 ^ b := by
      simpa [primeCode, hc0] using hd
    have hp : Nat.Prime 5 := by decide
    rcases hp.dvd_mul.mp hprod with h2 | h3
    · exact not_five_dvd_two_pow a h2
    · exact not_five_dvd_three_pow b h3
  · intro hc
    cases c with
    | zero => omega
    | succ n =>
        refine ⟨2 ^ a * (3 ^ b * 5 ^ n), ?_⟩
        change 2 ^ a * (3 ^ b * 5 ^ (n + 1))
          = 5 * (2 ^ a * (3 ^ b * 5 ^ n))
        rw [Nat.pow_succ]
        ring

end Compiler
end HakuiKoyori
