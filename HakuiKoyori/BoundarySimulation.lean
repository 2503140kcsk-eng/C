module

public import HakuiKoyori.MacroSemantics

@[expose] public section

/-!
# Macro-boundary simulation for the three-register machine

At a source-instruction boundary, the three virtual registers are encoded as
2^r0 * 3^r1 * 5^r2 in the target's left counter; the right counter is zero.
MUL and DIVREM are interpreted by the arithmetic macro semantics in
MacroSemantics.lean.  This file proves that those macro operations implement
the source increment and conditional-decrement arithmetic exactly.

This is intentionally a macro-boundary theorem.  The refinement of the
literal primitive instruction lists in LowLevelMacros.lean to these
arithmetic macros remains a separate proof obligation.
-/

namespace HakuiKoyori
namespace Compiler

open AssistantMachine

/-- The prime-power code of one source register tuple. -/
def regsCode (regs : Registers3) : Nat :=
  primeCode regs.r0 regs.r1 regs.r2

/-- The prime assigned to each virtual register. -/
@[simp] theorem registerPrime_pos (which : Register3) :
    0 < registerPrime which := by
  cases which <;> simp [registerPrime]

/-- Incrementing one source register multiplies the prime code by its prime. -/
theorem primeCode_write3_inc (regs : Registers3) (which : Register3) :
    regsCode (write3 regs which (read3 regs which + 1)) =
      regsCode regs * registerPrime which := by
  cases which with
  | r0 =>
      simpa [regsCode, read3, write3, registerPrime] using
        primeCode_inc_r0 regs.r0 regs.r1 regs.r2
  | r1 =>
      simpa [regsCode, read3, write3, registerPrime] using
        primeCode_inc_r1 regs.r0 regs.r1 regs.r2
  | r2 =>
      simpa [regsCode, read3, write3, registerPrime] using
        primeCode_inc_r2 regs.r0 regs.r1 regs.r2

/--
Decrementing a positive source register divides the prime code by the
corresponding prime.  The multiplier-divisor cancellation is discharged
using the natural-number division identity.
-/
theorem primeCode_write3_dec_div (regs : Registers3) (which : Register3)
    (hpositive : 0 < read3 regs which) :
    regsCode (write3 regs which (read3 regs which - 1)) =
      regsCode regs / registerPrime which := by
  cases which with
  | r0 =>
      have hdec := primeCode_dec_r0 (a := regs.r0) (b := regs.r1)
        (c := regs.r2) (by simpa [read3] using hpositive)
      change primeCode (regs.r0 - 1) regs.r1 regs.r2 =
        primeCode regs.r0 regs.r1 regs.r2 / 2
      rw [hdec, Nat.mul_div_right _ (by decide : 0 < 2)]
  | r1 =>
      have hdec := primeCode_dec_r1 (a := regs.r0) (b := regs.r1)
        (c := regs.r2) (by simpa [read3] using hpositive)
      change primeCode regs.r0 (regs.r1 - 1) regs.r2 =
        primeCode regs.r0 regs.r1 regs.r2 / 3
      rw [hdec, Nat.mul_div_right _ (by decide : 0 < 2)]
  | r2 =>
      have hdec := primeCode_dec_r2 (a := regs.r0) (b := regs.r1)
        (c := regs.r2) (by simpa [read3] using hpositive)
      change primeCode regs.r0 regs.r1 (regs.r2 - 1) =
        primeCode regs.r0 regs.r1 regs.r2 / 5
      rw [hdec, Nat.mul_div_right _ (by decide : 0 < 2)]

/--
The DIVREM block's divisibility branch is exactly the source register's
zero-test: the corresponding prime divides the prime code iff the register
is nonzero.
-/
theorem registerPrime_dvd_regsCode_iff (regs : Registers3) (which : Register3) :
    registerPrime which ∣ regsCode regs ↔ 0 < read3 regs which := by
  cases which with
  | r0 =>
      simpa [registerPrime, regsCode, read3] using
        two_dvd_primeCode_iff regs.r0 regs.r1 regs.r2
  | r1 =>
      simpa [registerPrime, regsCode, read3] using
        three_dvd_primeCode_iff regs.r0 regs.r1 regs.r2
  | r2 =>
      simpa [registerPrime, regsCode, read3] using
        five_dvd_primeCode_iff regs.r0 regs.r1 regs.r2

/--
The arithmetic macro implementing a source increment returns precisely the
prime-power code of the updated source register tuple and restores the
scratch counter to zero.
-/
theorem MUL_compiles_inc (regs : Registers3) (which : Register3) :
    MUL (registerPrime which) (regsCode regs) =
      (regsCode (write3 regs which (read3 regs which + 1)), 0) := by
  rw [MUL_correct, primeCode_write3_inc]
  simp [Nat.mul_comm]

/--
The arithmetic macro implementing a source conditional decrement has the
same branch and code result as the virtual instruction: zero is preserved,
and a positive register is decremented and encoded by exact division.
-/
theorem DIVREM_compiles_decJump (regs : Registers3) (which : Register3) :
    DIVREM (registerPrime which) (regsCode regs) =
      if read3 regs which = 0 then
        (regsCode regs, 0)
      else
        (regsCode (write3 regs which (read3 regs which - 1)), 0) := by
  have hp : 0 < registerPrime which := registerPrime_pos which
  by_cases hz : read3 regs which = 0
  · have hnotdvd : ¬ registerPrime which ∣ regsCode regs := by
      rw [registerPrime_dvd_regsCode_iff]
      omega
    have hmod : regsCode regs % registerPrime which ≠ 0 := by
      intro hzero
      apply hnotdvd
      exact Nat.dvd_iff_mod_eq_zero.mpr hzero
    rw [DIVREM_correct hp]
    simp [hz, hmod]
  · have hpositive : 0 < read3 regs which := by omega
    have hdvd : registerPrime which ∣ regsCode regs :=
      (registerPrime_dvd_regsCode_iff regs which).2 hpositive
    have hmod : regsCode regs % registerPrime which = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp hdvd
    rw [DIVREM_correct hp]
    simp [hz, hmod, primeCode_write3_dec_div regs which hpositive]

end Compiler
end HakuiKoyori
