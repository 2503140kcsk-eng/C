# M2 compiler and semantic-simulation design

**Status on this branch: formal foundations added; compiler theorem NOT YET PROVED.**

This document freezes the intended proof architecture for a value-preserving
compiler into the existing HakuiKoyori.AssistantMachine two-counter ISA.
It is deliberately explicit about the gap between arithmetic identities and
an actual generated low-level program. The exact local instruction templates,
termination variants, label relocation, stack macros, and corrected output
codec are specified in [M2_LOW_LEVEL_MACROS.md](M2_LOW_LEVEL_MACROS.md).

## 1. Correctness contract

The target theorem is stronger than "the target halts whenever the source
halts". For a deterministic source machine S, input n, compiler compile,
and target machine T = compile(S), the intended contract is:

- **Termination preservation:** S halts on n iff T halts on the encoded input.
- **Value preservation:** if S halts on n with result v, then T halts with
  the explicit output code `OutputCode(v)` in the designated left counter;
  the codec/decoder relation must recover the unique source value v.
- **Trace preservation:** if source transitions emit observable labels,
  the target emits the same label sequence; internal compiler steps emit
  the empty label.
- **Divergence preservation:** an infinite source run corresponds to an
  infinite target run, and the target cannot diverge forever inside one
  simulated source step.

The observable behavior in this project is currently the pair
(termination status, natural-number output). A future I/O extension must
replace this with an explicit event trace and a stated observation policy.

A forward simulation alone is insufficient to claim equality of all
behaviors unless the target is deterministic and the simulation's
progress/initial/final-state obligations are strong enough. The intended
proof is a stuttering bisimulation: one source step is matched by a nonempty
finite target run, internal target steps are silent, and a well-founded
measure prevents an infinite target-only stutter.

## 2. Three-stage construction

Use a finite-alphabet, deterministic, one-tape Turing machine only as the
surface source language. Keep the source semantics first-order and finite.

### Stage A: finite tape machine to three-register machine

The Lean source model in `StackSemantics.lean` is authoritative:
`TMConfiguration` consists of a finite control state, a separate current
symbol, a left stack containing cells strictly left of the head, and a right
stack containing cells strictly right of the head. Neither stack contains
the current cell.

Fix a finite state set `Q` and finite alphabet `Γ) containing blank
`□). Choose `β=|Γ|+1` and an injective digit map
`d:Γ→{0,...,β-1}` with `d(□)=0) and nonblank symbols assigned nonzero
digits. A stack's nearest cell is the least-significant base-`β` digit:
`enc([])=0`, `enc(s::xs)=d(s)+β*enc(xs)). Thus
`stackPop β z=(z mod β,z/β)`; its remainder is the symbol and its quotient
is the remaining stack. Every transition writes a digit below `β).

The three virtual registers are `r0=T` (scratch and final unary-output
accumulator), `r1=L` (left stack), and `r2=R` (right stack). At ordinary
TM-step boundaries `T=0`. The finite program counter encodes the pair
`(q,a)∈Q×Γ`; this pair contains the explicit current symbol in
`TMConfiguration`. Consequently the compiler input must be a finite
transition table. The current unbounded function alias `TMDelta := Nat →
Nat → Option TMAction` is only a semantic convenience; it is not itself a
finite/effective machine description. A formal compiler must consume a
finite typed table (or bounded codes plus a proof that every next state and
written symbol remains in range).

For each transition `(q,a)→(q',b,move)`, dispatch from label `(q,a)):

- Stay: set the current symbol to `b` by jumping to label `(q',b));
  leave both stacks unchanged.
- Right: PUSH `d(b)` onto `L), POP `R), and jump to
  `(q',a')), where `a'` is the popped symbol.
- Left: PUSH `d(b)` onto `R), POP `L), and jump to
  `(q',a')), where `a'` is the popped symbol.

For all POP calls, the stack macro returns the quotient in the selected
register and places the remainder in finite control; the scratch register
returns to zero. PUSH realizes `X:=β*X+d(b)`. These operations match
the explicit-current cases in `turingStep_right`, `turingStep_left), and
`turingStep_stay). The source configuration relation must state that the
finite-control label is exactly `(state,current)), while the two register
values are exactly the side-stack codes.

The initial M1 input is not yet a TM boundary state: the compiler's entry
block is a bootstrap. It receives the complete unary word `1^n` in `R`,
including the head cell, with `T=L=0). It executes POP(R), then routes
the returned symbol to `(q0,a)). For `n=0), this returns blank and an
empty right stack; for `n>0), it returns `1` and leaves the remaining
`n-1` symbols in R. Hence
`ρ(n)=d(1)*(1+β+...+β^(n-1))` and, with the fixed register assignment,
`inputCode(n)=primeCode(0,0,ρ(n))=5^(ρ(n))`.

Required Stage-A lemmas:
1. `encodeStack` / `stackPop` satisfy the exact quotient/remainder equations.
2. Every PUSH macro terminates and transforms `X) to `β*X_old+d).
3. Every POP macro terminates, returns `X_old/β), and routes
   `X_old mod β) to the corresponding finite-control label.
4. The control-pair/stack-code relation is invariant under every operation.
5. Every finite TM step has a matching nonempty finite three-register run.
6. A halting TM configuration is converted to the specified unary-output
   convention and then to `(T,L,R)=(v,0,0)).

### Stage B: three-register machine to two-counter machine

Encode virtual register contents (a,b,c) by

N = 2^a * 3^b * 5^c.

At macro boundaries, the physical target configuration satisfies:
- left = N;
- right = 0;
- target PC equals the start label for the corresponding source PC.

An increment of virtual register i multiplies N by its associated prime
p_i in {2,3,5}.

A conditional decrement of virtual register i is a divisibility test:
- if p_i divides N, the exponent is positive and the virtual register is
  decremented by dividing N by p_i;
- otherwise the exponent is zero and N must be restored unchanged.

The physical second counter is the quotient/remainder scratch register.
The long division routine consumes N, stores the quotient in right, and
keeps the remainder in one of finitely many program-counter states. The
remainder range is finite because the divisors are the constants 2, 3, and 5.
If the remainder is zero, transfer the quotient back to left. If it is
nonzero, reconstruct N = divisor*quotient + remainder and restore the
encoded state. Every internal loop is driven by a strictly decreasing
natural-number counter, giving a concrete termination measure.

CompilerCore.lean formalizes the intermediate instruction semantics,
primeCode, the three increment identities, the positive-exponent decrement
identities, and all three exact divisibility tests: 2 divides the code iff
r0 is positive, 3 divides it iff r1 is positive, and 5 divides it iff r2 is
positive. The explicit low-level code blocks, their offset relocation, and
their termination proofs remain required.

Required Stage-B lemmas:
1. `two_dvd_primeCode_iff` (implemented): 2 ∣ N ↔ 0 < a.
2. `three_dvd_primeCode_iff` (implemented): 3 ∣ N ↔ 0 < b.
3. `five_dvd_primeCode_iff` (implemented): 5 ∣ N ↔ 0 < c.
4. Low-level multiply-by-constant blocks terminate and implement
   N := p*N with scratch restored to zero.
5. Low-level division blocks terminate and implement exact quotient/remainder.
6. The compiler's label allocator relocates every local jump to the correct
   global instruction index.
7. Each source instruction is simulated by a finite target run.
8. The source/target relation is invariant at every macro boundary.

### Provenance and originality boundary

The prime-exponent idea is **not claimed as a new invention**. Encoding
several virtual counters in one natural number by distinct prime exponents,
then implementing increment/decrement through multiplication/divisibility,
is a classical Minsky-style construction. Standard accounts describe
two-stack → multiple-counter → two-counter simulation and use prime
factorization; the literature also warns that the exact instruction set
matters. See Minsky, *Computation: Finite and Infinite Machines* (1967);
Dudenhefner, *Certified Decision Procedures for Two-Counter Machines*
(FSCD 2022); and Dudenhefner, *Constructive Many-one Reduction from the
Halting Problem to Semi-unification* (2022).

The project-specific synthesis here is the explicit composition:
finite-alphabet tape stacks → a 3-register intermediate semantics →
the repository's exact `inc/decJump` two-counter ISA, with a stated encoded
unary input, unary output decoder, nonempty finite stuttering simulation,
and a layered progress argument. This is a concrete formalization plan,
not a claim of priority or publication-level novelty. The actual low-level
blocks and their universal simulation theorem must still be proved in Lean.

### Stage C: output restoration and the composite theorem

A final output convention must be fixed before claiming a value-preserving
TM compiler. This branch uses unary output on the source tape and the explicit
target output code `OutputCode(v) = 2^v`. A raw-counter normalizer from
`2^v` to `v` is a separate optional theorem and is not claimed. The target
must finish with its right scratch counter zero.

Then prove, in order:
- compile3_step_simulation: every three-register step is matched by a
  nonempty finite two-counter run;
- compile3_halts_iff: halting is preserved in both directions;
- compile3_output_codec: the designated natural-number result is represented by the explicit target codec;
- compileTM_step_simulation: the composed TM-to-three-register-to-two-
  counter compiler simulates each TM step;
- compileTM_halts_iff and compileTM_output_codec;
- divergence preservation from the progress measure and determinism.

Only after the final two theorems pass the pinned Lean kernel and the
configured axiom audit may this repository claim that this target machine
simulates the selected TM model with output preserved.

## 3. Input/output encoding contract

To avoid silently assuming identity encodings, the surface source is fixed as a
deterministic one-tape Turing machine over a finite alphabet containing blank
and a distinguished unary output symbol.

At the initial source configuration, the input tape is the unary word
`1^n` beginning at the head and blank outside those (n) cells. Let
`d₁ ∈ {1,…,B−1}` be the fixed digit assigned to symbol `1`; its right-stack
code is the explicit finite sum
`ρ(n) = d₁ * (1 + B + … + B^(n−1))`, with `ρ(0)=0`.
The left stack and scratch register are zero. Thus the target's M1 input is
the explicit computable code

`inputCode(n) = primeCode(0, ρ, 0) = 3^ρ`.

The compiler theorem is therefore stated for the encoded target input, not
incorrectly asserted for the same raw integer on both machines.

A halting source machine is required to leave its natural-number result as a
unary block `1^v` beginning at the head, followed by blank. The Stage-A
three-register cleanup macro first clears the left stack, scans the leading
unary block, increments virtual register `r0` once per unary symbol, and
then clears both stack registers. It leaves `(r0,r1,r2)=(v,0,0)` and scratch
zero. The Stage-B boundary encoding is therefore exactly
`primeCode(v,0,0)=2^v` in the M1 left counter, with the right counter zero.
The output representation is `OutputCode(v)=2^v`; its decoder relation is
`OutputRep(v,z) iff z=2^v`, which uniquely recovers `v`.

**Important correction:** the earlier proposal to repeatedly divide by 2
while simultaneously accumulating the number of divisions in the second
physical counter is not a proved two-counter macro: that counter is also
needed as the quotient/remainder work register. No raw-output conversion
`2^v -> v` is claimed. A raw-counter normalizer would be a separate program
and theorem. See [M2_LOW_LEVEL_MACROS.md](M2_LOW_LEVEL_MACROS.md), Section 6.

The intended final theorem has the shape

`TMHaltsWithUnaryOutput M n v ↔ AssistantMachine.HaltsWithOutput
  (compileTM M) (inputCode n) (2^v)`.

This fixes the source model, input encoding, output convention, and observable
value before claiming semantic preservation.


### Exact scope of the input parameter

The composite theorem above is a many-one simulation with an explicit,
computable input translation:
`n ↦ inputCode(n)`. This is sufficient for a halting-preserving
compiler/reduction theorem because the compiler and the translated input are
both effectively constructed from the finite TM and the natural input.

It does **not**, by itself, prove the un-reparameterized pointwise claim
`busyBeaver(bound,n) > f(n)` for the M1 function whose initial left counter
is exactly `n). In general, `inputCode(n) ≠ n`, and a theorem about
`busyBeaver(bound,inputCode(n))` cannot be silently rewritten as one about
`busyBeaver(bound,n)`.

There are two precise theorem choices:

1. Define and prove a named encoded-input diagonal function
   `busyBeaverEncoded(bound,n) := busyBeaver(bound,inputCode(n))`.
   This gives the pointwise domination theorem relative to the explicit
   encoding and is the direct corollary of the composite compiler theorem.
2. If the intended statement must use the existing M1 function at the raw
   argument `n`, add and prove a two-counter input-loader prelude
   `loadUnaryInput` such that, from the M1 initial configuration
   `(pc,left,right)=(0,n,0)`, it reaches the exact prime-power encoding of
   the initial TM tape. The loader must have a total termination proof for
   every `n), preserve the designated source input, and be included in the
   program-size bound and final simulation theorem.

Until option 2 is proved, this project may claim the encoded-input simulation
and the encoded-input domination corollary only. It must not claim the raw
argument domination theorem. This is a separate interface obligation, not a
failure of the finite-TM-to-target simulation itself.


## 4. Simulation relation and theorem shape

Let R relate a source configuration s and target configuration t.
At macro boundaries:

R(s,t) := t.left = primeCode(s.r0,s.r1,s.r2) ∧ t.right = 0
           ∧ t.pc = blockStart(s.pc) ∧ controlInvariant(s,t).

For one source step, prove:

R(s,t) ∧ step3(P,s)=some s'
implies
there exists t', targetRun(P',t,t') ∧ R(s',t').

targetRun is the reflexive/transitive closure of the existing one-step
relation. For actual source steps, require a nonempty closure, or carry a
strict progress witness so that no simulated step vanishes.

For reverse correctness, establish that every reachable target state either:
- is a macro-boundary state related to exactly one source state; or
- is an internal state of one compiler block with a decreasing loop measure.

This rules out target-only infinite runs and target halts inside an unfinished
macro. Determinism of the existing target transition function is already
proved in M1; determinism of step3 is proved in CompilerCore.lean.

## 5. Composition theorem

If C1 simulates S with relation R1, and C2 simulates C1 with relation R2,
define the composite relation

R(s,t) := there exists m, R1(s,m) ∧ R2(m,t).

This composition layer is now formalized generically in
`HakuiKoyori/Simulation.lean`: `StepStar` and `StepPlus` model finite runs,
`ForwardSimulation` requires at least one target step for every source step,
`forwardSimulation_preservesPlus` extends that property to finite source
runs, and `forwardSimulation_compose` composes two compiler passes using an
existential intermediate state. This theorem is proof infrastructure only;
it does not prove that the concrete TM/three-register/two-counter passes
satisfy its premises. The concrete proof still uses target segments that
concatenate by transitivity of finite execution closure. The progress measure is layered: Stage-A stack macro fuel and Stage-B
prime arithmetic loop fuel. A lexicographic measure (first the current
source-step phase, then the decreasing loop counter) prevents infinite
silent stuttering.

## 6. Tool and repository assignments (free/local/OSS only)

The roles below separate research discovery, computation, and proof authority.

| Resource | Assigned responsibility | What it may establish |
|---|---|---|
| Lean 4.35.0 + Mathlib v4.35.0 | Definitions, compiler output, simulation relations, theorem proofs | Kernel-checked proof terms |
| GitHub Actions | Rebuild the pinned project and run the axiom audit | Reproducible CI evidence for an exact commit |
| Sider Scholar | Locate and compare primary machine-model/compiler papers | Sources and theorem statements, not proof |
| Parallel Search | Independently check original papers and official documentation | Traceable external evidence |
| Context7 | Current Lean/Rocq/Mathlib API reference | API syntax and library lemma discovery |
| Wolfram | Independent arithmetic exploration for quotient/remainder and prime-code identities | Conjecture and exact calculation only |
| cvc5 | Search for finite counterexamples to proposed arithmetic invariants and check bounded side conditions | Counterexamples/SMT evidence only |
| SymPy | Exact small-value arithmetic tests for stack and prime-code macros | Regression evidence, not universal proof |
| SageMath | Independent finite tests of prime-factor encoding and bounded macro execution | Regression evidence, not halting proof |
| LeanDojo-v2 | Retrieve similar Lean proof states and suggest tactic structures | Tactic proposals, kernel re-check required |
| Naproche | Cross-check the prose specification against its formal mathematical structure | Specification feedback, not target-machine correctness |
| GAP | Check finite control-state permutations/finite-state transition tables if the compiler generator uses them | Finite computations only; not on the arithmetic critical path |
| Macaulay2 | No justified role in this discrete arithmetic proof at present | Intentionally not forced into the proof |

The starred repositories are not executables exposed through this chat. Their public source, issues, and documentation may be inspected; numerical tools are not silently run. The role assignment is a research workflow, not a claim that these projects are coordinated autonomous agents.

## 7. Trust and acceptance policy

- No sorry, admit, unchecked axiom, or opaque external result may discharge a theorem.
- Classical.choice may appear only where the existing project's explicit
  axiom policy permits it; compiler correctness itself should be constructive.
- Search engines, Wolfram, SMT solvers, symbolic systems, and generated proof
  scripts are untrusted helpers.
- Every theorem must compile with Lean 4.35.0 and Mathlib v4.35.0.
- Run the direct Lean file checks and the project's axiom audit on the final
  PR head.
- Do not claim full semantic preservation from the prime-code identities
  alone.

## 8. Current honest status

Proved in this branch's source: three-register machine syntax,
configuration, deterministic one-step semantics, positive prime code,
increment/decrement arithmetic identities, and the three divisibility
characterizations `two_dvd_primeCode_iff`, `three_dvd_primeCode_iff`, and
`five_dvd_primeCode_iff`.

Not yet proved: the full TM-to-three-register compiler; code generation into
the existing two-counter instruction list; correctness and termination of
generated low-level multiplication/division blocks; label relocation;
macro-step simulation; halting/output equivalence; divergence preservation.

The branch is an M2 foundation milestone, not a completed universal
compiler. The next implementation task is to encode and prove the
fixed-constant division and multiplication blocks as actual lists of the
M1 instruction datatype, with explicit decreasing loop measures.
