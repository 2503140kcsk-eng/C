# M2 compiler and semantic-simulation design

**Status on this branch: formal foundations added; compiler theorem NOT YET PROVED.**

This document freezes the intended proof architecture for a value-preserving
compiler into the existing HakuiKoyori.AssistantMachine two-counter ISA.
It is deliberately explicit about the gap between arithmetic identities and
an actual generated low-level program.

## 1. Correctness contract

The target theorem is stronger than "the target halts whenever the source
halts". For a deterministic source machine S, input n, compiler compile,
and target machine T = compile(S), the intended contract is:

- **Termination preservation:** S halts on n iff T halts on the encoded input.
- **Value preservation:** if S halts on n with result v, then T halts with
  the same natural-number result v in the designated left output counter.
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

### Stage A: tape machine to three-register machine

Represent the tape as two finite stacks:
- L: cells strictly left of the head, nearest cell on top;
- R: current cell followed by cells to the right, current cell on top;
- absent cells are blank.

For alphabet Γ, choose B = |Γ| + 1 and injectively code each symbol by a
digit in {1,...,B-1}. A stack is the natural number whose least-significant
base-B digit is its top symbol; zero denotes the empty stack (all further
cells blank).

The three registers are L, R, and TMP. At every simulated Turing
instruction boundary, TMP = 0.

Primitive stack operations are implemented by terminating loops:
- push(X,d): consume X into TMP, adding B to TMP for each decrement of X;
  transfer TMP back into X; then add d. The result is B*X_old+d.
- pop(X): consume X one unit at a time, maintain the residue modulo B in the
  finite program counter, and increment TMP whenever the residue wraps.
  At exit, TMP = X_old / B and finite control contains X_old % B; transfer
  the quotient back to X.
- Empty-pop returns the blank symbol and leaves the stack empty.

For each TM transition (q,a) -> (q',b,move), finite control knows q and the
popped symbol a. It writes b and moves by pushing/popping the appropriate
stacks. The third register is scratch only and is zero at every macro
boundary.

Required Stage-A lemmas:
1. encodeStack / decodeTop satisfy the quotient/remainder equations.
2. Each push macro terminates and transforms X to B*X+d.
3. Each pop macro terminates and returns (X/B, X%B).
4. The three-register macro preserves the tape/configuration relation.
5. Each TM transition is matched by a nonempty finite three-register run.
6. A halting TM configuration maps to a designated three-register output
   convention, with the same natural-number value.

The Lean definition Compiler.step3 is the deterministic intermediate
operational semantics. The current CompilerCore.lean proves its
single-step determinism, but does not yet emit these stack macros.

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
identities, and the exact divisibility test for register 0 (prime 2).
The corresponding divisibility lemmas for primes 3 and 5, the explicit
low-level code blocks, their offset relocation, and their termination proofs
remain required.

Required Stage-B lemmas:
1. two_dvd_primeCode_iff (implemented): 2 ∣ N ↔ 0 < a.
2. 3 ∣ N ↔ 0 < b and 5 ∣ N ↔ 0 < c.
3. Low-level multiply-by-constant blocks terminate and implement
   N := p*N with scratch restored to zero.
4. Low-level division blocks terminate and implement exact quotient/remainder.
5. The compiler's label allocator relocates every local jump to the correct
   global instruction index.
6. Each source instruction is simulated by a finite target run.
7. The source/target relation is invariant at every macro boundary.

### Stage C: output restoration and the composite theorem

A final output convention must be fixed before claiming a value-preserving
TM compiler. The preferred convention is unary output on the source tape,
decoded by a proved final macro into the target's left counter. The target
must finish with its right scratch counter zero.

Then prove, in order:
- compile3_step_simulation: every three-register step is matched by a
  nonempty finite two-counter run;
- compile3_halts_iff: halting is preserved in both directions;
- compile3_output_eq: the designated natural-number result is unchanged;
- compileTM_step_simulation: the composed TM-to-three-register-to-two-
  counter compiler simulates each TM step;
- compileTM_halts_iff and compileTM_output_eq;
- divergence preservation from the progress measure and determinism.

Only after the final two theorems pass the pinned Lean kernel and the
configured axiom audit may this repository claim that this target machine
simulates the selected TM model with output preserved.

## 3. Simulation relation and theorem shape

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

## 4. Composition theorem

If C1 simulates S with relation R1, and C2 simulates C1 with relation R2,
define the composite relation

R(s,t) := there exists m, R1(s,m) ∧ R2(m,t).

The finite-run simulation theorem composes by concatenating the target
segments. The proof is induction on the first simulation witness, followed
by induction on the second, with transitivity of finite execution closure.
The progress measure is layered: Stage-A stack macro fuel and Stage-B
prime arithmetic loop fuel. A lexicographic measure (first the current
source-step phase, then the decreasing loop counter) prevents infinite
silent stuttering.

## 5. Tool and repository assignments (free/local/OSS only)

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

## 6. Trust and acceptance policy

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

## 7. Current honest status

Proved in this branch's source: three-register machine syntax,
configuration, deterministic one-step semantics, positive prime code,
increment/decrement arithmetic identities, and
two_dvd_primeCode_iff.

Not yet proved: full TM-to-three-register compiler; divisibility
characterizations for 3 and 5; code generation into the existing two-counter
instruction list; correctness and termination of generated low-level blocks;
macro-step simulation; halting/output equivalence; divergence preservation.

The branch is an M2 foundation milestone, not a completed universal
compiler. The next implementation task is to complete the two remaining
prime-divisibility lemmas, then encode and prove the fixed-constant division
and multiplication blocks as actual lists of the M1 instruction datatype.
