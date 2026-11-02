# M2: concrete low-level macro specification and proof obligations

**Status: the instruction blocks and mathematical arguments below are specified; their
Lean realizations and kernel proofs are NOT yet present. This file does not
upgrade M2 to compiler-correctness-complete.**

This document fixes concrete code blocks for the exact target ISA in
`HakuiKoyori.AssistantMachine`. It also corrects the output-conversion issue
in the earlier design: the two-counter simulation naturally leaves the
intermediate output exponent encoded as (2^v). The theorem must use the
explicit output codec (v \mapsto 2^v), or a separately proved target-side
normalizer; it must not silently identify (2^v) with (v).

## 1. Exact target ISA and notation

The physical counters are (A=\texttt{left}) and (B=\texttt{right}).
The only instructions are:

- `inc X`: set (X:=X+1), then advance to the next instruction;
- `decJump X,L`: if (X=0), advance to the next instruction; otherwise
  set (X:=X-1) and jump to label (L);
- falling off the end of the flattened program halts.

There is **no primitive unconditional jump**. Define the two-instruction
identity jump macros

```text
J_A(L):  inc A
         decJump A, L

J_B(L):  inc B
         decJump B, L
```

They preserve both counters and always jump to (L): immediately before
`decJump`, the selected counter is positive because the preceding
instruction incremented it. This remains true when its old value was zero.

In the following blocks, labels are local to the block unless explicitly
marked `SRC(q)`, which denotes the entry label of source instruction (q).
A repetition such as `inc B × p` means exactly (p) consecutive primitive
`inc B` instructions, not a new ISA instruction.

When a block is nested at local offset o, every internal jump target
Local(k) is rebased to Local(o+k); an external Source(q) target is left
unchanged. Apply this rebasing before concatenation. In particular, the
internal back-edge of every embedded TR handler must be shifted by that
handler's starting offset; otherwise it jumps into the wrong enclosing block.


## 2. Multiply-by-a-fixed-constant block

For any fixed (p\ge 1), define `MUL(p, D)` with precondition
((A,B)=(n,0)) and destination label (D):

```text
L_mul:       decJump A, L_mul_body
L_transfer:  decJump B, L_transfer_body
L_exit:      J_A(D)

L_transfer_body:
             inc A
             J_A(L_transfer)

L_mul_body:
             inc B × p
             J_B(L_mul)
```

The control-flow layout is significant: the zero branch of `L_mul`
falls through to `L_transfer`; the zero branch of `L_transfer`
falls through to `L_exit`. A positive `L_mul` branch jumps over both
transfer/exit blocks to `L_mul_body`.

**Correctness.** During the first loop, after (k) returns to `L_mul`,
[
 A=n-k,\qquad B=pk.
]
Every completed iteration decrements (A) once and increments (B)
exactly (p) times. When (A=0), the transfer loop repeatedly decrements
(B) and increments (A) once. At its exit (B=0) and
(A=pn). Thus the block implements
[
(n,0)\longmapsto(pn,0).
]

**Termination measures.** At visits to `L_mul`, the natural number (A)
strictly decreases on every back-edge. In the second loop, (B) strictly
decreases on every back-edge. The intervening paths have fixed finite length.
The jump macros use the non-fuel counter, so they do not increase the
active loop variant. In particular, neither loop can be entered infinitely
often.

For the three virtual registers, instantiate (p=2,3,5).

## 3. Quotient/remainder block with exact restoration

For fixed (p\ge2), define a transfer/restoration sub-block
`TR(m,r,D)`. It is entered with (A=0), (B=q), where (m\ge1)
and (r\ge0), and exits at (D):

```text
L_test_B:    decJump B, L_body
L_zero_B:    inc A × r
             J_A(D)

L_body:      inc A × m
             J_A(L_test_B)
```

If (B=q), this terminates with
[
(A,B)=(mq+r,0).
]
Its loop variant is (B): every return to `L_test_B` has consumed
one unit of (B). The jump helper uses (A), not the fuel counter (B).

Now define `DIVREM(p, D_div, D_zero)` by laying out, for
(j=0,1,\ldots,p-1), the following test immediately followed in memory by
its handler:

```text
L_j:         decJump A, L_(j+1)     # L_p is L_group
H_j:         TR(m_j, j, D_j)
```

where
```text
m_0 = 1,       D_0 = D_div
m_j = p,       D_j = D_zero       for 1 <= j < p
```

After the last test/handler pair, append:

```text
L_group:     inc B
             J_B(MacroStart)
```

The group-loop jump is deliberately the non-rebased macro-origin label. A
plain local offset would be shifted together with the recursive suffix and
could incorrectly jump back to the group-loop itself, causing a nonterminating
loop at A=0.

The handler `H_j` is physically the instruction sequence immediately
following `L_j`. Hence when (A=0), `decJump A,L_(j+1)` falls directly
into `H_j`; when (A>0), it decrements (A) and jumps over the handler
to the next test.

**Division invariant.** Let (N) be the value of (A) on entry. After
(k) completed group passes, at `L_0),
[
 A=N-pk,\qquad B=k.
]
During the next group, the first (j) successful tests have decremented
(A) exactly (j) times. The first failed test occurs at the unique
(j=N\bmod p); there (A=0) and (B=\lfloor N/p\rfloor).

- If (j=0), the handler is `TR(1,0,D_div)`; it moves the quotient
  back to (A), giving ((A,B)=(N/p,0)).
- If (j>0), the handler is `TR(p,j,D_zero)`; it reconstructs
  (A=p\lfloor N/p\rfloor+j=N) and gives ((A,B)=(N,0)).

Consequently the exact block behavior is:

```text
DIVREM(p, D_div, D_zero)(N,0) =
  (N/p,0) at D_div, if N % p = 0
  (N,0)   at D_zero, otherwise
```

This is precisely the required destructive quotient test with a
non-destructive zero branch. The nonzero-remainder path restores the original
value rather than merely retaining the quotient.

**Termination measures.** The outer grouping loop is measured by (A):
each return to `L_0) follows exactly (p) successful decrements, so
(A) falls by (p). Once a remainder handler is entered, its transfer loop
is measured by (B), which falls by one on every back-edge. Each handler
has a fixed finite straight-line prefix/suffix. Thus the block has no
infinite internal execution.

For the prime-power invariant (N=2^a3^b5^c>0), the existing lemmas
`two_dvd_primeCode_iff`, `three_dvd_primeCode_iff`, and
`five_dvd_primeCode_iff` show that the remainder-zero case is exactly
the positive-exponent case. Therefore:

- virtual `inc r0/r1/r2` compiles to `MUL(2/3/5, SRC(pc+1))`;
- virtual `decJump r_i q` compiles to `DIVREM(p_i, SRC(q), SRC(pc+1))`.

The zero exponent case takes (D_{zero}) and restores (N); the positive
exponent case takes (D_{div}) and changes (N) to (N/p_i).

## 4. Label relocation and whole-program compiler

Do not bake guessed global addresses into a block. Use a template target type:

```text
Target := Local(offset) | MacroStart | Source(pc)
TemplateInstruction :=
    Inc(counter)
  | DecJump(counter, Target)
Block := finite list of TemplateInstruction
```

For source program (P=[i_0,\ldots,i_{n-1}]), let (B_i) be the block
generated for (i_i), and define

[
 start(i)=\sum_{j<i}|B_j|,\qquad total=\sum_{j<n}|B_j|.
]

Relocation at source instruction (i) is:

```text
reloc(i, Local(k))  = start(i) + k
reloc(i, Source(q)) = start(min(q,n))
```

Thus every out-of-range source jump goes to (total), the unique
fall-off/halt location. Flatten the relocated (B_0,\ldots,B_{n-1})
in source order. The internal labels in `MUL`/`DIVREM` are local offsets;
only their designated exits are `Source(q)` targets.

`Local(k)` is relative to the current nested block and is shifted by its
embedding offset. `MacroStart` always denotes the entry of the enclosing
arithmetic macro and is never shifted; it is needed for the quotient-group
loop, whose back-edge must return to the first residue test rather than to
the final group-loop block. `Source(q)` is external and is resolved only
after all top-level block lengths are known.

The compiler proof must establish:

1. every local target is strictly inside its own block;
2. every source target is relocated to the start of the corresponding block
   or to (total) when the source PC is out of range;
3. flattening preserves each block's internal fall-through adjacency;
4. `start` is monotone and injective over valid source PCs;
5. `start(n)=total`, so source halting corresponds to target fall-off.

## 5. Three-register stack macros for the explicit-current TM model

The Lean source model in `HakuiKoyori/StackSemantics.lean` is authoritative:
`TMConfiguration` has fields `state`, `leftStack`, `current`, and
`rightStack`. The two stack codes contain cells **strictly to the left and
strictly to the right** of the head. The current cell is the separate
`current` field. The earlier convention in which the top of `rightStack`
is also the current cell is rejected; it does not match `turingStep`.

Let the finite tape alphabet be `Γ), with blank symbol `□). Choose
`β = |Γ| + 1` and an injective digit map
`d : Γ → {0,...,β-1}` such that `d(□)=0` and every nonblank symbol has
a nonzero digit. For every symbol `s), `d(s)<β). A stack code has its
nearest cell in the least-significant digit:

```text
enc([])       = 0
enc(s :: tail) = d(s) + β * enc(tail)
```

Thus a stack pop returns `(code mod β, code / β)`; the empty stack pops
as blank `(0,0)`. The current symbol is not read from either stack.

Use the virtual register assignment
`r0 = T` (temporary / final unary-output accumulator),
`r1 = L` (left stack),
`r2 = R` (right stack).
At ordinary simulated TM-step boundaries, `T=0). The program counter
encodes the pair `(q,a)` consisting of the finite TM state and the current
symbol. This is possible only for a finite state set and finite alphabet;
the source specification must therefore be a finite transition table, not
an arbitrary unconstrained function `Nat → Nat → Option TMAction`.
The current `TMDelta` Nat-valued API is acceptable only with explicit
bounds and a well-formedness predicate, or after adding a finite typed
wrapper. Every transition must write a symbol below `β) and a state below
the fixed state bound.

A stack macro acts on one of `L,R`, using `T` as scratch and restoring
`T=0) on exit:

- `PUSH(X,d(s))`: multiply `X` by `β) using the fixed-constant
  multiplication pattern from Section 2, transfer the scratch back, then
  increment `X` exactly `d(s)` times. This realizes
  `X := β*X_old + d(s)`.
- `POP(X)`: use the quotient-group pattern from Section 3 with divisor
  `β), but choose `TR(1,0,D_j)` for every remainder
  `j∈{0,...,β-1}`. The selected continuation `D_j) encodes the popped
  symbol `d^{-1}(j)`; remainder zero denotes blank. It returns
  `X := X_old / β` and the symbol in finite control. It is not the
  non-restoring branch of `DIVREM` from Section 3: every remainder must
  discard the consumed top digit.

The transition `(q,a) ↦ (q',b,move)` is implemented from the control
label `(q,a)`:

- **Stay:** the new current symbol is `b`; no stack changes. Jump to
  control label `(q',b)`.
- **Right:** `PUSH(L,d(b))), then `POP(R)). Its remainder selects the
  new current symbol `a'`; jump to `(q',a')).
- **Left:** `PUSH(R,d(b))), then `POP(L)). Its remainder selects the
  new current symbol `a'`; jump to `(q',a')).

This follows the Lean equations exactly: a right move pushes the written
old-current symbol onto the left stack and pops the right stack; a left move
pushes the written symbol onto the right stack and pops the left stack.
The finite-control dispatch must cover every valid pair `(q,a)), and an
undefined transition is a halting TM state.

The source TM must be finite: represent states and symbols by finite types
(or natural-number codes bounded by fixed state/alphabet sizes), and prove
that every transition preserves those bounds. Without this finiteness
condition, an arbitrary `TMDelta` can encode an infinite, non-effective
transition function and cannot be compiled to a finite instruction list.

## 6. Input/output contract and bootstrap

The source TM is deterministic, one-tape, and has a finite alphabet and
finite state set. Its Lean configuration stores the current symbol separately
from both side-stacks.

The target's initial input code contains the entire unary word in the right
stack, including the head cell. With `d₁=d(1)`,

```text
ρ(n) = d₁ * (1 + β + ... + β^(n-1)),  ρ(0)=0
```

and the initial virtual registers are `(T,L,R)=(0,0,ρ(n))). The compiler
entry block first executes `POP(R)). For `n=0`, it obtains blank and an
empty right stack; for `n>0`, it obtains symbol `1` and leaves the
remaining `n-1` symbols in `R). The returned symbol is encoded in the
finite-control program counter, yielding the Lean source configuration
`(q₀, 0, current, tail)`. Under the assignment `(r0,r1,r2)=(T,L,R)`,
the exact M1 input code is

```text
inputCode(n) = primeCode(0, 0, ρ(n)) = 5^(ρ(n)).
```

This bootstrap is mandatory: the initial M1 configuration has program
counter zero and cannot directly encode an input-dependent current symbol
in its control state.

A halting TM is required to leave the unary result `1^v` beginning at the
current head cell and followed immediately by blank. The cleanup block
knows the current symbol from its `(q,a)` control label. It first adds one
to `T` iff the current symbol is `1`; if the current symbol is blank, it
adds zero. It then scans `R) with `POP(R)), using `L` as scratch while
preserving `T), adding one to `T` for each leading `1), and stopping at
the first blank. A nonblank symbol other than `1` before that blank violates
the output precondition. Finally it clears `L` and `R), leaving
`(T,L,R)=(v,0,0)). Stage B therefore produces the exact output code
`primeCode(v,0,0)=2^v).

The verified compiler contract must make the output representation explicit:

```text
OutputCode(v) := 2^v

TMHaltsWithUnaryOutput(M,n,v)
  iff
AssistantMachine.HaltsWithOutput
  (compileTM M) (inputCode(n)) (OutputCode(v))
```

The decoder relation is `OutputRep(v,z) iff z=2^v); injectivity of powers
of two gives uniqueness of the decoded `v`. This is exact value
preservation under a stated codec, not the stronger claim that the physical
left counter itself equals `v`. A raw-counter normalizer remains a
separate theorem and is not part of this milestone.

## 7. Concrete simulation and divergence theorems

At a three-register macro boundary define

[
 R_3(s,t)\;:\!\iff\;
 t.pc=start(s.pc)\land
 t.left=primeCode(s.r0,s.r1,s.r2)\land t.right=0.
]

For each virtual instruction, prove a nonempty finite run of the flattened
target program from the block entry to the relocated successor entry,
preserving (R_3). In the `inc` case use `MUL`; in the
`decJump` case use `DIVREM` and the three divisibility equivalences.

For the TM-to-three-register pass define the analogous relation between TM
state/head/stacks and the finite-control label plus ((L,R,T)). The
nonempty finite TM-step simulation follows by concatenating POP/PUSH
macros and the finite transition dispatch.

The composition relation is existential:
[
 R_{TM,2}(s,t)\iff\exists u,\ R_{TM,3}(s,u)\land R_{3,2}(u,t).
]
Use `StepPlus` transitivity and the existing
`forwardSimulation_compose` infrastructure to obtain forward simulation.

For the reverse direction, relate every reachable target state either to
the current source macro-boundary state (internal block state; source
stutters) or to the next source state (when the block exits). Prove the
finite block invariant and the decreasing variants above. This gives
backward simulation with finite source stuttering and rules out target
halting inside a block.

**No infinite internal macro:** every cycle in a MUL/PUSH main loop strictly
decreases its data counter; every cycle in its transfer loop strictly
decreases its scratch counter. Every cycle in DIVREM/POP grouping strictly
decreases the data counter by the fixed divisor; every cycle in the
quotient-transfer/restoration handler strictly decreases scratch. The
control graph between these loop headers is acyclic and finite. Therefore
an infinite run cannot remain inside a single macro. Since each simulated
source step has a nonempty finite target segment, an infinite source run
induces an infinite target run; conversely, if the source halts, its finite
sequence of terminating macros reaches target fall-off, so the target
cannot diverge.

The final proof suite must include:

- `mulBlock_correct` and `mulBlock_terminates`;
- `divRemBlock_correct` and `divRemBlock_terminates`;
- `relocate_local_correct`, `relocate_source_correct`, and
  `compile3_step_simulation`;
- `pushBlock_correct`, `popBlock_correct`, and
  `tmStep_simulation`;
- `compileTM_halts_iff`, `compileTM_output_codec`, and
  `compileTM_diverges_iff`;
- the existing axiom audit on the final pinned Lean 4.35.0 / Mathlib 4.35.0
  PR head.

These names are theorem targets, not declarations claimed to exist today.

## 8. Tool and repository trust assignments

| Resource | Assigned role | Evidence limit |
|---|---|---|
| Lean 4.35.0 + Mathlib 4.35.0 | Definitions, compiler, kernel proofs | Only kernel-checked declarations count as proof |
| GitHub Actions | Pinned build and axiom audit | Valid only for the exact green commit |
| Sider Scholar | Find primary papers and formalization sources | Search metadata is not proof |
| Parallel Search | Independent source discovery | Free-tier rate limit currently prevents this session's MCP search; web search is the fallback |
| Context7 | Current Lean/Rocq termination and semantics documentation | API guidance, not proof |
| Wolfram | Exact finite quotient/remainder sanity checks | Cross-check only; no theorem authority |
| cvc5/cvc5 repository | Search bounded counterexamples to arithmetic invariants | Solver output is not a universal proof |
| SymPy repository | Exact small-integer regression tests | Finite tests only |
| SageMath repository | Independent bounded arithmetic / stack-code testing | Finite tests only |
| LeanDojo-v2 repository | Retrieve analogous proof states and propose Lean tactics | Every proof still needs kernel checking |
| Naproche repository | Natural-language specification audit | Specification feedback only |
| GAP repository | Finite-state control-table checks if needed | Not on the arithmetic proof path |
| Macaulay2 repository | No natural role in this discrete counter-machine construction | Intentionally not forced into the project |

The listed GitHub projects are public research resources, not autonomous agents
that have been run or coordinated in this chat. Do not report a tool as having
executed merely because its repository was inspected.

## 9. Current verification boundary

The existing M2 PR head before this document had a successful GitHub Actions
run (run ID `41395159595`), including the pinned build, configured axiom
audit, and direct checks of the four then-existing Lean files. That run
certifies only those files at that exact commit. It does **not** certify the
macro blocks in this design document.

Until the theorem targets in Section 7 are implemented and the new PR head
passes the full kernel build and axiom audit, the status remains:

```text
M2_FOUNDATIONS_CI = PASS (for commit 0a0b30eb48a0de2b58bb891870386bccf95a9d91)
LOW_LEVEL_MACROS_LEAN = NOT_IMPLEMENTED
COMPILER_CORRECTNESS = NOT_PROVED
TM_OUTPUT_CODEC_THEOREM = NOT_PROVED
DIVERGENCE_PRESERVATION = NOT_PROVED
RELEASE = BLOCKED
```

## References

- Andrej Dudenhefner, "Certified Decision Procedures for Two-Counter Machines",
  FSCD 2022, DOI: https://doi.org/10.4230/LIPIcs.FSCD.2022.16 .
  The paper studies the exact `inc` / conditional-decrement-and-jump
  instruction shape and emphasizes that universality claims depend on the
  chosen instruction set.
- Minsky, *Computation: Finite and Infinite Machines*, 1967.
- Lecture notes, *Foundations of Computer Science*, Theorem 8.10 and
  Corollary 8.11 (three counters to two; Turing machine simulation):
  https://www.enseignement.polytechnique.fr/informatique/INF412/uploads/Main/polyinf412english-goodINF412ENGLISH.pdf .
