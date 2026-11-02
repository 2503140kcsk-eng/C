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
             J_B(L_0)
```

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
Target := Local(offset) | Source(pc)
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

The compiler proof must establish:

1. every local target is strictly inside its own block;
2. every source target is relocated to the start of the corresponding block
   or to (total) when the source PC is out of range;
3. flattening preserves each block's internal fall-through adjacency;
4. `start` is monotone and injective over valid source PCs;
5. `start(n)=total`, so source halting corresponds to target fall-off.

## 5. Three-register stack macros for a Turing tape

Let the finite tape alphabet be (\Gamma), with blank (\square).
Choose (\beta=|\Gamma|+1) and an injective digit map
(d: \Gamma\to\{1,\ldots,\beta-1\}). Define the stack code, with
the top at the least-significant digit, by

[
 enc([])=0,\qquad enc(s::xs)=d(s)+\beta\,enc(xs).
]

A well-formed nonempty stack therefore has remainder (d(s)\ne0) modulo
(\beta), and its quotient is the code of its tail. The empty stack is
zero and represents an unvisited infinite blank suffix.

Use three **virtual** registers: L (left stack), R (right stack, whose top is
the current cell), and T (scratch, zero at every Turing-step boundary). A
stack macro uses a pair (X,S) of distinct registers, with X as data and S
as scratch; the remaining register is untouched. Ordinary TM steps use
S=T. Final output cleanup clears L first, then uses (X,S)=(R,L), leaving
T available as the unary-output accumulator.

- `PUSH(X,d(s))`: execute the MUL(β) pattern from Section 2 on (X,S),
  then execute `inc X` exactly d(s) times. This maps X to β*X_old+d(s)
  and restores S=0.
- `POP(X)`: lay out tests `L_j: decJump X,L_(j+1)` for
  j=0,...,β-1, with L_β the group-loop header. Immediately after each
  test put the handler `TR(1,0,D_j)` from Section 3, with all its
  internal labels rebased to that handler's offset. If the test sees zero,
  it falls through to its handler; if positive, it decrements X and jumps
  to the next test. At the group header execute `inc S; J_S(L_0)`.
  Starting from (X,S)=(N,0), after k full groups the invariant is
  X=N-βk and S=k. The first failed test is j=N mod β, at which point
  X=0 and S=floor(N/β). Its handler TR(1,0,D_j) transfers only the
  quotient back to X, then branches to continuation D_j.
  Therefore it returns (X,S)=(floor(N/β),0), with remainder j
  held in finite control. For a well-formed nonempty stack j=d(s)≠0;
  for the empty stack j=0 and the returned symbol is blank.

The POP handler transfers the quotient for **every** remainder. It is not
DIVREM from Section 3: that block restores the original data when the
remainder is nonzero, whereas POP must always replace the stack by its tail.
For a TM transition ((q,s)\mapsto(q',w,move)), first POP (R) to read
the current symbol (s); the returned remainder selects the finite
continuation:

- **Stay:** PUSH (R,w).
- **Right:** PUSH (L,w); (R) is already the old right tail.
- **Left:** POP (L) to obtain (x) (blank if empty), then PUSH (R,w)
  followed by PUSH (R,x). Since each push puts its symbol at the top,
  the new (R) is (x::w::tail(R)), as required.

These operations leave the unmodified stack unchanged and return (T=0).
The tape relation is proved by induction on the stack-code equations and the
three movement cases. The outer POP grouping loop decreases (X) by
\(\beta\) per completed pass; its quotient-transfer loop decreases (T).
PUSH has an outer loop decreasing (X), followed by a transfer loop
decreasing (T). The third register is not touched as data during the
other-stack operation.

## 6. Input/output contract and a necessary correction

The source TM is fixed to a deterministic one-tape machine over (\Gamma).
Input (n) is the unary word (1^n) at the head, with blank cells beyond it.
If (d_1=d(1)), the initial right-stack value is

[
 \rho(n)=d_1(1+\beta+\cdots+\beta^{n-1}),\qquad \rho(0)=0.
]

The left stack and scratch are zero, so the target input is

[
 inputCode(n)=primeCode(0,\rho(n),0)=3^{\rho(n)}.
]

A halting source TM is required to leave (1^v) beginning at the current
head cell, followed immediately by blank. The Stage-A cleanup first clears
the left stack, then scans (R) with POP using (L) as scratch, increments
(r0) for each leading symbol (1), and stops at the first blank (or
empty stack). It clears the remaining (R) and leaves the virtual registers
((r0,r1,r2)=(v,0,0)). It therefore establishes the exact target
representation (primeCode(v,0,0)=2^v).

**Correction to the earlier M2 plan:** the proposed target-side routine
"repeatedly divide the prime code by 2 while incrementing the other physical
counter, then transfer that counter as the raw output (v)" is not justified
by the two-counter quotient block: the second counter is simultaneously
needed as quotient scratch and as the persistent output accumulator. No
such macro is present in the current source, and it must not be claimed.

The verified compiler contract should instead make the output representation
explicit:

```text
OutputCode(v) := 2^v

TMHaltsWithUnaryOutput(M,n,v)
  iff
AssistantMachine.HaltsWithOutput
  (compileTM M) (inputCode(n)) (OutputCode(v))
```

The decoder is specified by the relation (OutputRep(v,z)\iff z=2^v);
injectivity of powers of two gives uniqueness of the decoded (v).
This is exact value preservation under a stated codec, not the stronger
claim that the physical left counter itself equals (v). If raw-counter
output is later required, it needs a separate two-counter normalization
program and a new proof; it is not part of this milestone.

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
