# M1: Assistant-machine specification

**Status: VERIFIED** on commit `126147c89a3f870eb3dc6856450ae75e8cadd892` by [GitHub Actions run 41386200256](https://github.com/2503140kcsk-eng/C/actions/runs/41386200256).
This document freezes the mathematical model. It does not claim that the universality compiler or LNGN comparison has been formalized.

## 1. Foundational boundary

The machine semantics use finite inductive syntax, natural numbers, finite lists, functions, and propositions. The formal definitions do not introduce a set-membership predicate or ZF, ZFC, or MK axioms. The project pins Mathlib v4.35.0, matching Lean 4.35.0, for the standard natural-number pairing and finite-list encoding.

The distinction is important: a library may contain general set-theoretic mathematics in unrelated modules, while the machine's actual state and transition definitions remain over Nat and List. The axiom audit checked 381 declarations under HakuiKoyori; all axioms were within the allowlist `propext`, `Classical.choice`, and `Quot.sound`.

## 2. Machine model

A machine is a finite program, a list of instructions. There are exactly two counters, each storing a natural number, and a natural-number program counter.

The counter type is:
- left
- right

The instruction grammar is:
- inc(r): increment counter r and advance the program counter by one.
- decJump(r,q): if counter r is zero, leave both counters unchanged and advance the program counter by one; otherwise decrement counter r and set the program counter to q.

The program counter is zero-based. If the program list has no instruction at the current program counter, the machine is halted. There is no implicit wraparound or instruction after the end of the list. The left counter is the output register. An input n initializes the configuration to (pc=0, left=n, right=0).

This exact instruction set matters. Two-counter instruction sets that look superficially similar need not have the same computational power. Dudenhefner's 2023 extended paper defines two-counter programs using increment instructions and conditional decrement-and-jump instructions, and explains their Turing-completeness by reducing Turing-machine halting through a four-counter simulation to two counters. The Lean development here formalizes the operational semantics and the Busy Beaver diagonal; it does not yet formalize that compiler.

## 3. Finite encodings and total decoders

Use the Mathlib natural-number pairing function Nat.pair with inverse Nat.unpair.

Counter coding:
- left maps to 0
- right maps to 1

Instruction coding:
- inc(r) maps to pair(0, pair(code(r), 0))
- decJump(r,q) maps to pair(1, pair(code(r), q))

The instruction decoder is total. It decodes tag zero as inc; every nonzero tag is interpreted as decJump. A counter subcode of zero means left; every nonzero counter subcode means right. The encoding/decoding inverse theorem proves that valid instruction encodings round-trip exactly.

A program is a finite list of instructions. Its canonical code is Encodable.encode for the list type, using Mathlib's constructive List.encodable instance. The decoder is total by mapping an invalid Option result to the empty program. Every finite program is recovered from its canonical code. Different malformed natural numbers may denote the empty program; this does not affect injectivity of canonical encodings.

A configuration (pc,left,right) is coded as pair(pc, pair(left,right)), with a total decoder and an inverse theorem.

A finite trace is a finite list of configurations. It is encoded with Encodable.encode for lists of configurations. The total trace decoder maps malformed codes to the empty trace, and every valid finite trace has a code that decodes to itself.

## 4. Transition and finite traces

step(program, configuration) is a partial deterministic function returning either:
- some nextConfiguration for the unique next state; or
- none if the program counter is outside the instruction list.

step_deterministic proves that two some successors from the same program and configuration are equal.

ExecutionTrace program start trace final is an inductive Type-valued family:
- a terminal trace consists of the single configuration c, with step program c = none;
- a nonterminal trace consists of c followed by the trace from its unique successor.

Thus a trace is a finite list including its initial and final configurations. It carries a natural-number code through encodeTrace. The halting proposition wraps this Type-valued witness in `Nonempty`, keeping halting in Prop while allowing proofs to inspect trace data.

HaltsWithOutput program input output means that there exists a natural-number trace code whose decoded trace is a valid execution from the initial configuration and terminates in a configuration whose left counter equals output. This definition expresses halting by the existence of a finite, natural-number-coded execution trace; it does not ask a program to decide nonhalting.

## 5. Determinism and output uniqueness

The proof is compositional:
1. step_deterministic proves local uniqueness of a successor.
2. trace_final_unique inducts over a finite execution trace. At the first step, both traces must choose the same successor; the induction hypothesis then identifies their endpoints.
3. halts_output_unique applies endpoint uniqueness to two encoded halting traces and projects the left counter.

Consequently, the output associated with a halting machine and input is a partial function, not a relation with competing values.

## 6. Finite Busy Beaver catalogue

For m in Nat, the finite code catalogue is codesUpTo(m) = List.range (m+1), i.e. codes 0 through m inclusive.

For a code e and input n:
- if the decoded program halts with output y, use y;
- if it does not halt, use 0.

Output uniqueness makes the first case well-defined. The value is selected noncomputably from the proposition that a halting output exists; no halting decider is assumed.

maxHaltOutput(m,n) recursively takes the maximum of the selected output at code m and the previous maximum, starting at code zero. It therefore covers exactly the finite catalogue 0,...,m. The Lean theorem halting_output_le_maxHaltOutput proves that every actual halting output in that catalogue is at most this maximum.

Define:
- busyBeaver(m,n) = maxHaltOutput(m,n) + 1
- HKN_1 = busyBeaver(HKN_0,HKN_0)

Theorem busyBeaver_exceeds_catalogue proves that every halting output from a code e ≤ m on input n is strictly below busyBeaver(m,n).

Code zero decodes to the empty program. It halts immediately and returns its input. Therefore busyBeaver_gt_input proves that n < busyBeaver(m,n) for every m,n. Substituting n = HKN_0 yields the desired strict inequality HKN_0 < HKN_1.

## 7. Explicit non-claims and next theorem

This M1 formalization does not yet prove:
- that this Lean machine simulates a conventional Turing machine;
- a compiler from arbitrary Turing-machine descriptions to these two-counter programs;
- domination of every total computable function;
- noncomputability of the Busy Beaver function as a separately stated Lean theorem;
- any comparison with the Large Number Garden Number.

The next research gate is a value-preserving compiler/simulation theorem: given a Turing machine and input, construct a two-counter program and encoded input whose finite runs correspond and whose terminal output agrees. Only after that theorem is formalized and checked may the project claim general computable-function domination. LNGN remains a separate comparison problem.
