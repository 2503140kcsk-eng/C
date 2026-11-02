# Hakui Koyori Number（博衣こより数）

**A finite, set-theory-free googology research project with Lean 4 formal proofs.**

> **Current status: M0 AND M1 VERIFIED / TURING-MACHINE COMPILER AND LNGN COMPARISON NOT PROVED.**  
> M1 defines a deterministic two-counter machine, codes programs and finite traces by natural numbers, and proves a bounded Busy Beaver-style diagonal theorem. It has not yet been shown to dominate every total computable function in this repository, nor to exceed the Large Number Garden Number.

## Inspiration

The design is inspired by the public concept of Hakui Koyori: holoX's researcher and R&D member, her curiosity-driven experiments, and her fan community of “助手くん”. In this project, the assistants form a finite laboratory of arithmetic programs: enumerate them, run each at a prescribed input, harvest the maximum output, and define the next stage to exceed the entire previous catalogue.

This is an unofficial fan-inspired mathematical project. It is not affiliated with or endorsed by COVER Corp. or Hakui Koyori. No official artwork, music, voice, or proprietary media is included.

- Official profile: https://hololive.hololivepro.com/talents/hakui-koyori/
- Official YouTube channel: https://www.youtube.com/@hakuikoyori

## Mathematical constraints

1. The target is a **finite natural number**, not infinity or an ordinal.
2. Its definition must be exact and unambiguous.
3. The construction must not use ZF, ZFC, MK, set-theoretic universes, or a set-membership relation.
4. Claims must be checked by Lean's kernel. Numerical experiments are not proofs.
5. No comparison claim is accepted until the target's exact semantics and a comparison theorem are formalized.
6. A larger-looking notation is not evidence that one number exceeds another.

## Milestone 0: arithmetic assistant diagonal

The Lean file `HakuiKoyori.lean` defines a finite language of total unary arithmetic programs. A program is built from:
- the input, zero, and one;
- successor, doubling, squaring, and self-power;
- `repeatAtInput`, which iterates an inner program exactly n times when evaluated at input n.

Let `depth(p)` be the syntax depth of program p, and let A_n be the finite catalogue of all programs of depth at most n. Let `eval(p,n)` denote the output of program p on input n. Define

```text
D(n) = 1 + max { eval(p,n) : p is in A_n }

T(0) = 1
T(k+1) = 10 ^ T(k)
b = T(10)

firstHarvest = D(b)
HKN_0 = D(firstHarvest) = D(D(b))
```

The maximum is over a finite nonempty catalogue, and every program in the language is total. The Lean development proves that D(n) is strictly greater than the output at n of every program in A_n. This is a genuine finite diagonal construction, but its language is deliberately limited; M0 alone does not dominate all computable functions.

## Milestone 1: deterministic two-counter machine

The module `HakuiKoyori/AssistantMachine.lean` defines a deterministic machine with a finite instruction list, a program counter, and two natural-number counters:
- `inc(r)`: increment counter r and advance the program counter;
- `decJump(r,q)`: if r=0, advance without changing counters; otherwise decrement r and jump to q;
- leaving the finite instruction list halts;
- input n initializes (pc,left,right)=(0,n,0), and the left counter is the output register.

Instructions, programs, configurations, and finite execution traces have natural-number encodings and total decoders. The halting relation is existence of a coded finite trace that follows every transition and ends in a terminal configuration. Lean proves deterministic transitions, uniqueness of halting output, and a finite maximum-output bound over all program codes 0,...,m.

The M1 candidate is

```text
HKN_1 = busyBeaver(HKN_0, HKN_0)
```

where `busyBeaver(m,n)` is one more than the maximum halting output among decoded program codes 0,...,m on input n (nonhalting codes contribute zero). Lean proves HKN_1 > HKN_0 and proves that every halting output in the bounded catalogue is strictly below HKN_1.

This is a bounded Busy Beaver-style theorem, not yet a Lean proof of universal-machine simulation. Published work establishes Turing-completeness for the selected two-counter instruction family, but the compiler and value-preserving simulation are not yet mechanized in this repository. Thus no claim of domination of all total computable functions is made.

Specification: [ASSISTANT_MACHINE_SPEC.md](docs/ASSISTANT_MACHINE_SPEC.md).

## Why the LNGN comparison is open

The community entry describes LNGN as

```text
f iterated 10 times at (10 ↑^10 10)
```

where f is defined through “First Order Theory beyond Higher Order Set Theory”. The published construction explicitly uses a first-order set-theory language with the membership relation, ZF/ZFC schemas, and an embedding discussion involving ZFC and MK. That conflicts with this project's no-set-theory constraint.

A proof of `HKN_1 > LNGN` would require a machine-checkable formalization of the exact target semantics and a value-preserving comparison theorem, or an independently proved numerical upper bound on LNGN. Neither has been established. See [the LNGN audit](docs/LNGN_AUDIT.md).

The community description is not a peer-reviewed theorem establishing a universal “largest number”. Its historical “largest well-defined googologism” wording is a googology status claim, not a theorem about all finite natural numbers. There is no largest finite natural number without restricting the class of allowed descriptions: for every N, N+1>N.

## Verification

- Lean toolchain: 4.35.0.
- M0 has no Mathlib or third-party Lean dependencies.
- M1 pins Mathlib v4.35.0 for natural-number pairing and finite-list encoding.
- Successful M1 workflow: https://github.com/2503140kcsk-eng/C/actions/runs/41386200256
- Verified M1 commit: `126147c89a3f870eb3dc6856450ae75e8cadd892`.
- The workflow passed `lake build`, direct checks of both Lean files, and the configured axiom audit.
- The audit checked 381 declarations under `HakuiKoyori`; all axioms were within the allowlist `propext`, `Classical.choice`, and `Quot.sound`.

The use of `Classical.choice` is explicit and intentional for the noncomputable halting-output selector. The audit does not claim that the development uses zero classical axioms.

## Research gates

- [x] Fix a finite, set-theory-free arithmetic language and prove its diagonal theorem (M0).
- [x] Define a deterministic finite two-counter machine and total natural-number encodings (M1).
- [x] Define finite execution traces and prove unique output for halting runs.
- [x] Define a finite bounded machine catalogue and prove its Busy Beaver-style diagonal bound.
- [x] Prove HKN_1 > HKN_0 in Lean 4.35.0 and pass the configured axiom audit.
- [ ] Formalize a Turing-machine-to-two-counter compiler and value-preserving simulation.
- [ ] Derive a Lean-verified domination theorem for the intended class of total computable functions.
- [ ] Audit FOTbHOST against the original author's complete specification.
- [ ] Formalize the exact LNGN semantics or a rigorous numerical upper bound.
- [ ] Prove an explicit HKN_1/LNGN comparison before making any size claim.

See [formal status](docs/FORMAL_STATUS.md), [the next Busy Beaver research plan](docs/NEXT_RESEARCH_PLAN.md), and [tool roles](docs/TOOL_ROLES.md).
