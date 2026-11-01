# Hakui Koyori Number（博衣こより数）

**A finite, set-theory-free googology research project with Lean 4 formal proofs.**

> **Current status: MILESTONE 0 VERIFIED / LNGN COMPARISON NOT PROVED.**  
> The current candidate is completely specified and its diagonal theorem passes Lean CI. It has not been shown to exceed the Large Number Garden Number.

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

## Milestone-0 definition

The Lean file `HakuiKoyori.lean` defines a finite language of total unary arithmetic programs. A program is built from:

- the input, zero, and one;
- successor, doubling, squaring, and self-power;
- `repeatAtInput`, which iterates an inner program exactly (n) times when evaluated at input (n).

Let `depth(p)` be the syntax depth of program (p), and let (A_n) be the finite catalogue of all programs of depth at most (n). Let `eval(p,n)` denote the output of program (p) on input (n). Define

```text
D(n) = 1 + max { eval(p,n) : p is in A_n }

T(0) = 1
T(k+1) = 10 ^ T(k)
b = T(10)

firstHarvest = D(b)
HKN_0 = D(firstHarvest) = D(D(b))
```

The maximum is over a finite nonempty catalogue, and every program in the language is total. Thus this specifies one finite natural number. The Lean development proves that `D(n)` is strictly greater than the output at (n) of every program in (A_n). Its main theorem therefore proves that `HKN_0` exceeds every program in this language of depth at most `firstHarvest`, evaluated at `firstHarvest`.

This is a genuine finite diagonal construction, but the language is deliberately limited. It does **not** establish domination of all computable functions, all formal theories, or LNGN.

## Why the LNGN comparison is open

The community entry describes LNGN as

```text
f iterated 10 times at (10 ↑^10 10)
```

where (f) is defined through “First Order Theory beyond Higher Order Set Theory”. The published construction explicitly uses a first-order set-theory language with the membership relation, ZF/ZFC schemas, and an embedding discussion involving ZFC and MK. That conflicts with this project's no-set-theory constraint.

A proof of `HKN_0 > LNGN` would require a machine-checkable formalization of the exact target semantics and a value-preserving comparison theorem, or an independently proved numerical upper bound on LNGN. Neither has been established. See [the LNGN audit](docs/LNGN_AUDIT.md).

The community description is not a peer-reviewed theorem establishing a universal “largest number”. Its historical “largest well-defined googologism” wording is a googology status claim, not a theorem about all finite natural numbers. There is no largest finite natural number without restricting the class of allowed descriptions: for every (N), (N+1>N).

## Verification

The project pins Lean 4.35.0 and has no Mathlib or third-party Lean dependencies in milestone 0.

- Successful workflow: https://github.com/2503140kcsk-eng/C/actions/runs/41358704214
- Verified commit: `fb5ab1dfd0b90469efca745195744732283f843b`
- Checks: Lake build, direct Lean source check, and axiom-audit.

A green run certifies the declarations in that commit under the pinned toolchain. It does not certify a comparison with LNGN.

## Research gates

- [x] Fix a finite, set-theory-free arithmetic language.
- [x] Define its finite depth-bounded assistant catalogue and evaluator.
- [x] Prove diagonal dominance in Lean.
- [x] Pass Lean 4.35.0 CI and the configured axiom audit.
- [ ] Audit FOTbHOST against the original author's complete specification.
- [ ] Formalize the target semantics without silently assuming consistency or soundness.
- [ ] Prove a value-preserving interpretation/comparison theorem, or document a rigorous obstruction.
- [ ] Only after comparison review, freeze a final HKN definition and any size claim.

See [formal status](docs/FORMAL_STATUS.md), [the next Busy Beaver research plan](docs/NEXT_RESEARCH_PLAN.md), and [tool roles](docs/TOOL_ROLES.md).
