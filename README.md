# Hakui Koyori Number（博衣こより数）

**An independent, set-theory-free googology research project with Lean 4 proofs.**

> Status: **RESEARCH / COMPARISON-BLOCKED**  
> The current milestone contains a precisely defined finite candidate and a Lean proof of its diagonal property. It does **not** yet prove that the candidate exceeds the Large Number Garden Number (LNGN).

## Why this project exists

The project takes inspiration from the public character concept of Hakui Koyori: a researcher and R&D member of Secret Society holoX, an unusually curious investigator, and someone whose fan community is called Koyori's Assistants. The mathematics turns that motif into a finite “assistant laboratory”: a finite catalogue of arithmetic programs is evaluated, its greatest output is harvested, and the next diagonal stage is set beyond every program in the previous catalogue.

This is an unofficial fan-inspired mathematical project. It is not affiliated with, endorsed by, or a representation of COVER Corp. or Hakui Koyori. It uses no official artwork, music, or other proprietary media.

Official profile: https://hololive.hololivepro.com/talents/hakui-koyori/  
Official YouTube channel: https://www.youtube.com/@hakuikoyori

## Non-negotiable mathematical constraints

1. The target is a **finite natural number**, not infinity or an ordinal.
2. The number's definition must be complete and unambiguous.
3. The number's mathematical construction must not use ZF, ZFC, MK, a set-theoretic universe hierarchy, or set-membership semantics.
4. Every proved claim must be checked by Lean's kernel; numerical experiments are not proofs.
5. A comparison with another named number is not accepted until the other number's exact semantics and the comparison theorem are formalized.
6. No result may be described as “larger than LNGN” merely because it looks more complicated or uses a higher-looking notation.

## Current candidate: assistant-laboratory diagonalization

The prototype uses a small, explicit language of total unary arithmetic programs. For an input (n), let (A_n) be the finite list of all assistant programs whose syntax depth is at most (n). Each program is evaluated at input (n). Define

[
D(n)=1+\max\{\operatorname{eval}(p,n):p\in A_n\}.
]

Let (T_0(0)=1), (T_0(k+1)=10^{T_0(k)}), and (b=T_0(10)). The milestone-0 candidate is

[
\boxed{\mathrm{HKN}_0=D(D(b)).}
]

The expression language and evaluator are given in `HakuiKoyori.lean`. The file proves that (D(n)) is strictly greater than the value at (n) of every program in (A_n). Consequently, (mathrm{HKN}_0) exceeds every program in this language whose syntax depth is at most (D(b)), when those programs are evaluated at (D(b)).

This is a genuine finite diagonal construction. It is not a claim that the prototype already dominates every total computable function, every formal theory, or LNGN.

## Why the LNGN comparison is blocked

The published description of LNGN gives it as (f^{10}(10\uparrow^{10}10)), where (f) is defined using a theory that explicitly starts from first-order set theory with the membership relation (\in), extends ZF/ZFC axiom schemas, and discusses embeddings of ZFC and MK set theory. See [Googology Wiki's LNGN entry](https://googology.miraheze.org/wiki/Large_Number_Garden_Number) and the original-author summary [First Order Theory beyond Higher Order Set Theory](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/First_Order_Theory_beyond_Higher_Order_Set_Theory).

This creates a real design conflict: the present candidate deliberately avoids set theory, while the target is defined through a set-theoretic meta-theory. A proof of (mathrm{HKN}_0>\mathrm{LNGN}) requires (at minimum) a precise, machine-checkable interpretation of the target's theory and a theorem relating that interpretation to the HKN language. No such theorem is claimed here.

The community description of LNGN is not a peer-reviewed theorem establishing a universal “largest number”; “largest” in googology is always relative to a specified class of definitions and conventions. There is no largest finite natural number in the unrestricted sense, since (N+1>N).

## Verification

The CI workflow uses the Lean 4.35.0 toolchain and checks the proof file without Mathlib or third-party dependencies:

```sh
lean --version
lean HakuiKoyori.lean
```

A green CI run certifies only the declarations in the committed Lean file. It does not certify a comparison with LNGN.

## Research gates

- [x] Fix a finite, set-theory-free arithmetic language.
- [x] Define its finite depth-bounded assistant catalog and evaluator.
- [x] Prove the diagonal dominance theorem in Lean.
- [ ] Audit the definition of FOTbHOST against the original author's full specification.
- [ ] Formalize the target semantics without silently assuming consistency or soundness.
- [ ] Prove a value-preserving interpretation/comparison theorem, or document a rigorous obstruction.
- [ ] Only after the comparison theorem passes review, freeze a final HKN definition and claim.

See [the LNGN audit](docs/LNGN_AUDIT.md), [the formal status](docs/FORMAL_STATUS.md), and [the tool-role matrix](docs/TOOL_ROLES.md).
