# Next research plan: assistant-machine Busy Beaver

**Current status:** the exact M1 machine semantics and HKN_1 definitions have been committed to branch m1/two-counter-machine-formalization. The Lean workflow has not yet certified this branch. Treat M1 as implementation-pending until CI, compilation, and the axiom audit pass.

## M0 baseline

Milestone 0 defines a finite language of total unary arithmetic programs and proves its own finite diagonal theorem. The verified HKN_0 source and prior successful CI commit remain the M0 baseline. M0 alone does not dominate arbitrary Turing machines or all total computable functions.

## M1 — frozen two-counter machine

The selected model is the deterministic two-counter machine with the exact instruction syntax:
- inc(r): increment counter r and advance the instruction pointer;
- decJump(r,q): if r=0, advance unchanged; otherwise decrement r and jump to q;
- falling outside the finite instruction list halts;
- the left counter is the output, and input n initializes (pc,left,right)=(0,n,0).

This is not an informal choice of any model called “two-counter machine”. The instruction set is pinned to the Turing-complete variant described by Dudenhefner. The formal source currently encodes instructions, programs, configurations, and finite traces as natural numbers using pairing and finite-list Encodable instances.

Specification: [ASSISTANT_MACHINE_SPEC.md](ASSISTANT_MACHINE_SPEC.md)

## M1 proof obligations represented in the Lean source

1. Total decoding for instruction, program, configuration, and trace codes.
2. Exact encode/decode round trips for valid descriptions, configurations, and traces.
3. Deterministic partial one-step transition.
4. Finite inductive execution traces with a natural-number code.
5. Existence-based halting and a unique left-counter output.
6. A finite catalogue of program codes from zero through m.
7. Maximum halting output over that finite catalogue, defaulting nonhalting codes to zero.
8. Diagonal theorem: every halting output in the catalogue is strictly below the maximum plus one.
9. Code zero denotes an empty program, giving HKN_1 > HKN_0.

These obligations are authored, but must not be marked VERIFIED until the pinned GitHub Actions workflow passes for the exact head commit and the axiom audit reports no unapproved axioms.

## M2 — universality and computable-function domination

Primary source: Andrej Dudenhefner, Constructive Many-one Reduction from the Halting Problem to Semi-unification, CSL 2022, extended version in Logical Methods in Computer Science (2023). The paper defines a precise two-counter model with increment and conditional decrement/jump instructions and reduces Turing-machine halting to the two-counter halting problem via an intermediate multi-counter construction.

The next formal theorem must construct a two-counter program from a Turing-machine code and input, preserve halting, and preserve the chosen output convention. A statement in a paper is evidence for the mathematical result, not a substitute for the project’s Lean proof. Until the compiler/simulation theorem is kernel-checked, do not claim domination of all total computable functions.

## M3 — LNGN audit and comparison

LNGN remains un-compared. Its published description uses a theory-language construction with set-theoretic vocabulary and substantial metatheoretic conditions. The no-set-theory constraint means the project needs an explicit value-preserving interpretation or a proven numeric bound. Neither notation size nor Busy Beaver domination over computable functions proves HKN_i > LNGN.

## Research sequence

- [ ] Compile M1 under Lean 4.35.0 and Mathlib v4.35.0.
- [ ] Resolve every kernel, linter, and axiom-audit error; record the exact successful CI commit.
- [ ] Check that all definitions satisfy the no-ZF/ZFC/MK semantic constraint.
- [ ] Formalize the two-counter compiler and step-by-step simulation theorem.
- [ ] Derive the precise total-computable-function domination corollary.
- [ ] Formalize the exact LNGN source semantics or establish a rigorous obstruction.
- [ ] Prove an explicit comparison theorem before making any LNGN size claim.

## Tool roles

- Lean 4 kernel / GitHub Actions: final authority for definitions and proofs.
- Mathlib v4.35.0: pairing/unpairing and finite-list encodings only at the machine foundation layer.
- Sider Scholar: identify primary sources and theorem statements.
- Parallel Search: cross-check the original definitions and bibliographic records.
- Context7: version-appropriate Lean/Lake documentation.
- cvc5: finite counterexample and arithmetic side-condition search; never a proof authority.
- SymPy and SageMath: exact small-instance and bounded-run sanity checks.
- LeanDojo-v2: optional retrieval/proof-state assistance; generated tactics still require kernel acceptance.
- Naproche: independent natural-language specification consistency checks.
- GAP and Macaulay2: not on the M1 critical path; use only if later algebraic/combinatorial subproblems require them.
- Wolfram: optional symbolic calculation cross-check; never a proof authority.

See [TOOL_ROLES.md](TOOL_ROLES.md) for the trust and evidence policy.
