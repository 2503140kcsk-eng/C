# Formal status

## M0 — verified baseline

**State: previously verified.** The HKN_0 arithmetic-program candidate and its diagonal theorem were checked under Lean 4.35.0.

- Verified M0 commit: fb5ab1dfd0b90469efca745195744732283f843b
- Prior successful GitHub Actions run: https://github.com/2503140kcsk-eng/C/actions/runs/41358704214
- Checks recorded for M0: Lake build, direct Lean source check, and configured axiom audit.
- M0 used no Mathlib or third-party Lean dependency.

M0 does not establish general computable-function domination or a comparison with LNGN.

## M1 — implementation submitted; verification pending

The branch m1/two-counter-machine-formalization adds:
- AssistantMachine.lean: exact two-counter instruction semantics; total instruction/program/configuration/trace decoders; canonical natural-number encodings; deterministic step; encoded finite execution traces; halting-output uniqueness; finite maximum-output catalogue; Busy Beaver diagonal theorem.
- An M1 extension in HakuiKoyori.lean: hakuiKoyoriNumber1, a definition of HKN_1, and the theorem that HKN_1 > HKN_0.
- Mathlib pinned to v4.35.0, matching the existing Lean 4.35.0 toolchain, for pairing and list encoding.
- CI configured to build both formalization files and audit the HKN root.

**Important:** The source has been pushed to the branch, but the actual Lean compile, CI run, and axiom-audit result have not been confirmed yet. Therefore M1 is not labelled verified. Any compile failure must be resolved and the exact passing CI commit recorded before the milestone is accepted.

## Exact M1 model

The machine has two natural-number counters, a finite list of instructions, and a natural-number program counter:
- inc(r): increment r and advance the program counter.
- decJump(r,q): if r=0, advance unchanged; otherwise decrement r and jump to q.
- An out-of-range program counter is a halting configuration.
- Input n initializes (pc,left,right)=(0,n,0); output is the left counter.

The exact semantics, encoding, trace relation, and theorem statements are documented in [ASSISTANT_MACHINE_SPEC.md](ASSISTANT_MACHINE_SPEC.md).

## Claims deliberately not made

Until further formalization, the project does not claim:
- a Lean-verified simulation of Turing machines by this model;
- domination of all total computable functions;
- a separately formalized proof that the Busy Beaver function is noncomputable;
- HKN_1 > LNGN or any other LNGN comparison.

The published literature supports the universality of the selected two-counter instruction set, but a paper citation does not substitute for the compiler and simulation theorem in this repository.

## Next gate

1. Obtain a green GitHub Actions run on the exact M1 branch commit.
2. Inspect all build and axiom-audit logs; ensure no sorry and no unapproved axioms.
3. Record the successful commit hash and CI run.
4. Formalize and kernel-check the Turing-machine-to-two-counter simulation.
5. Handle LNGN in a separate exact-semantics comparison project.
