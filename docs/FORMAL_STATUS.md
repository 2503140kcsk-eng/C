# Formal status

## M0 — verified baseline

**State: previously verified.** The HKN_0 arithmetic-program candidate and its diagonal theorem were checked under Lean 4.35.0.

- Verified M0 commit: fb5ab1dfd0b90469efca745195744732283f843b
- Prior successful GitHub Actions run: https://github.com/2503140kcsk-eng/C/actions/runs/41358704214
- Checks recorded for M0: Lake build, direct Lean source check, and configured axiom audit.
- M0 used no Mathlib or third-party Lean dependency.

M0 does not establish general computable-function domination or a comparison with LNGN.

## M1 — verified two-counter machine and bounded diagonal theorem

**State: VERIFIED on 2026-11-02.**

- Verified commit: `126147c89a3f870eb3dc6856450ae75e8cadd892`
- Successful GitHub Actions run: https://github.com/2503140kcsk-eng/C/actions/runs/41386200256
- Toolchain: Lean 4.35.0; Mathlib pinned to v4.35.0.
- Build: `lake build` succeeded (711 build jobs).
- Direct checks: `lake env lean HakuiKoyori.lean` and `lake env lean HakuiKoyori/AssistantMachine.lean` both succeeded.
- Axiom audit: 381 declarations under `HakuiKoyori` audited; all axioms were within the explicit allowlist `propext`, `Classical.choice`, and `Quot.sound`.

M1 provides:
- deterministic two-counter machine with finite instruction-list descriptions;
- total natural-number encoding/decoding for instructions, programs, configurations, and finite traces;
- deterministic one-step operational semantics;
- finite execution traces, with a Type-valued trace witness wrapped in `Nonempty` in the halting proposition;
- uniqueness of halting output;
- finite program-code catalogue 0,...,m and a noncomputably selected maximum halting output;
- bounded Busy Beaver-style diagonal theorem;
- HKN_1 definition and Lean theorem HKN_1 > HKN_0.

The use of `Classical.choice` is explicitly permitted by the current audit configuration. The output selector is noncomputable; it does not provide an algorithm deciding which arbitrary machines halt.

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

The published literature supports the universality of the selected two-counter instruction set, but that paper-level theorem is not a substitute for this repository's value-preserving compiler proof.

## Next gate

1. Formalize and kernel-check a Turing-machine-to-two-counter compiler.
2. Prove step-by-step simulation, including input and output preservation.
3. Derive the precise total-computable-function domination corollary.
4. Audit the exact LNGN source semantics and determine whether a set-theory-free, value-preserving interpretation is possible.
5. Prove a separate explicit comparison theorem before making any LNGN size claim.
