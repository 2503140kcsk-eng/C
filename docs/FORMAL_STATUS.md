# Formal status

## Milestone 0 — verified

**State: Lean CI PASS.** The candidate definition and its diagonal theorem were checked by the Lean kernel under the pinned Lean 4.35.0 toolchain.

- Verified commit: `fb5ab1dfd0b90469efca745195744732283f843b`
- GitHub Actions run: https://github.com/2503140kcsk-eng/C/actions/runs/41358704214
- Final run conclusion: `success`
- Successful job: `lean-proof`
- Successful checks: Lake build, direct `lake env lean HakuiKoyori.lean`, and the configured `axiom-audit`.
- No Mathlib or third-party Lean dependency is used by this milestone.

The axiom audit uses the Lean Action's conventional allowlist (`propext`, `Classical.choice`, and `Quot.sound`). This is not a claim that Lean has no foundational axioms; it means the project passed that configured audit. The Lean source contains no `sorry`.

## Definition in `HakuiKoyori.lean`

The file defines:

- a finite inductive syntax `AssistantCode`;
- a total evaluator over natural numbers;
- a finite list `assistants n` containing every code up to syntax depth `n`;
- the maximum output of that catalogue at input `n`;
- the diagonal function `diagonal n = maximumAssistantOutput n + 1`;
- `tenTower 0 = 1` and `tenTower (n+1) = 10 ^ tenTower n`;
- `firstHarvest = diagonal (tenTower 10)`;
- `hakuiKoyoriNumber = diagonal firstHarvest`.

Equivalently, writing (D(n)) for `diagonal n` and (T) for `tenTower`:

```text
HKN_0 = D(D(T(10)))
```

## Central theorem

The main theorem is:

```lean
hakuiKoyoriNumber_dominates_catalogue
```

It states that every assistant program with syntax depth at most `firstHarvest` has output strictly below `hakuiKoyoriNumber` when evaluated at `firstHarvest`.

The proof follows from:
1. every code occurs in the finite catalogue at its own depth;
2. the catalogue is monotone in the depth bound;
3. every member of a finite list is bounded by the list maximum;
4. the diagonal adds one to that maximum.

The corollary `hakuiKoyoriNumber_gt_identity_at_firstHarvest` applies the main theorem to the identity/input program.

## What this proof does not establish

- It does not dominate arbitrary Turing machines.
- It does not dominate all total computable functions.
- It does not dominate all formal theories.
- It does not prove `hakuiKoyoriNumber > LNGN`.
- It does not prove consistency or soundness of FOTbHOST.
- It does not use ZF, ZFC, MK, or set-membership semantics to define HKN_0.

The current object is a formalized finite candidate and a sound initial milestone, not the final answer to the LNGN comparison objective.

## Next formalization target

The next candidate direction is a finite-description **assistant-machine Busy Beaver** construction:

- define a small register-machine or Turing-machine language over natural-number codes;
- define a deterministic step relation and finite execution traces;
- define halting/output semantics;
- take the maximum output of every halting machine in a finite code-bounded catalogue, then add one.

The catalogue would be finite, while the halting test is not generally decidable. This can yield a precisely defined noncomputable finite number without invoking ZF/ZFC/MK. It would strictly exceed all halting outputs in its own bounded catalogue. It would **still not automatically exceed LNGN**: the comparison theorem remains a separate requirement.

This is a research proposal, not a theorem already present in the Lean source.
