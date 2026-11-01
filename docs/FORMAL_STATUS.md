# Formal status

## Milestone 0

**State:** candidate definition written; Lean proof included; CI execution pending.

The file `HakuiKoyori.lean` defines:

- a finite inductive syntax `AssistantCode`;
- a total evaluator over natural numbers;
- a finite list `assistants n` containing all codes up to syntax depth `n`;
- the maximum output of that catalogue at input `n`;
- the diagonal function `diagonal n = maximumAssistantOutput n + 1`;
- the finite candidate `hakuiKoyoriNumber = diagonal (diagonal (tenTower 10))`.

The central theorem is:

```lean
hakuiKoyoriNumber_dominates_catalogue
```

It states that every assistant program with syntax depth at most `firstHarvest` has output strictly below `hakuiKoyoriNumber` when evaluated at `firstHarvest`.

The theorem follows from:
1. every code occurs in the finite catalogue at its own depth;
2. the catalogue is monotone in the depth bound;
3. every member of a finite list is bounded by the list maximum;
4. the diagonal adds one to that maximum.

## What this proof does not establish

- It does not prove a bound against arbitrary Turing machines.
- It does not prove a bound against all total computable functions.
- It does not prove a bound against all formal theories.
- It does not prove that `hakuiKoyoriNumber` exceeds LNGN.
- It does not prove consistency or soundness of FOTbHOST.
- It does not use set theory to define the candidate.

## CI evidence

Only a successful GitHub Actions run for the exact commit can be called a CI pass. The workflow is configured to run `lean HakuiKoyori.lean` under the pinned Lean 4.35.0 toolchain. If the workflow fails, fix the Lean file and rerun CI before promoting the milestone.
