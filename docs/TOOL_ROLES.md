# Independent tool and repository roles

The roles below separate discovery, experimentation, and proof authority. A tool output is not a theorem merely because a tool returned it.

| Tool / repository | Assigned role for M1 | What counts as evidence |
|---|---|---|
| Lean 4.35.0 | Primary definition and proof checker | A successful kernel check on the pinned CI commit; no sorry or unapproved axioms |
| mathlib4 v4.35.0 | Pairing/unpairing and Encodable finite lists | Imported theorem declarations checked by Lean; tag must match Lean 4.35.0 |
| LeanDojo-v2 | Optional proof-state retrieval and tactic proposal | Reproducible traces; every final proof still kernel-checked |
| cvc5 | Bounded arithmetic/SMT side conditions and counterexample search | A reproducible SMT query; not a proof of an unbounded theorem |
| Naproche | Natural-language specification cross-check | A machine-checked specification document; not a replacement for Lean |
| SymPy | Exact small-code and short-trace sanity tests | Reproducible exact calculation; detects bugs but proves no universal claim |
| SageMath | Independent finite enumeration and arithmetic checks | Reproducible script/output; does not establish halting claims |
| GAP | Finite groups/actions only if a later encoding introduces such objects | Reproducible finite computation; currently not on the critical path |
| Macaulay2 | Commutative-algebra computations only if a later proof introduces algebraic structures | Reproducible algebra computation; currently not relevant to M1 |
| Wolfram | Optional symbolic/numerical cross-check | Reproducible query/code and exact output; not a proof certificate |
| Sider Scholar | Primary-source literature discovery | Verifiable paper metadata and theorem statements |
| Context7 | Current Lean/Lake API documentation | Documentation matched to the pinned version |
| Parallel Search | Independent source cross-check and extraction | Primary-source URLs and relevant passages |
| GitHub | Versioned research record and CI execution | Exact commit SHA, workflow run, job logs, and proof artifacts |

## Why some repositories are intentionally not on the critical path

M1 is a small discrete operational-semantics development over Nat and finite lists. GAP and Macaulay2 are not useful merely for the sake of using every starred repository. They should be engaged only if the mathematical construction later needs finite algebraic groups or commutative-algebra computations. Forcing these tools into the proof would add dependencies without adding evidence.

## Cost, security, and trust policy

- Prefer public, free, read-only research and GitHub's free CI allowance.
- Do not rely on paid inference, paid cloud compute, subscriptions, or private APIs.
- No external solver can approve its own output.
- Numerical experiments may falsify a conjecture; they do not prove universal theorems.
- The final mathematical claim must be represented as a Lean theorem whose proof is accepted by the Lean kernel.
- The M0 axiom audit and the M1 axiom audit are separate reports; do not extrapolate one commit's result to another.
