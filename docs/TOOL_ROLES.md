# Independent tool and repository roles

These are proposed roles for the research project. No external tool's output substitutes for Lean kernel checking.

| Tool / repository | Assigned role | What counts as evidence |
|---|---|---|
| Lean 4 | Primary definition and proof checker | A green CI run on a pinned toolchain, with no `sorry` or unapproved axioms |
| mathlib4 | Reusable formal mathematics after the core is stable | Imported theorem declarations checked by Lean |
| LeanDojo-v2 | Retrieval and proof-state assistance for later Lean development | Reproducible retrieval/prover traces; never treated as proof evidence itself |
| cvc5 | Bounded arithmetic/SMT side checks and counterexample search | SMT result plus independently checked proof where possible |
| Naproche | Natural-language-to-formal-specification consistency checks | A machine-checked Naproche document; not a replacement for Lean |
| SymPy | Exact small-input calculations and recurrence sanity checks | Reproducible exact outputs, used only to detect mistakes |
| SageMath | Independent combinatorial and arithmetic experiments | Reproducible scripts and exact output |
| GAP | Finite algebraic structures, finite group actions, and combinatorial enumeration if the theory needs them | Reproducible finite computation |
| Macaulay2 | Algebraic structures only if later algebraic encodings arise | Reproducible computation; currently not on the critical path |
| Wolfram | Independent symbolic/numerical cross-checks | Reproducible query/code and exact output; not a proof certificate |
| Sider Scholar | Literature discovery and source tracking | Primary-source references and bibliographic metadata |
| Context7 | Version-specific Lean and tool documentation | Documentation matching the pinned toolchain |
| Parallel Search | Cross-check public source material, including the LNGN origin | Source URLs and extracted text |
| GitHub | Versioned research record and CI execution | Commit SHA, workflow run, logs, artifacts |

## Cost and trust policy

- Prefer public, free, read-only research and local exact arithmetic.
- Do not depend on paid inference, paid cloud compute, subscriptions, or private APIs.
- No independent solver is allowed to “approve” its own output.
- Numerical experiments may falsify conjectures; they do not prove universal theorems.
- The final mathematical claim must be represented as a Lean theorem whose proof is accepted by the Lean kernel.
