# Next research plan: assistant-machine Busy Beaver

**Status: proposal only. Not part of the verified HKN_0 definition.**

## Why move beyond the current arithmetic grammar?

Milestone 0 proves diagonal dominance only over a deliberately small language of total arithmetic programs. Its strength is that every program evaluation is total and easy to formalize. Its weakness is equally clear: it says nothing about programs outside that grammar.

The next candidate should model the “助手くん laboratory” as a finite catalogue of general-purpose machines. A Busy Beaver construction takes the maximum output among machines below a finite description bound that eventually halt. The description catalogue is finite, but deciding which machines halt is not generally computable. This gives a route to a rigorously defined **noncomputable yet finite natural number** without using ZF, ZFC, MK, or set-membership semantics.

## Proposed mathematical definition

First freeze one deterministic universal register-machine or Turing-machine model.

- A machine has a finite natural-number code (e).
- A total decoder maps every natural number (e) to a machine. Invalid descriptions map to a fixed trivial machine.
- The machine receives input (n).
- Its one-step transition relation is deterministic and computable.
- A halting execution has a finite trace and a unique natural-number output.

For a code bound (m) and input (n), let (C_m) be the finite list of codes (0,1,ldots,m). Define the halting-output catalogue

```text
O(m,n) = [ output(e,n) | e in C_m and machine e halts on n ]

B(m,n) = 1 + max(0 and all entries of O(m,n))
HKN_1  = B(HKN_0, HKN_0)
```

The fixed code 0 will be chosen to be a machine that halts and returns its input, so the catalogue is nonempty and (HKN_1>HKN_0).

The predicate “machine e halts on input n” is the existence of a finite execution trace. It is a proposition over natural-number-coded traces; the definition does not quantify over a universe of sets. Because (C_m) is finite, the collection of outputs that exist is finite and has a maximum. Extracting the output from a halting witness is noncomputable in general, but it still specifies one natural number.

This definition is not frozen until the machine model, decoder, output convention, and proof of determinism are fixed in Lean. In particular, the code-0 convention and universality must be proved rather than assumed.

## Formal proof obligations

1. Define a deterministic machine syntax and finite code decoder.
2. Define configurations and a total single-step transition function.
3. Define bounded execution by primitive recursion on the number of steps.
4. Prove that halting witnesses determine a unique output.
5. Define the finite list of codes below a bound without using set theory.
6. Define (B(m,n)) from the finite list and prove it is greater than every halting output in that catalogue.
7. Prove (HKN_1>HKN_0).
8. Prove the chosen machine model can simulate a conventional universal machine, if general computable-function domination is claimed.

## What this would and would not establish

A correctly formalized Busy Beaver construction can dominate all outputs of machines in its own finite code catalogue. With a suitable universal-machine coding and an asymptotic argument, its function can eventually dominate every total computable function.

It does **not** follow that (HKN_1) exceeds LNGN. The LNGN function is defined through a stronger semantic/theoretic construction involving set theory. Busy Beaver dominance over computable functions is not a comparison against every noncomputable number definition. The LNGN comparison remains a separate, explicit theorem obligation.

## Research sequence

- **M1 — machine semantics:** exact code, decoder, configurations, execution, halting, and output.
- **M2 — finite Busy Beaver bound:** define (B(m,n)) and prove its finite-catalogue diagonal theorem in Lean.
- **M3 — strength theorem:** prove the precise computable-function domination result supported by the selected machine model.
- **M4 — LNGN source formalization:** transcribe the exact FOTbHOST language, coding, axioms, satisfaction conditions, and metatheoretic assumptions from the original source. Do not assume consistency or soundness without proof.
- **M5 — comparison:** either prove a no-set-theory lower bound that yields (HKN_i > LNGN), or record a rigorous obstruction. Do not announce victory without the theorem.

## Tool roles

Lean remains the authority for definitions and proof checking. cvc5 may search for finite counterexamples; SymPy and SageMath may check small instances; GAP and Macaulay2 are optional and only enter if the chosen encoding creates algebraic subproblems; Naproche may cross-check natural-language specifications; LeanDojo may assist proof search. Sider Scholar and Parallel Search support source discovery; Context7 supports version-specific Lean documentation; Wolfram is an auxiliary independent calculator. None of these tools' outputs count as proof unless converted into kernel-checked Lean theorems.
