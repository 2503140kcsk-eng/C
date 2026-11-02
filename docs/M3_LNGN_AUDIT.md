# M3 source audit: Large Number Garden Number

**Audit date:** 2026-11-02  
**Status:** source transcription started; exact formalization and comparison NOT PROVED.

This document freezes what can currently be supported by the cited source material. It is not a claim that the HKN project has reproduced the author's theory or compared HKN with LNGN.

## 1. Canonical expression

The community entry describes

`LNGN = f^{10}(10 \uparrow^{10} 10)`

where `f^{10}` is tenfold iteration and `\uparrow^{10}` is ten-arrow Knuth notation.

Source classification:

- **Primary-source summary by the number's author:** [First Order Theory beyond Higher Order Set Theory](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/First_Order_Theory_beyond_Higher_Order_Set_Theory).
- **Community-maintained transcription:** [Large Number Garden Number](https://googology.miraheze.org/wiki/Large_Number_Garden_Number). The entry identifies itself as a stub and should not be treated as a peer-reviewed proof or a universal ranking of all number definitions.

The phrase “largest well-defined googologism” is a community classification, not a mathematical theorem that no larger finite number definition exists.

## 2. Source theory, as stated by the author

The author's summary starts with a first-order set-theory language `L`, extended by a unary function symbol `U` and the membership relation `∈`. It then describes:

1. `ZF_L`: ZF axiom instances in the extended language, with comprehension and replacement schemas ranging over `L`-formulas, including formulas containing `U`.
2. A formalized language `⌜L⌝`, with Gödel coding and a further unary function symbol `Θ`.
3. `ZFC_{⌜L⌝}` and a Henkin-constant schema: for a formula `P` with code `n`, if an object satisfying `P` exists, then `Θ(n)` is required to satisfy `P`.
4. `ZFCH_{⌜L⌝}`: the formalized ZFC theory augmented by that Henkin schema.
5. A theory `T = ZF_L ∪ {U1,U2,U3}`.

The community transcription gives the intended roles of the three additional axioms:

- `U1`: each `U(α)` satisfies `ZFCH_{⌜L⌝}`.
- `U2`: the interpretation of `U` inside `U(α)` agrees with earlier `U(β)` for `β∈α`.
- `U3`: each `U(α)` is related to an initial segment `V_β` in a way intended to preserve the membership relation on that segment.

The exact formal syntax, bound-variable conventions, coding, and all schema instances must be checked against the original-language source before these paraphrases are promoted to formal definitions. In particular, this document does not silently replace satisfaction by provability.

## 3. Definition of the function f

The source summary specifies a surjective coding

`CNF : ℕ → ε₀`

using Cantor normal forms.

For an `⌜L⌝`-formula `P`, `IsDefinition(P)` says that there is exactly one `x` satisfying `P`.

The source's predicate `Definable(m,i,P)` requires, in substance:

1. `i∈ℕ`;
2. `P` is an `⌜L⌝`-formula;
3. `U(CNF(i)) ⊨ IsDefinition(P)`;
4. `U(CNF(i)) ⊨ P[m/x]`.

The author then describes `f(n)` as the sum of those natural numbers `m` satisfying this predicate for some `i<n` and formula code `P<n`.

**Ambiguity to resolve from the original source:** the prose does not, by itself, settle whether the sum is indexed by distinct values of `m` or by qualifying triples `(m,i,P)` (which could count the same `m` more than once). The uniqueness clause bounds the number of values per fixed pair `(i,P)`, but it does not settle the multiplicity convention across different pairs. This is a formalization blocker, not a cosmetic notation choice.

Most importantly, `⊨` is a **model-satisfaction relation**: it says that a formula is true in the specified structure. It is not interchangeable with “the formula is provable in the theory”.

## 4. Compatibility with the HKN project's constraints

The current HKN machine formalization deliberately uses finite syntax, natural numbers, lists, and operational semantics, and its axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`. The LNGN source theory explicitly uses:

- set-membership semantics;
- ZF/ZFC axiom schemas;
- a hierarchy of structures `U(α)`;
- truth/satisfaction in those structures;
- an existence story involving a hierarchy of universes (the author mentions ZFC with a Grothendieck-universe axiom in the discussion).

Consequently, replacing `⊨` with syntactic derivability, or replacing `U(CNF(i))` with an arbitrary arithmetic predicate, would define a different function unless a value-preserving interpretation is proved.

A possible *research route*, not yet established, is to encode the syntax, structures, assignments, and satisfaction relation in a type-theoretic or arithmetic metatheory. To count as the same LNGN definition, this encoding must prove that it preserves the exact models and satisfaction predicates used by the source, the Henkin scheme, the U1–U3 conditions, and the finite sum defining `f`. A mere Gödel numbering of formulas is insufficient.

## 5. M3 proof obligations

The following gates are required before a comparison claim is allowed:

- [ ] Obtain and freeze the original Japanese source and its exact notation; compare it line-by-line with the English summary.
- [ ] Resolve the indexing/multiplicity convention in the sum defining `f(n)`.
- [ ] Define the complete syntax and Gödel coding of `L` and `⌜L⌝`.
- [ ] Formalize the axiom schemas, including capture-avoiding substitution in `P[m/x]`.
- [ ] Define the relevant structures and the satisfaction relation.
- [ ] State and discharge the required existence/consistency assumptions for the `U(α)` hierarchy; do not smuggle them in as unapproved axioms.
- [ ] Prove that the defining sum is finite and that `f(n)` is a uniquely specified natural number.
- [ ] Formalize tenfold iteration and the exact input `10 \uparrow^{10} 10`.
- [ ] State the intended comparison theorem with its exact HKN index and exact LNGN interpretation.
- [ ] Prove the comparison in the pinned Lean kernel and run a separate axiom audit.

## 6. What is and is not established

**Established by source inspection:** the author describes LNGN through a model-theoretic, set-theoretic satisfaction construction and gives the expression `f^{10}(10 ↑^{10} 10)`.

**Not established:** a set-theory-free reproduction of that construction; a proof that the original source is internally consistent; a Lean definition of the exact function `f`; or any inequality between an HKN value and LNGN.

A syntactic or arithmetic diagonal analogue may be a worthwhile new object, but it must receive a different name until equivalence with the author's `f` is proved.

## 7. Relevant formal-verification precedents

- Andrej Dudenhefner, [Constructive Many-One Reduction from the Halting Problem to Semi-Unification](https://doi.org/10.4230/LIPIcs.CSL.2022.18), CSL 2022; an axiom-free Coq mechanization of a constructive reduction from Turing-machine halting to two-counter-machine halting is described.
- Yannick Forster and Dominique Larchey-Wendling, [Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines](https://doi.org/10.1145/3293880.3294096), CPP 2019; provides a useful verified low-level compiler/linker architecture and emphasizes both soundness and completeness of simulation.

These papers motivate the compiler methodology for M2. They do not prove the LNGN comparison in M3.
