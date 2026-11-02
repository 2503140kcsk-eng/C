/-!
# Compositional simulation infrastructure (M2)

The source and target machines use partial deterministic transition functions
of type `State → Option State`. This file defines nonempty finite runs and
proves that forward simulations compose. The relation records semantic
correspondence; internal target transitions are absorbed by finite stuttering.
-/

universe u v w

/-- Reflexive-transitive closure of a partial transition function. -/
inductive StepStar {α : Type u} (step : α → Option α) : α → α → Prop where
  | refl (a : α) : StepStar step a a
  | tail {a b c : α} :
      StepStar step a b → step b = some c → StepStar step a c

/-- Nonempty finite closure of a partial transition function. -/
inductive StepPlus {α : Type u} (step : α → Option α) : α → α → Prop where
  | one {a b : α} : step a = some b → StepPlus step a b
  | tail {a b c : α} :
      StepPlus step a b → step b = some c → StepPlus step a c

namespace StepStar

theorem trans {α : Type u} {step : α → Option α} {a b c : α}
    (hab : StepStar step a b) (hbc : StepStar step b c) :
    StepStar step a c := by
  induction hbc with
  | refl => exact hab
  | tail hbc hstep ih => exact StepStar.tail ih hstep

end StepStar

namespace StepPlus

/-- Every nonempty finite run is also a reflexive-transitive run. -/
theorem toStar {α : Type u} {step : α → Option α} {a b : α}
    (h : StepPlus step a b) : StepStar step a b := by
  induction h with
  | one hstep => exact StepStar.tail (StepStar.refl _) hstep
  | tail h hstep ih => exact StepStar.tail ih hstep

/-- Concatenate two nonempty finite runs without losing nonemptiness. -/
theorem trans {α : Type u} {step : α → Option α} {a b c : α}
    (hab : StepPlus step a b) (hbc : StepPlus step b c) :
    StepPlus step a c := by
  induction hbc generalizing a with
  | one hstep => exact StepPlus.tail hab hstep
  | tail hbc hstep ih => exact StepPlus.tail (ih hab) hstep

end StepPlus

/--
Forward simulation with progress: every source transition is matched by
at least one target transition and reaches a related target state.
-/
def ForwardSimulation {S : Type u} {T : Type v}
    (sourceStep : S → Option S) (targetStep : T → Option T)
    (rel : S → T → Prop) : Prop :=
  ∀ ⦃s s' t⦄, rel s t → sourceStep s = some s' →
    ∃ t', StepPlus targetStep t t' ∧ rel s' t'

/-- Extend a one-step forward simulation to every nonempty finite source run. -/
theorem forwardSimulation_preservesPlus
    {S : Type u} {T : Type v}
    {sourceStep : S → Option S} {targetStep : T → Option T}
    {rel : S → T → Prop}
    (sim : ForwardSimulation sourceStep targetStep rel) :
    ∀ ⦃s s' t⦄, rel s t → StepPlus sourceStep s s' →
      ∃ t', StepPlus targetStep t t' ∧ rel s' t' := by
  intro s s' t hrel hrun
  induction hrun generalizing t with
  | one hstep =>
      exact sim hrel hstep
  | tail hprefix hstep ih =>
      obtain ⟨t₁, hrun₁, hrel₁⟩ := ih hrel
      obtain ⟨t₂, hrun₂, hrel₂⟩ := sim hrel₁ hstep
      exact ⟨t₂, StepPlus.trans hrun₁ hrun₂, hrel₂⟩

/--
Composition theorem for compiler passes.

If pass A simulates into B and pass B simulates into C, then the composite
relation (there exists a B-state related to both endpoints) is itself a
forward simulation from A into C. The proof concatenates the finite target
segments; no appeal to external automation or axioms is needed.
-/
theorem forwardSimulation_compose
    {A : Type u} {B : Type v} {C : Type w}
    {stepA : A → Option A} {stepB : B → Option B} {stepC : C → Option C}
    {relAB : A → B → Prop} {relBC : B → C → Prop}
    (simAB : ForwardSimulation stepA stepB relAB)
    (simBC : ForwardSimulation stepB stepC relBC) :
    ForwardSimulation stepA stepC
      (fun a c => ∃ b, relAB a b ∧ relBC b c) := by
  intro a a' c hrel hstep
  rcases hrel with ⟨b, hab, hbc⟩
  obtain ⟨b', hrunB, hab'⟩ := simAB hab hstep
  obtain ⟨c', hrunC, hbc'⟩ :=
    forwardSimulation_preservesPlus simBC hbc hrunB
  exact ⟨c', hrunC, ⟨b', hab', hbc'⟩⟩

/-- The composite simulation relation is the relational composition. -/
def ComposeRelation {A : Type u} {B : Type v} {C : Type w}
    (relAB : A → B → Prop) (relBC : B → C → Prop) : A → C → Prop :=
  fun a c => ∃ b, relAB a b ∧ relBC b c

/-- The explicit relation alias agrees with the composition theorem's relation. -/
theorem forwardSimulation_compose_explicit
    {A : Type u} {B : Type v} {C : Type w}
    {stepA : A → Option A} {stepB : B → Option B} {stepC : C → Option C}
    {relAB : A → B → Prop} {relBC : B → C → Prop}
    (simAB : ForwardSimulation stepA stepB relAB)
    (simBC : ForwardSimulation stepB stepC relBC) :
    ForwardSimulation stepA stepC (ComposeRelation relAB relBC) := by
  exact forwardSimulation_compose simAB simBC
