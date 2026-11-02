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

namespace StepPlus

/-- A nonempty finite run always begins with an actual transition. -/
theorem firstStep {α : Type u} {step : α → Option α} {a b : α}
    (h : StepPlus step a b) : ∃ c, step a = some c := by
  induction h with
  | one hstep => exact ⟨_, hstep⟩
  | tail hprefix hstep ih => exact ih

end StepPlus

/-- Extend forward simulation to reflexive-transitive source runs. -/
theorem forwardSimulation_preservesStar
    {S : Type u} {T : Type v}
    {sourceStep : S → Option S} {targetStep : T → Option T}
    {rel : S → T → Prop}
    (sim : ForwardSimulation sourceStep targetStep rel) :
    ∀ ⦃s s' t⦄, rel s t → StepStar sourceStep s s' →
      ∃ t', StepStar targetStep t t' ∧ rel s' t' := by
  intro s s' t hrel hrun
  induction hrun generalizing t with
  | refl =>
      exact ⟨t, StepStar.refl t, hrel⟩
  | tail hprefix hstep ih =>
      obtain ⟨t₁, htarget₁, hrel₁⟩ := ih hrel
      obtain ⟨t₂, htarget₂, hrel₂⟩ := sim hrel₁ hstep
      exact ⟨t₂, StepStar.trans htarget₁ (StepPlus.toStar htarget₂), hrel₂⟩


/--
Backward simulation: each target transition is matched by a possibly empty
finite source run and preserves the relation. Empty source progress accounts
for internal target steps.
-/
def BackwardSimulation {S : Type u} {T : Type v}
    (sourceStep : S → Option S) (targetStep : T → Option T)
    (rel : S → T → Prop) : Prop :=
  ∀ ⦃s t t'⦄, rel s t → targetStep t = some t' →
    ∃ s', StepStar sourceStep s s' ∧ rel s' t'

/-- Lift backward simulation from one target step to a finite target run. -/
theorem backwardSimulation_preservesStar
    {S : Type u} {T : Type v}
    {sourceStep : S → Option S} {targetStep : T → Option T}
    {rel : S → T → Prop}
    (sim : BackwardSimulation sourceStep targetStep rel) :
    ∀ ⦃s t t'⦄, rel s t → StepStar targetStep t t' →
      ∃ s', StepStar sourceStep s s' ∧ rel s' t' := by
  intro s t t' hrel hrun
  induction hrun generalizing s with
  | refl =>
      exact ⟨s, StepStar.refl s, hrel⟩
  | tail hprefix hstep ih =>
      obtain ⟨s₁, hsource₁, hrel₁⟩ := ih hrel
      obtain ⟨s₂, hsource₂, hrel₂⟩ := sim hrel₁ hstep
      exact ⟨s₂, StepStar.trans hsource₁ hsource₂, hrel₂⟩

/-- A related source terminal state must correspond to a target terminal state. -/
def TerminalReflecting {S : Type u} {T : Type v}
    (sourceStep : S → Option S) (targetStep : T → Option T)
    (rel : S → T → Prop) : Prop :=
  ∀ ⦃s t⦄, rel s t → sourceStep s = none → targetStep t = none

/--
At related macro-boundary states, forward simulation plus terminal reflection
makes halting status equivalent. Forward progress rules out a target halt
while the source still has a step.
-/
theorem forwardSimulation_terminal_iff
    {S : Type u} {T : Type v}
    {sourceStep : S → Option S} {targetStep : T → Option T}
    {rel : S → T → Prop}
    (sim : ForwardSimulation sourceStep targetStep rel)
    (terminal : TerminalReflecting sourceStep targetStep rel) :
    ∀ ⦃s t⦄, rel s t → (sourceStep s = none ↔ targetStep t = none) := by
  intro s t hrel
  constructor
  · exact terminal hrel
  · intro ht
    cases hsource : sourceStep s with
    | none => exact hsource
    | some s' =>
        obtain ⟨t', hrun, hrel'⟩ := sim hrel hsource
        obtain ⟨t₁, hfirst⟩ := StepPlus.firstStep hrun
        rw [ht] at hfirst
        cases hfirst

/-- A finite run ending in a terminal state with a specified observable value. -/
def TerminatesWithOutput {α : Type u}
    (step : α → Option α) (output : α → Nat) (start : α) (value : Nat) : Prop :=
  ∃ final, StepStar step start final ∧ step final = none ∧ output final = value

/--
The observable output agrees at related terminal states. The source terminal
premise is sufficient because TerminalReflecting supplies target termination.
-/
def TerminalOutputCompatible {S : Type u} {T : Type v}
    (sourceStep : S → Option S) (rel : S → T → Prop)
    (sourceOutput : S → Nat) (targetOutput : T → Nat) : Prop :=
  ∀ ⦃s t⦄, rel s t → sourceStep s = none →
    sourceOutput s = targetOutput t

/--
Full finite termination-and-value preservation from paired simulations.

The forward pass transports a terminating source run to the target. The
backward pass transports any terminating target run back to the source.
Terminal reflection aligns the stopping points, and output compatibility
equates their observable natural-number results.

This theorem is generic: a concrete compiler must still prove both simulation
premises, terminal reflection, and output compatibility for its own code.
-/
theorem simulations_terminatesWithOutput_iff
    {S : Type u} {T : Type v}
    {sourceStep : S → Option S} {targetStep : T → Option T}
    {rel : S → T → Prop}
    {sourceOutput : S → Nat} {targetOutput : T → Nat}
    (forward : ForwardSimulation sourceStep targetStep rel)
    (backward : BackwardSimulation sourceStep targetStep rel)
    (terminal : TerminalReflecting sourceStep targetStep rel)
    (outputCompatible :
      TerminalOutputCompatible sourceStep rel sourceOutput targetOutput) :
    ∀ ⦃s t value⦄, rel s t →
      (TerminatesWithOutput sourceStep sourceOutput s value ↔
       TerminatesWithOutput targetStep targetOutput t value) := by
  intro s t value hrel
  constructor
  · rintro ⟨sourceFinal, hsourceRun, hsourceHalt, hsourceOutput⟩
    obtain ⟨targetFinal, htargetRun, hfinalRel⟩ :=
      forwardSimulation_preservesStar forward hrel hsourceRun
    have htargetHalt := terminal hfinalRel hsourceHalt
    have houtputs := outputCompatible hfinalRel hsourceHalt
    refine ⟨targetFinal, htargetRun, htargetHalt, ?_⟩
    rw [← houtputs]
    exact hsourceOutput
  · rintro ⟨targetFinal, htargetRun, htargetHalt, htargetOutput⟩
    obtain ⟨sourceFinal, hsourceRun, hfinalRel⟩ :=
      backwardSimulation_preservesStar backward hrel htargetRun
    have hsourceHalt :
        sourceStep sourceFinal = none :=
      (forwardSimulation_terminal_iff forward terminal hfinalRel).mpr htargetHalt
    have houtputs := outputCompatible hfinalRel hsourceHalt
    refine ⟨sourceFinal, hsourceRun, hsourceHalt, ?_⟩
    rw [houtputs]
    exact htargetOutput

