/-
Erdős 592 — the reduction: ALL of the remaining uncertainty sits in class D.

Builds on `Erdos592Frontier`. Everything here is conditional on the four literature verdicts,
which are carried as EXPLICIT HYPOTHESES, never asserted:

  hA : ∀ β, ClassA β → P β      -- β < 3.  (β=0 is `P_zero`, proved; β=1 Ramsey; β=2 Specker)
  hB : ∀ β, ClassB β → ¬ P β    -- Galvin–Larson 1974
  hC : ∀ β, ClassC β → P β      -- Chang 1972 (count 1) + Schipperus 2010 (count 2)
  hE : ∀ β, ClassE β → ¬ P β    -- Schipperus 2010

⚠ CORRECTNESS WARNING FOR ANYONE FILLING IN `answer(sorry)` IN
   google-deepmind/formal-conjectures `FormalConjectures/ErdosProblems/592.lean`:
The file's own TODO says "add condition by Galvin and Larson". Galvin and Larson proved a
NECESSARY condition (β ≥ 3 with the property ⟹ β additively indecomposable) and separately
CONJECTURED that it is also sufficient — that every β ≥ 3 of the form ω^γ has the property.
THAT CONJECTURE IS FALSE: Schipperus [Sc10] exhibits failures at every γ that is a sum of four
or more indecomposables. So

    answer(fun β => β < 3 ∨ ∃ γ, β = ω ^ γ)          -- the Galvin–Larson conjecture

is a REFUTED answer and must not be committed. `hE` below is exactly the fact that refutes it;
`galvin_larson_conjecture_false` derives the refutation from it.
-/

import Erdos592Frontier

open Cardinal Ordinal Set

namespace Erdos592

universe u

/-- The Galvin–Larson conjectured answer set: `β < 3`, or `β` additively indecomposable. -/
def GalvinLarsonAnswer (β : Ordinal.{u}) : Prop := β < 3 ∨ ∃ γ : Ordinal.{u}, β = ω ^ γ

/-- Class E lies inside the Galvin–Larson conjectured answer set, so Schipperus' negative result
refutes the Galvin–Larson conjecture outright. -/
theorem galvin_larson_conjecture_false
    (hE : ∀ β : Ordinal.{u}, ClassE β → ¬ P β)
    (hEne : ∃ β : Ordinal.{u}, ClassE β) :
    ¬ (∀ β : Ordinal.{u}, GalvinLarsonAnswer β ↔ P β) := by
  obtain ⟨β, hβ⟩ := hEne
  intro hall
  obtain ⟨γ, hγ, -⟩ := hβ.2
  exact hE β hβ ((hall β).1 (Or.inr ⟨γ, hγ⟩))

/-- Unconditional form: `ω^4` is in class E, hence in the Galvin–Larson answer set, so if
Schipperus' negative verdict on class E holds then the Galvin–Larson conjecture is false. -/
theorem galvin_larson_conjecture_false' (hE : ∀ β : Ordinal.{u}, ClassE β → ¬ P β) :
    ¬ (∀ β : Ordinal.{u}, GalvinLarsonAnswer β ↔ P β) :=
  galvin_larson_conjecture_false hE ⟨_, omega_pow_four_mem_ClassE⟩

/-- **The reduction.** Given the four settled regions, membership in the Erdős 592 answer set is
completely determined outside class D, and inside class D it is exactly `P` itself. Every bit of
the remaining problem is the restriction of `P` to class D. -/
theorem erdos592_reduces_to_ClassD
    (hA : ∀ β : Ordinal.{u}, ClassA β → P β)
    (hB : ∀ β : Ordinal.{u}, ClassB β → ¬ P β)
    (hC : ∀ β : Ordinal.{u}, ClassC β → P β)
    (hE : ∀ β : Ordinal.{u}, ClassE β → ¬ P β)
    (β : Ordinal.{u}) :
    P β ↔ (ClassA β ∨ ClassC β ∨ (ClassD β ∧ P β)) := by
  constructor
  · intro hp
    rcases frontier_exhaustive β with h | h | h | h | h
    · exact Or.inl h
    · exact absurd hp (hB β h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hp⟩)
    · exact absurd hp (hE β h)
  · rintro (h | h | ⟨-, h⟩)
    · exact hA β h
    · exact hC β h
    · exact h

/-- **The answer has exactly two possible closed forms — but only if class D is uniform.**

If (and this is NOT known) `P` is constant on class D, then the answer to Erdős 592 is either
`ClassA ∪ ClassC ∪ ClassD` or `ClassA ∪ ClassC`, and nothing else. The hypothesis `huniform` is
listed explicitly because nobody has proved it: a priori different `γ` with three indecomposable
summands could behave differently, in which case Erdős 592 has NO answer of this shape at all. -/
theorem erdos592_answer_dichotomy
    (hA : ∀ β : Ordinal.{u}, ClassA β → P β)
    (hB : ∀ β : Ordinal.{u}, ClassB β → ¬ P β)
    (hC : ∀ β : Ordinal.{u}, ClassC β → P β)
    (hE : ∀ β : Ordinal.{u}, ClassE β → ¬ P β)
    (huniform : (∀ β : Ordinal.{u}, ClassD β → P β) ∨ (∀ β : Ordinal.{u}, ClassD β → ¬ P β)) :
    (∀ β : Ordinal.{u}, P β ↔ (ClassA β ∨ ClassC β ∨ ClassD β)) ∨
    (∀ β : Ordinal.{u}, P β ↔ (ClassA β ∨ ClassC β)) := by
  rcases huniform with hD | hD
  · refine Or.inl fun β => ⟨fun hp => ?_, fun h => ?_⟩
    · rcases frontier_exhaustive β with h | h | h | h | h
      · exact Or.inl h
      · exact absurd hp (hB β h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd hp (hE β h)
    · rcases h with h | h | h
      · exact hA β h
      · exact hC β h
      · exact hD β h
  · refine Or.inr fun β => ⟨fun hp => ?_, fun h => ?_⟩
    · rcases frontier_exhaustive β with h | h | h | h | h
      · exact Or.inl h
      · exact absurd hp (hB β h)
      · exact Or.inr h
      · exact absurd hp (hD β h)
      · exact absurd hp (hE β h)
    · rcases h with h | h
      · exact hA β h
      · exact hC β h

end Erdos592
