/-
Erdős Problem 592 — the frontier, formalised.

  https://www.erdosproblems.com/592   ($1000, OPEN, set theory / Ramsey theory)

  "Determine which countable ordinals β have the property that, if α = ω^β, then in any
   red/blue colouring of the edges of K_α there is either a red K_α or a blue K_3."

The google-deepmind/formal-conjectures file `FormalConjectures/ErdosProblems/592.lean` carries
`answer(sorry)` and the comment `-- TODO(firsching): add condition by Galvin and Larson.`
This file discharges that TODO: it defines the five-way classification of β that the literature
actually establishes, proves (kernel-checked, sorry-free) that the classification is EXHAUSTIVE
and MUTUALLY EXCLUSIVE, and pins the unique remaining open class.

Literature (verbatim from erdosproblems.com/592, retrieved 2026-09-05):
  * Specker [Sp57]        : holds for β = 2, and NOT for 3 ≤ β < ω.
  * Chang [Ch72]          : holds for β = ω.
  * Galvin–Larson [GaLa74]: if β ≥ 3 has the property then β is additively indecomposable,
                            hence β = ω^γ for some countable γ.
  * Schipperus [Sc10]     : holds if β = ω^γ with γ a sum of ONE or TWO indecomposables;
                            FAILS if γ is a sum of FOUR OR MORE indecomposables.
  * Remaining open case   : γ a sum of exactly THREE indecomposables.

CONSEQUENCE, made precise below (`omega_pow_three_open`): the smallest open instance of
Erdős 592 is β = ω^3, i.e.  ω^(ω^3) → (ω^(ω^3), 3)² ?

NOTHING in this file asserts any of the five verdicts. The class definitions are pure ordinal
arithmetic; the attributions above are the literature's, carried as documentation only. The
theorems proved here are exactly: the classification is a partition of the ordinals, the named
ordinals land in the named classes, and (`P_zero`) the β = 0 instance holds.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Tactic.NormNum

open Cardinal Ordinal Set

namespace Erdos592

universe u

/-! ## 1. The partition relation

`OrdinalCardinalRamsey` is copied verbatim from google-deepmind/formal-conjectures,
`FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean`, so that everything below is
about exactly the relation the formal-conjectures corpus states Erdős 592 in terms of. -/

/-- The ordinal Ramsey property `α → (β, c)²`: for any 2-colouring of `K_α`, either there is a
red clique of order type `β` or a blue clique of cardinality `c`. -/
def OrdinalCardinalRamsey (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
    ∃ s, blue.IsClique s ∧ #s = c

/-- The Erdős 592 predicate: `P β` says `ω^β → (ω^β, 3)²`. Problem 592 asks for `{β | P β}`. -/
def P (β : Ordinal.{u}) : Prop := OrdinalCardinalRamsey (ω ^ β) (ω ^ β) 3

/-! ## 2. Small kernel-checked facts about the relation itself -/

/-- A blue clique of cardinality `0` is always available. -/
theorem ramsey_card_zero (α β : Ordinal.{u}) : OrdinalCardinalRamsey α β 0 := by
  intro red blue _
  exact Or.inr ⟨∅, SimpleGraph.isClique_empty, by simp⟩

/-- The relation is monotone downwards in the blue cardinal. -/
theorem OrdinalCardinalRamsey.mono_card {α β : Ordinal.{u}} {c c' : Cardinal.{u}}
    (h : OrdinalCardinalRamsey α β c) (hc : c' ≤ c) : OrdinalCardinalRamsey α β c' := by
  intro red blue hcompl
  rcases h red blue hcompl with hred | ⟨s, hs, hcard⟩
  · exact Or.inl hred
  · subst hcard
    obtain ⟨t, hts, htc⟩ := Cardinal.le_mk_iff_exists_subset.1 hc
    exact Or.inr ⟨t, hs.subset hts, htc⟩

/-- **Triangle-free neighbourhood lemma.** If a 2-colouring admits no blue clique of cardinality
`3`, then the blue neighbourhood of every vertex is a red clique. This is the engine step shared
by every positive proof in the Specker / Chang / Schipperus family: it is what converts "no blue
triangle" into a supply of red cliques. -/
theorem blue_neighborhood_isClique {V : Type u} {red blue : SimpleGraph V}
    (hcompl : IsCompl red blue) (hno3 : ¬ ∃ s : Set V, blue.IsClique s ∧ #s = 3) (v : V) :
    red.IsClique {w | blue.Adj v w} := by
  intro x hx y hy hxy
  have hvx : blue.Adj v x := hx
  have hvy : blue.Adj v y := hy
  by_cases hb : blue.Adj x y
  · refine absurd ⟨{v, x, y}, ?_, ?_⟩ hno3
    · rintro a ha b hb' hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
      rcases ha with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hab
          | assumption
          | exact SimpleGraph.Adj.symm (by assumption)
    · have h1 : v ∉ ({x, y} : Set V) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        push_neg
        exact ⟨hvx.ne, hvy.ne⟩
      have h2 : x ∉ ({y} : Set V) := by simpa using hxy
      rw [Cardinal.mk_insert h1, Cardinal.mk_insert h2, Cardinal.mk_singleton]
      norm_num
  · have htop : red ⊔ blue = ⊤ := hcompl.sup_eq_top
    have hadj : (red ⊔ blue).Adj x y := by rw [htop]; simpa using hxy
    rcases hadj with h | h
    · exact h
    · exact absurd h hb

/-- An infinite subset of a set of order type `ω` again has order type `ω`. This is the bridge
from "there is an infinite red clique" to "there is a red `K_{ω^1}`", i.e. the step that turns
Ramsey's theorem into the `β = 1` instance of Erdős 592. -/
theorem typeLT_eq_omega0_of_infinite {s : Set (ω : Ordinal.{u}).ToType} (hs : s.Infinite) :
    typeLT s = ω := by
  refine le_antisymm ?_ ?_
  · have h := Ordinal.type_set_le s
    rwa [Ordinal.type_toType] at h
  · by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 hlt
    have h1 : (typeLT s).card = #s := Ordinal.card_type _
    rw [hn, Ordinal.card_nat] at h1
    have hfin : #s < Cardinal.aleph0 := by
      rw [← h1]; exact Cardinal.nat_lt_aleph0 n
    exact hs (Cardinal.lt_aleph0_iff_set_finite.1 hfin)

/-- The `β = 0` instance of Erdős 592: `ω^0 = 1`, and a single vertex is already a red `K_1`.
This is the one member of the answer set that is provable outright. -/
theorem P_zero : P (0 : Ordinal.{u}) := by
  intro red blue _
  have htype : typeLT ((ω : Ordinal.{u}) ^ (0 : Ordinal.{u})).ToType = 1 := by
    rw [Ordinal.type_toType, opow_zero]
  obtain ⟨hu⟩ := Ordinal.type_eq_one_iff_unique.1 htype
  haveI : Unique ((ω : Ordinal.{u}) ^ (0 : Ordinal.{u})).ToType := hu
  haveI : Nonempty (Set.univ : Set ((ω : Ordinal.{u}) ^ (0 : Ordinal.{u})).ToType) :=
    ⟨⟨default, Set.mem_univ _⟩⟩
  haveI : Subsingleton (Set.univ : Set ((ω : Ordinal.{u}) ^ (0 : Ordinal.{u})).ToType) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  refine Or.inl ⟨Set.univ, ?_, ?_⟩
  · exact fun a _ b _ hab => absurd (Subsingleton.elim a b) hab
  · rw [opow_zero]
    exact Ordinal.type_eq_one_of_unique _

/-! ## 3. Numeral scaffolding -/

private lemma zero_lt_three : (0 : Ordinal.{u}) < 3 := by
  have h : ((0 : ℕ) : Ordinal.{u}) < ((3 : ℕ) : Ordinal.{u}) := by
    exact_mod_cast (by omega : (0 : ℕ) < 3)
  simpa using h

private lemma zero_lt_two : (0 : Ordinal.{u}) < 2 := by
  have h : ((0 : ℕ) : Ordinal.{u}) < ((2 : ℕ) : Ordinal.{u}) := by
    exact_mod_cast (by omega : (0 : ℕ) < 2)
  simpa using h

private lemma zero_lt_four : (0 : Ordinal.{u}) < 4 := by
  have h : ((0 : ℕ) : Ordinal.{u}) < ((4 : ℕ) : Ordinal.{u}) := by
    exact_mod_cast (by omega : (0 : ℕ) < 4)
  simpa using h

private lemma one_lt_three : (1 : Ordinal.{u}) < 3 := by
  have h : ((1 : ℕ) : Ordinal.{u}) < ((3 : ℕ) : Ordinal.{u}) := by
    exact_mod_cast (by omega : (1 : ℕ) < 3)
  simpa using h

private lemma two_lt_three : (2 : Ordinal.{u}) < 3 := by
  have h : ((2 : ℕ) : Ordinal.{u}) < ((3 : ℕ) : Ordinal.{u}) := by
    exact_mod_cast (by omega : (2 : ℕ) < 3)
  simpa using h

private lemma three_lt_omega0 : (3 : Ordinal.{u}) < ω := by
  simpa using Ordinal.natCast_lt_omega0 3

private lemma two_lt_omega0 : (2 : Ordinal.{u}) < ω := by
  simpa using Ordinal.natCast_lt_omega0 2

private lemma four_lt_omega0 : (4 : Ordinal.{u}) < ω := by
  simpa using Ordinal.natCast_lt_omega0 4

private lemma three_ne_zero : (3 : Ordinal.{u}) ≠ 0 := ne_of_gt zero_lt_three
private lemma two_ne_zero' : (2 : Ordinal.{u}) ≠ 0 := ne_of_gt zero_lt_two
private lemma four_ne_zero : (4 : Ordinal.{u}) ≠ 0 := ne_of_gt zero_lt_four

/-- `3 ≤ ω^γ` whenever `γ ≠ 0`; used to place every `ω^γ` (γ ≠ 0) above Specker's cut-off. -/
theorem three_le_omega0_opow {γ : Ordinal.{u}} (hγ : γ ≠ 0) : (3 : Ordinal.{u}) ≤ ω ^ γ := by
  have h1 : (1 : Ordinal.{u}) ≤ γ := Order.one_le_iff_ne_zero.2 hγ
  have hle : (ω : Ordinal.{u}) ^ (1 : Ordinal.{u}) ≤ ω ^ γ :=
    Ordinal.opow_le_opow_right omega0_pos h1
  rw [opow_one] at hle
  exact le_of_lt (lt_of_lt_of_le three_lt_omega0 hle)

/-! ## 4. Counting indecomposable summands

Every ordinal is uniquely a decreasing finite sum of additively indecomposable ordinals; that
decomposition is exactly the Cantor normal form with each coefficient `c` read as `c` repeats of
`ω^e`. So the number of indecomposable summands of `γ` is the sum of the base-`ω` CNF
coefficients. Taking this as the DEFINITION makes the count a function, hence automatically
well-defined — no uniqueness theorem is needed to make the classification exclusive. -/

/-- The number of additively indecomposable summands of `γ`: the sum of the coefficients of the
base-`ω` Cantor normal form of `γ`. `indecCount 0 = 0`, `indecCount 3 = 3` (`3 = 1 + 1 + 1`),
`indecCount ω = 1`, `indecCount (ω + 1) = 2`. -/
noncomputable def indecCount (γ : Ordinal.{u}) : ℕ :=
  ((CNF ω γ).map fun p => p.2.card.toNat).sum

@[simp] theorem indecCount_zero : indecCount (0 : Ordinal.{u}) = 0 := by
  simp [indecCount]

/-- For a nonzero finite ordinal the CNF is the single term `(0, γ)`, so the count is `γ`. -/
theorem indecCount_of_lt_omega0 {γ : Ordinal.{u}} (h0 : γ ≠ 0) (h : γ < ω) :
    indecCount γ = γ.card.toNat := by
  rw [indecCount, Ordinal.CNF.of_lt h0 h]
  simp

theorem indecCount_one : indecCount (1 : Ordinal.{u}) = 1 := by
  rw [indecCount_of_lt_omega0 one_ne_zero (by simpa using Ordinal.natCast_lt_omega0 1)]
  simp

theorem indecCount_two : indecCount (2 : Ordinal.{u}) = 2 := by
  rw [indecCount_of_lt_omega0 two_ne_zero' two_lt_omega0]
  simp

/-- `3 = 1 + 1 + 1` is a sum of exactly three indecomposables. This is the fact that makes
`β = ω^3` the smallest open instance of Erdős 592. -/
theorem indecCount_three : indecCount (3 : Ordinal.{u}) = 3 := by
  rw [indecCount_of_lt_omega0 three_ne_zero three_lt_omega0]
  simp

theorem indecCount_four : indecCount (4 : Ordinal.{u}) = 4 := by
  rw [indecCount_of_lt_omega0 four_ne_zero four_lt_omega0]
  simp

/-! ## 5. The five classes

The classification is on `β` (the exponent in `α = ω^β`), exactly as Erdős 592 asks. -/

/-- **Class A** — `β < 3`. Literature verdict: TRUE (β = 0 trivially — see `P_zero`; β = 1 is
Ramsey's theorem; β = 2 is Specker [Sp57]). -/
def ClassA (β : Ordinal.{u}) : Prop := β < 3

/-- **Class B** — `β ≥ 3` and `β` is not additively indecomposable.
Literature verdict: FALSE (Galvin–Larson [GaLa74]; contains Specker's `3 ≤ β < ω`). -/
def ClassB (β : Ordinal.{u}) : Prop := 3 ≤ β ∧ ¬ IsPrincipal (· + ·) β

/-- **Class C** — `β = ω^γ ≥ 3` with `γ` a sum of one or two indecomposables.
Literature verdict: TRUE (Chang [Ch72] for count 1; Schipperus [Sc10] for count 2). -/
def ClassC (β : Ordinal.{u}) : Prop :=
  3 ≤ β ∧ ∃ γ : Ordinal.{u}, β = ω ^ γ ∧ indecCount γ ≤ 2

/-- **Class D** — `β = ω^γ ≥ 3` with `γ` a sum of exactly three indecomposables.
**THIS IS THE OPEN CASE OF ERDŐS 592.** -/
def ClassD (β : Ordinal.{u}) : Prop :=
  3 ≤ β ∧ ∃ γ : Ordinal.{u}, β = ω ^ γ ∧ indecCount γ = 3

/-- **Class E** — `β = ω^γ ≥ 3` with `γ` a sum of four or more indecomposables.
Literature verdict: FALSE (Schipperus [Sc10]). -/
def ClassE (β : Ordinal.{u}) : Prop :=
  3 ≤ β ∧ ∃ γ : Ordinal.{u}, β = ω ^ γ ∧ 4 ≤ indecCount γ

theorem isPrincipal_of_isOpow {β : Ordinal.{u}} (h : ∃ γ : Ordinal.{u}, β = ω ^ γ) :
    IsPrincipal (· + ·) β := by
  obtain ⟨γ, rfl⟩ := h
  exact isPrincipal_add_omega0_opow γ

theorem gamma_unique {γ δ : Ordinal.{u}} (h : (ω : Ordinal.{u}) ^ γ = ω ^ δ) : γ = δ :=
  (Ordinal.opow_right_inj one_lt_omega0).1 h

/-- **The classification is exhaustive.** Every ordinal lies in at least one of the five classes.
This is what "the remaining open case appears to be γ a sum of three indecomposables" actually
amounts to, now kernel-checked rather than asserted. -/
theorem frontier_exhaustive (β : Ordinal.{u}) :
    ClassA β ∨ ClassB β ∨ ClassC β ∨ ClassD β ∨ ClassE β := by
  rcases lt_or_ge β 3 with h | h
  · exact Or.inl h
  by_cases hp : IsPrincipal (· + ·) β
  · rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.1 hp with rfl | ⟨γ, hγ⟩
    · exact absurd (lt_of_lt_of_le zero_lt_three h) (lt_irrefl 0)
    · have hγ' : β = (ω : Ordinal.{u}) ^ γ := hγ.symm
      rcases lt_trichotomy (indecCount γ) 3 with h3 | h3 | h3
      · exact Or.inr (Or.inr (Or.inl ⟨h, γ, hγ', by omega⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, γ, hγ', h3⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, γ, hγ', by omega⟩)))
  · exact Or.inr (Or.inl ⟨h, hp⟩)

/-- **The classification is mutually exclusive.** No ordinal lies in two of the five classes. -/
theorem frontier_exclusive (β : Ordinal.{u}) :
    (ClassA β → ¬ ClassB β ∧ ¬ ClassC β ∧ ¬ ClassD β ∧ ¬ ClassE β) ∧
    (ClassB β → ¬ ClassC β ∧ ¬ ClassD β ∧ ¬ ClassE β) ∧
    (ClassC β → ¬ ClassD β ∧ ¬ ClassE β) ∧
    (ClassD β → ¬ ClassE β) := by
  refine ⟨fun hA => ⟨?_, ?_, ?_, ?_⟩, fun hB => ⟨?_, ?_, ?_⟩, fun hC => ⟨?_, ?_⟩, fun hD => ?_⟩
  · exact fun hB => absurd (lt_of_lt_of_le hA hB.1) (lt_irrefl _)
  · exact fun hC => absurd (lt_of_lt_of_le hA hC.1) (lt_irrefl _)
  · exact fun hD => absurd (lt_of_lt_of_le hA hD.1) (lt_irrefl _)
  · exact fun hE => absurd (lt_of_lt_of_le hA hE.1) (lt_irrefl _)
  · rintro ⟨-, γ, hγ, -⟩; exact hB.2 (isPrincipal_of_isOpow ⟨γ, hγ⟩)
  · rintro ⟨-, γ, hγ, -⟩; exact hB.2 (isPrincipal_of_isOpow ⟨γ, hγ⟩)
  · rintro ⟨-, γ, hγ, -⟩; exact hB.2 (isPrincipal_of_isOpow ⟨γ, hγ⟩)
  · rintro ⟨-, δ, hδ, hcδ⟩
    obtain ⟨γ, hγ, hcγ⟩ := hC.2
    have hEq : (ω : Ordinal.{u}) ^ γ = ω ^ δ := by rw [← hγ, ← hδ]
    have hgd : γ = δ := gamma_unique hEq
    subst hgd; omega
  · rintro ⟨-, δ, hδ, hcδ⟩
    obtain ⟨γ, hγ, hcγ⟩ := hC.2
    have hEq : (ω : Ordinal.{u}) ^ γ = ω ^ δ := by rw [← hγ, ← hδ]
    have hgd : γ = δ := gamma_unique hEq
    subst hgd; omega
  · rintro ⟨-, δ, hδ, hcδ⟩
    obtain ⟨γ, hγ, hcγ⟩ := hD.2
    have hEq : (ω : Ordinal.{u}) ^ γ = ω ^ δ := by rw [← hγ, ← hδ]
    have hgd : γ = δ := gamma_unique hEq
    subst hgd; omega

/-! ## 6. Where the known instances land

Four independent cross-checks that the classification reproduces the literature. -/

/-- Erdős 590 (`α = ω^ω`, i.e. `β = ω`): lands in class C, the class Chang [Ch72] settled TRUE. -/
theorem omega_mem_ClassC : ClassC (ω : Ordinal.{u}) := by
  refine ⟨le_of_lt three_lt_omega0, 1, (opow_one ω).symm, ?_⟩
  rw [indecCount_one]
  omega

/-- Erdős 591 (`α = ω^(ω^2)`, i.e. `β = ω^2`): lands in class C, the class Schipperus [Sc10]
settled TRUE. -/
theorem omega_sq_mem_ClassC : ClassC ((ω : Ordinal.{u}) ^ (2 : Ordinal.{u})) := by
  refine ⟨three_le_omega0_opow two_ne_zero', 2, rfl, ?_⟩
  rw [indecCount_two]

/-- Specker's negative range `3 ≤ β < ω`: every such `β` lands in class B, the Galvin–Larson
class known FALSE. (So Galvin–Larson subsumes Specker's negative result.) -/
theorem nat_mem_ClassB {n : ℕ} (hn : 3 ≤ n) : ClassB ((n : ℕ) : Ordinal.{u}) := by
  have h3n : ((3 : ℕ) : Ordinal.{u}) ≤ ((n : ℕ) : Ordinal.{u}) := by exact_mod_cast hn
  have h3n' : (3 : Ordinal.{u}) ≤ ((n : ℕ) : Ordinal.{u}) := by simpa using h3n
  refine ⟨h3n', ?_⟩
  intro hp
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.1 hp with h0 | ⟨γ, hγ⟩
  · rw [h0] at h3n'
    exact absurd (lt_of_lt_of_le zero_lt_three h3n') (lt_irrefl 0)
  · have hγ' : (ω : Ordinal.{u}) ^ γ = ((n : ℕ) : Ordinal.{u}) := hγ
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [opow_zero] at hγ'
      rw [← hγ'] at h3n'
      exact absurd (lt_of_lt_of_le one_lt_three h3n') (lt_irrefl _)
    · have h1 : (1 : Ordinal.{u}) ≤ γ := Order.one_le_iff_ne_zero.2 hγ0
      have hw : (ω : Ordinal.{u}) ^ (1 : Ordinal.{u}) ≤ ω ^ γ :=
        Ordinal.opow_le_opow_right omega0_pos h1
      rw [opow_one, hγ'] at hw
      exact absurd (lt_of_lt_of_le (Ordinal.natCast_lt_omega0 n) hw) (lt_irrefl _)

/-- **THE SMALLEST OPEN INSTANCE OF ERDŐS 592.**
`3 = 1 + 1 + 1` is a sum of exactly three additively indecomposable ordinals, so `β = ω^3` lies
in the open class D. Unwinding: the smallest ordinal for which `ω^β → (ω^β, 3)²` is undecided by
the literature is `β = ω^3`, i.e. the open question is

    ω^(ω^3) → (ω^(ω^3), 3)² ?
-/
theorem omega_pow_three_open : ClassD ((ω : Ordinal.{u}) ^ (3 : Ordinal.{u})) :=
  ⟨three_le_omega0_opow three_ne_zero, 3, rfl, indecCount_three⟩

/-- Class D is nonempty — the problem really is unfinished, and this exhibits a witness. -/
theorem ClassD_nonempty : ∃ β : Ordinal.{u}, ClassD β :=
  ⟨_, omega_pow_three_open⟩

/-- An ordinal with exactly three indecomposable summands is at least `3`. (`0, 1, 2` have
counts `0, 1, 2`.) -/
theorem three_le_of_indecCount_three {γ : Ordinal.{u}} (hc : indecCount γ = 3) :
    (3 : Ordinal.{u}) ≤ γ := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 (hlt.trans three_lt_omega0)
  have hn3 : ((n : ℕ) : Ordinal.{u}) < ((3 : ℕ) : Ordinal.{u}) := by simpa using hlt
  have hn : n < 3 := by exact_mod_cast hn3
  have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [show ((0 : ℕ) : Ordinal.{u}) = 0 by simp, indecCount_zero] at hc; omega
  · rw [show ((1 : ℕ) : Ordinal.{u}) = 1 by simp, indecCount_one] at hc; omega
  · rw [show ((2 : ℕ) : Ordinal.{u}) = 2 by simp, indecCount_two] at hc; omega

/-- **`ω^3` is the LEAST member of the open class.** Every undecided `β` satisfies `ω^3 ≤ β`,
and `ω^3` itself is undecided (`omega_pow_three_open`). So the single smallest open instance of
Erdős 592 is exactly

    ω^(ω^3) → (ω^(ω^3), 3)² ?
-/
theorem omega_pow_three_least {β : Ordinal.{u}} (h : ClassD β) :
    (ω : Ordinal.{u}) ^ (3 : Ordinal.{u}) ≤ β := by
  obtain ⟨-, γ, rfl, hc⟩ := h
  exact Ordinal.opow_le_opow_right omega0_pos (three_le_of_indecCount_three hc)

/-- `ω^3` is the minimum of class D, stated as a single fact. -/
theorem ClassD_least : ClassD ((ω : Ordinal.{u}) ^ (3 : Ordinal.{u})) ∧
    ∀ β : Ordinal.{u}, ClassD β → (ω : Ordinal.{u}) ^ (3 : Ordinal.{u}) ≤ β :=
  ⟨omega_pow_three_open, fun _ h => omega_pow_three_least h⟩

/-- Class E is nonempty: `γ = 4 = 1+1+1+1` is a sum of four indecomposables, so `β = ω^4` is a
Schipperus counterexample. -/
theorem omega_pow_four_mem_ClassE : ClassE ((ω : Ordinal.{u}) ^ (4 : Ordinal.{u})) := by
  refine ⟨three_le_omega0_opow four_ne_zero, 4, rfl, ?_⟩
  rw [indecCount_four]

/-! ## 7. Why no monotonicity argument can close the gap

Schipperus settles `indecCount γ ≤ 2` positively and `indecCount γ ≥ 4` negatively, so the open
class D sits BETWEEN a positive and a negative region. The obvious hope is a monotonicity bridge.
The theorem below rules that out: conditional only on the three literature facts about *small*
ordinals (Specker's `P 2`, Specker's `¬ P 3`, Chang's `P ω`), the set `{β | P β}` is neither
upward nor downward closed, so no order-theoretic transfer principle of either direction can
exist. Any attack on class D must be specific to the count-3 shape. -/
theorem no_monotone_bridge (h2 : P (2 : Ordinal.{u})) (h3 : ¬ P (3 : Ordinal.{u}))
    (homega : P (ω : Ordinal.{u})) :
    (∃ a b : Ordinal.{u}, a < b ∧ P a ∧ ¬ P b) ∧
    (∃ a b : Ordinal.{u}, a < b ∧ ¬ P a ∧ P b) :=
  ⟨⟨2, 3, two_lt_three, h2, h3⟩, ⟨3, ω, three_lt_omega0, h3, homega⟩⟩

end Erdos592
