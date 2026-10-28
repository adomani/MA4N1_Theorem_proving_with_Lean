import MA4N1.Init
-- Note that we import `Mathlib`, since we want to maximise our chance of finding
-- theorems and definitions that are already available.
import Mathlib

namespace RandomStatements

/-!
This file contains my formalisation attempts of theorems that were suggested during the lectures.

I have tried to not polish them too much and to leave the code that I used to find the various
lemmas and definitions, so that you can see how I went about formalising the statements.
-/

section Presentation
/-!
# Fundamental theorem of algebra

The first statement is the fundamental theorem of algebra.

Of various equivalent statements, I chose the formulation "ℂ is algebraically closed",
since I imagine it will be the easiest to formalise on the spot.

I am aware that this will feel like cheating, but, when you are on your own, you should
find the easy way out, if you can!
-/

/-
Looking for the concept of "algebraically closed" in Mathlib, since I imagine it exists.

I came across this lemma using autocompletion: I know this could be useful, since
the `Geometrically` in `GeometricallyReduced` means that the property holds over
an algebraic closure.
I did not follow this path, but indeed if you Ctrl-click on this lemma and then on
`IsGeometricallyReduced`, you will see that `AlgebraicClosure` exists and then you are
really close.
-/
#check Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced

/-
Instead, I opened the [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/index.html)
and started typing `isalg[ebraicallyclosed]` and saw `IsAlgClosed`: that's what we wanted!
-/
#check IsAlgClosed

-- Making sure that `ℂ` exists (hover over ℂ to see how to type it).
#check ℂ

/-
Finally, the fundamental theorem of algebra.  Since we stated it cleanly,
`exact?` actually finds the proof for us!
-/
example : IsAlgClosed ℂ := by
  exact Complex.isAlgClosed

/-!
# Pigeonhole principle

The next statement is the pigeonhole principle.  In this case, "the" pigeonhole principle,
is really more of a family of possible different statements.

I decided that one option was to say that if `A` and `B` are sets,
`A` has cardinality `n + 1` and `B` has cardinality `n`,
then any function `f : A → B` is not injective.

*Warning*. Some of these attempts are incorrect!
-/

theorem flawed_pigeonhole {A B : Type*} {n : ℕ} (f : A → B)
    (hA : Nat.card A = n + 1) (hB : Nat.card B = n) :
    ¬ Function.Injective f := by
  sorry

/-
Here is why `flawed_pigeonhole` is flawed: we can prove `False` using it!
I'll leave you to figure out what this `example` does.
-/
example : False := by
  have := flawed_pigeonhole (A := Unit) (B := ℕ) (n := 0) (fun _ => 0) (by simp) (by simp)
  exact?  -- we are missing a hypothesis!

/-
What `flawed_pigeonhole` is missing is that `A` and `B` are finite sets.
The source of confusion is that `Nat.card` is defined for all types,
and for infinite ones, it returns `0`.
-/

example {A B : Type*} [Finite A] [Finite B] {n : ℕ} (f : A → B)
    (hA : Nat.card A = n + 1) (hB : Nat.card B = n) :
    ¬ Function.Injective f := by
  sorry

/-
This statement is probably true, but definitely can be cleaned up still!
First, finiteness of `A` follows from the fact that `Nat.card A` is non-zero.
Second, we don't actually need the cardinality of `A` to be one more than the one of `B`,
we just need it to be strictly larger.
-/

example {A B : Type*} [Finite B] (f : A → B) (hAB : Nat.card B < Nat.card A) :
    ¬ Function.Injective f := by
  sorry

/-
We can still improve this: if instead of the `Nat.card` we use the actual cardinality
(Mathlib's `Cardinal`), then we don't even need to assume that `B` is finite.
-/
#check Cardinal

-- It turns out that, with `open scoped Cardinal`, we can use `#A` for the cardinal of `A`.

open scoped Cardinal in
example {A B : Type _} (f : A → B) (hAB : #B < #A) :
    ¬ Function.Injective f := by
  sorry

/-
If you observe carefully the statement, you will notice that I changed `Type*` for `Type _`:
this is a technicality and it is easier to do this, than to wrangle universe levels.
A consequence of this change is that the universe levels of `A` and `B` end up being the same.

For completeness, and if you are really curious about how to handle arbitrary universe levels,
here is one way -- feel free to ignore this!
-/
open Cardinal in
universe u v in
example {A : Type u} {B : Type v} (f : A → B) (hAB : lift.{max u v} #B < lift #A) :
    ¬ Function.Injective f := by
  sorry

-- Now that we are here, though, the contrapositive of this statement looks like a tautology!
open scoped Cardinal in
example {A B : Type _} (f : A → B) (hf : Function.Injective f) :
    #A ≤ #B := by
  exact Cardinal.mk_le_of_injective hf -- found using `exact?`

-- The version with universe levels is also easy to prove, but `exact?` does not prove it directly.
open Cardinal in
universe u v in
example {A : Type u} {B : Type v} (f : A → B) (hf : Function.Injective f) :
    lift.{max u v} #A ≤ lift #B := by
  refine lift_mk_le.mpr ?_ -- found using `apply?` and selecting what looked more promising
  use f

-- handshake lemma

example {A : Type*} (h6 : 6 ≤ Nat.card A) (friends : A → A → Prop)
    (hSymm : ∀ a b : A, friends a b ↔ friends b a) :
    ∃ a b c : A,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ((friends a b ∧ friends a c ∧ friends b c) ∨
       (¬ friends a b ∧ ¬ friends a c ∧ ¬ friends b c)) := by
  sorry

-- chain rule

#check hasDerivAt_abs

example {f g : ℝ → ℝ} {x : ℝ} {f' g' : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' (f x)) :
    HasDerivAt (g ∘ f) (g' * f') x := by
  exact?
  sorry

end Presentation

end RandomStatements
