import Mathlib.Tactic
import Mathlib.NumberTheory.ZetaFunction

namespace TPwL

/-!
#  Finiteness in Mathlib

Finiteness can be a tricky concept for formalisation.
Part of the reason for this, is that it often means dealing with computability issues,
that tend to be not too familiar for mathematicians.

This file is intended as a first introduction to finiteness.

We will touch upon `Fintype` and `Finite`, two typeclasses dealing with finiteness,
as well as some implied "finite-adjacent" classes/structures.

##  `Finite`

As usual, let's see the definition.
-/

#print Finite

-- as usual, note the lower-case `f`inite,
-- to avoid later confusing Lean when we later use `Mathlib`'s `Finite`.
class inductive finite (α : Sort*) : Prop
  | intro {n : ℕ} : α ≃ Fin n → finite _

/-!
The definition of `Finite α` simply means that the only way of having `Finite α`
is to provide an `Equiv` between `a` and `Fin n` for some `n`.

In turn, for `n : ℕ`, `Fin n` is the type with `n` elements.
This is defined as a structure with two fields:
* a natural number `a`;
* a proof of the inequality `a < n`.

So, ultimately, `Finite α` means that there is a bijection of `α` with the finite set `0, 1, ..., n`.

This class is the less-computable one.

##  `Fintype`

-/

#print Fintype

/-- `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class fintype (α : Type*) where  -- the actual class has a capital `F`
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α
  /-- A proof that `elems` contains every element of the type -/
  complete : ∀ x : α, x ∈ elems

/-!

Thus, an instance of `Fintype α` specifies a `Finset a` and a proof that every element of `α` belongs
to this subset.

In turn, a `Finset` is a `Multiset` with no repetitions, which itself is a `List` up to permutation.

Thus, ultimately, an instance of `Fintype α` is an enumeration of all the elements of `α`, each listed
exactly once, up to their order.

##  `Finite α` vs `Fintype α`
-/

#check finite_iff_exists_equiv_fin

/-!
The lemma `finite_iff_exists_equiv_fin` asserts the equivalence
`Finite α ↔ (∃ n, Nonempty (α ≃ Fin n))) : finite_iff_exists_equiv_fin`.

Is there a similar characterisation for `Fintype`?

Of course, it depends on what you mean by "similar".
However, I would argue that the answer is "No"!.

In my opinion, the main difference between `Finite` and `Fintype` is that
* the former is a `Prop`osition, while
* the latter is a `Type`.
-/
variable {α : Sort} in
#check (Finite α : Prop)

variable {α : Type} in
#check (Finite α : Prop)

variable {α : Type} in
#check (Fintype α : Type)

/-!
To produce a `Finite` instance on a Type, you only need to prove a `Prop`osition.

To produce a `Fintype` instance on a Type, you actually have to provide some *data*
(e.g. an enumeration of your type) and then show that this data satisfies some properties.

In informal mathematics, it is very easy to convert a `Prop`osition into a `Type`:
the statement `∃ n, Nonempty (α ≃ Fin n)` converts to `∃ n, ∃ f : α ≃ Fin n` and
from this you can simply say "Pick an `n` and a bijection `f : α → Fin n`".
This last step converts a `Prop`osition into a `Type`:
we go from simply asserting the existence of a natural number with some property to
a natural number itself.

##  Why is converting a `Prop` to a `Type` a "problem"?

In practice, it is not for "mathematics".
However, part of the issue is that Lean is also building code associated with what it checks.
Converting a `Prop`osition to a `Type` leads to a gap in the code-production.
Here is an example that maybe clears up what the underlying issue is.
-/

open Classical in
noncomputable
def twin_primes? : ℕ :=
if ∀ M, ∃ n, M ≤ n ∧ (Prime n) ∧ (Prime (n + 2)) then 0
                                                 else 1

/-!
Using only `open Classical`, Lean wants us to mark the `def`inition as `noncomputable`.
This is because we are asking Lean to convert a `Prop`osition into a `Type`:
the "value" of `twin_primes?` depends on whether `Prop`osition that
there are infinitely many twin primes is `True` or `False`.

If we do not `open Classical`, then Lean tells us that
it failed to synthesize a `Decidable` instance in `twin_primes?`.

The `Decidable` instance that Lean would like would precisely
supply the "data" that is missing from the `Prop`osition.

Here is a similar example.
-/
open Classical in
noncomputable
def RH? : Bool := RiemannHypothesis

/-!

_Conclusion._
In informal mathematics, there is very little distinction between `Type` and `Prop`.
In constructive mathematics, this is not the case:
there is a much bigger gap between `Prop`ositions and `Type`s.

In Lean, there is support for both, constructive and non-constructive mathematics
(even though `Mathlib` is very often non-constructive and closer to the kind of
mathematics to which you have been exposed here at Warwick).

#  Bonus

Let's see how to work in the presence of `Classical` and `noncomputable`.
-/
open Classical in
/-- `Prop_to_Bool?` is always `true`: not only the condition is `True`, also both arms of the
`if ... then ... else ...` statement end in `true`! -/
def Prop_to_Bool? : Bool :=
if ∃ n, n = 0 then true
              else true

/-!  Proving that `Prop_to_Bool?` is `True` is easy:
we look at the definition and `simp` finishes the proof
-/
example : Prop_to_Bool? = true := by
  unfold Prop_to_Bool?
  simp only [exists_eq, ite_self]
  done

/-!
The next example uses the Type `Unit`:
this type has a unique constructor, called `unit`.
For convenience, there is notation for `unit` and we can simply write `()` instead of `unit`.
-/

#print PUnit

open Classical in
def Prop_to_type? : Unit :=
if ∃ n, n = 0 then ()
              else ()

example : Prop_to_type? = () := by
  unfold Prop_to_type?
  rfl
  done

open Classical in
noncomputable
def Prop_to_Bool_again? : Bool :=
if ∃ n, n = 0 then true
              else false

example : Prop_to_Bool_again? = true := by
  unfold Prop_to_Bool_again?
  simp only [exists_eq, ite_true]
  done



end TPwL
