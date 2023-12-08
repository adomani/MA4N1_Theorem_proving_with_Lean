import Mathlib.Tactic
import Mathlib.NumberTheory.ZetaFunction

namespace TPwL_finiteness

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

So, ultimately, `Finite α` means that there is a bijection of `α` with the finite set `0, 1, ..., n-1`.

The `Finite` class is less computable than `Fintype`.
In fact, there is an instance that, given a `Fintype` instance on a Type,
there is an automatic `Finite` instance on that Type.
-/

#check Finite.of_fintype

/-!

This brings us to wondering about what is the `Fintype` class.

##  `Fintype`

-/

#print Fintype

/-- `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class fintype (α : Type*) where  -- note the lower-case `f`, to avoid issues.
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α
  /-- A proof that `elems` contains every element of the type -/
  complete : ∀ x : α, x ∈ elems

/-!
As you can see, `Fintype` is built from a finite set `elems : Finset α`,
and a proof that every element of `α` belongs to this finite set.

A `Finset` is itself a `Multiset` with no duplicate elements and
a `Multiset` is a `List` up to reordering.

This took us down a few iterations, but hopefully we now have a clearer picture:
* `Finite α`  means that, for some `n`, there is an equivalence between `{0, ..., n-1}` and `α`;
* `Fintype α` means that there is a `List` enumerating all and only the elements of `α`
  with no repetitions, up to reordering.

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

In practice, the conversion is not a problem for "mathematics".
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

--  The Type `Unit` is the specialisation of the "polymorphic" `PUnit` at `Type`.
#print PUnit

open Classical in
/-- `Prop_to_type?` is always `()` for 3 reasons:
* the condition is `True`,
* both arms of the `if ... then ... else ...` statement end in `true`,
* there is a unique function to `Unit` from *anything*!
-/
def Prop_to_type? : Unit :=
if ∃ n, n = 0 then ()
              else ()

example : Prop_to_type? = () := by
  unfold Prop_to_type?
  rfl  -- this time, the proof is even simpler than before `rfl` closes the goal!
  done

--  We make our goals a little harder: the arms differ, though the condition is unchanged.
open Classical in
noncomputable
def Prop_to_Bool_again? : Bool :=
if ∃ n, n = 0 then true
              else false

example : Prop_to_Bool_again? = true := by
  unfold Prop_to_Bool_again?
  simp only [exists_eq, ite_true]
  done

-- Here is a proof that "there is a unique function to `Unit` from *anything*".
variable {α} in
example : Subsingleton (α → Unit) := by
  infer_instance
  --exact? says exact instSubsingletonForAll
  done

/-!

#  Digression on `Unit` and `Subsingleton`

First of all, `Subsingleton α` means that any two elements of `α` are equal.
This is equivalent to saying that `α` has at most one element.
The main example of a `Subsingleton` is `Prop`:
by proof-irrelevance, any `lemma/theorem` in Lean as at most one proof:
* it actually has a proof (and all proofs are "equal") if it is provable;
* it has no proof if it is unprovable.

(The statement above is maybe more of a tautology than usual!
I wanted to highlight the concept of *proof-irrelevance* with it, though.)

Why are `Unit` and `Subsingleton` important?

For formalisation, mostly as a ripple effect from programming and computer science.
To first approximation, tactics do nothing but manipulating the "state"
(roughly, what you see in the Infoview).
The actual proof that you construct is a "by-product" of this manipulation.
However, the operations that the tactics perform are themselves part of the Lean
language and therefore are terms of some Type.
However, as they manipulate the "state" and do not really have a return value.
Tactics are encoded as functions from what you type (technically, `Syntax`), to
`Unit` (more precisely, there are `Monad`s involved, but that is besides the point).
The intuitive idea is that what you type instructs the computer to perform some
computations that modify the state but do not really have any return value.
When a proof is complete, Lean inspects the final state that the succession of
tactics produced and verifies that it matches whatever you had set out to prove.
If this type-checking passes, then Lean accepts your proof as valid and adds to
the environment a declaration with the name that you specified and the proof that
you built.
If the type-checking fails, then Lean throws some error.
-/

--  We set our target: given the LHS, we want to produce a term of Type the RHS
theorem blah (assumption : ℕ) : 0 + 0 = 0 := by
--  inside the `by` we are in the "tactic world": we are building a computer program
  have : 0 * assumption = 0 := by simp
  nth_rewrite 1 [← this]
  let x : ℕ := 0
  show 0 * assumption + x = 0
  simp
  done
/-!
Here, the `theorem` disappeared.  The "consequences" are that there is a declaration
called `blah` whose Type is the `Prop`osition `0 + 0 = 0` and whose term is...
-/
#print blah

/-!
The following is a simpler proof.  This highlights the same, except that, of course,
the declaration `blah1` that is produced is much simpler.
-/
theorem blah1 (assumption : ℕ) : 0 + 0 = 0 := by
  rfl
  done

#print blah1

--  Proof-irrelevance does not see the difference between the two terms used to prove `0 + 0 = 0`.
example : blah 3 = blah1 0 := by
  rfl
  done

end TPwL_finiteness
