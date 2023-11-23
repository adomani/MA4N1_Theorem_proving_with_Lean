import Mathlib.Tactic

namespace TPwL

/-!
#  Finteness in Mathlib

Finiteness can be a tricky concept for formalisation.
Part of the reason for this, is that it often means dealing with computability issues,
that tend to be not too familiar for mathematicians.

This file is intended as a first introduction to finiteness.

We will touch upon `Fintype` and `Finite`, two typeclasses dealing with finiteness.

As usual, let's see the definition.
-/

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

So, ultimately, `Finite α` means that you chose a bijection of `α` with the finite set `0, 1, ..., n`.
-/

#where
end TPwL
