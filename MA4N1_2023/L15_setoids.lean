import Mathlib.Tactic

namespace TPwL

/-!
#  `Setoid`s and equivalence relations

Many constructions in mathematics are obtained by "passing to the quotient".
The "quotient" is usually an implicit way of referring to some equivalnce relation
that we are using to identify different elements of some set.

The following `Setoid` is copied from `Core` Lean.
-/

#check Setoid

/--
A setoid is a type with a distinguished equivalence relation, denoted `≈`.
This is mainly used as input to the `Quotient` type constructor.

Note that I copied it here, but with a *lower-case* `S`!
This is so that it does not mess up the in-built one that we use later.
-/
class setoid (α : Sort*) where
  /-- `x ≈ y` is the distinguished equivalence relation of a setoid. -/
  r : α → α → Prop
  /-- The relation `x ≈ y` is an equivalence relation. -/
  iseqv : Equivalence r

/-!

Thus, a `Setoid` is simply
* a Type `α`;
* a relation called `Setoid.r` on `a`;
* a proof `iseqv` that `r` is an equivalence relation.

Notice that it is a `class`.
This means that we can use the typeclass system to take over for us, when we want.

This also means that we should have some idea of how to set things up correctly!

Here is an easy example:
every Type is a `Setoid` with respect to the identity equivalence relation.
-/

def Setoid_eq (α : Type*) : Setoid α where
  r x y := x = y
  iseqv := by
    --exact? says exact eq_equivalence -- works
    constructor
    · exact? says exact fun x => rfl
    · exact? says exact fun {x y} a => id a.symm
    · intros x y z
      exact Eq.trans
    done

section

/--  A copy of the natural numbers, with none of the instances already registered. -/
def myN := ℕ

variable {a b : myN}

/- We record a `Setoid` instance on `myN`, determined by the equality relation. -/
instance Nat_setoid : Setoid myN := Setoid_eq ℕ

/-!
Having a Setoid gives us two convenient notations.

First, the notation `a ≈ b` for `HasEquiv.Equiv`.

This is a very primitive notion: simply a Type with a relation on it.
The relation is called `Equiv`, but it is simply a relation.
Of course, the most likely intended use-case is when `HasEquiv.Equiv` is an equivalence relation.
-/
#check a ≈ b

#print HasEquiv
#check HasEquiv.Equiv

--  A `HasEquiv` is just any relation, no extra requirement.
example : HasEquiv Nat where
  Equiv a _b := a = 0

/-!
Second, the notation `⟦x⟧` for `Quotient s`, if `s : Setoid X` is available.
-/

#check (⟦a⟧ : Quotient Nat_setoid)

variable {α : Type}

variable (r : α → α → Prop) in
--  Good for a relation that is not required to be an equivalence relation
#check Quot r
#print Quot

--  Better, when the relation is an equivalence relation
--  Takes a `Setoid` an input.
#check Quotient

variable [s : Setoid α] in
#check Quotient s

example : a ≈ b ↔ Setoid.r a b := by
  exact? says exact Iff.rfl
  done

example : (⟦a⟧ : Quotient Nat_setoid) = ⟦b⟧ ↔ a ≈ b := by
  exact? says exact Quotient.eq
  done

#check Quotient.eq_rel

end

end TPwL
