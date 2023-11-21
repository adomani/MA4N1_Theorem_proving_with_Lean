import Mathlib.Tactic
import MA4N1_2023.help_me

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
#check Quot.sound
end

/-- `Week` is the finite Type with exactly 7 constructors, one for each day of the week. -/
inductive Week
  | Mon
  | Tue
  | Wed
  | Thu
  | Fri
  | Sat
  | Sun

/-- `week_end? d` is the predicate on a day of the `Week`,
answering the question "Is `d` part of the week-end?" -/
def week_end? : Week → Bool
  -- the "anonymous dot-notation":
  -- Lean is expecting a term of type `Week`, so `.Sat` gets parsed as `Week.Sat
  | .Sat => true
  | .Sun => true
  -- every other day of the `Week` returns `false`
  | _ => false

instance Week_setoid : Setoid Week where
  r x y := week_end? x = week_end? y
  iseqv := by
    constructor
    · exact? says exact fun x => rfl
    · exact? says exact fun {x y} a => id a.symm
    · intros x y z xy yz
      exact xy.trans yz
    done

--  If you like an equivalent but more obfuscated version of the instance above, here it is!
/-
instance : Setoid Week where
  r := (work? · = work? ·)
  iseqv := { refl  := fun _ => rfl
             symm  := fun {_ _} => .symm
             trans := fun {_ _ _} => .trans }
-/

@[simp]
lemma sat_sun : (⟦Week.Sat⟧ : Quotient Week_setoid) = ⟦Week.Sun⟧ := by
  exact Quotient.eq.mpr rfl
  done

example : (⟦Week.Sat⟧ : Quotient Week_setoid) ≠ ⟦Week.Mon⟧ := by
  intro h
  simp only [Quotient.eq] at h
  cases h
  done

example : (⟦Week.Sat⟧ : Quotient Week_setoid) ≠ ⟦Week.Mon⟧ := by
  simp only [ne_eq, Quotient.eq]
  rintro ⟨⟩
  done

@[simp]
lemma equiv_class_of_Sunday (d : Week) : (⟦Week.Sun⟧ : Quotient Week_setoid) = ⟦d⟧ ↔
    d ∈ ({Week.Sat, Week.Sun} : Set _) := by
  -- `rcases d with _ | _ | _ | _ | _ | _ | _ <;>` also works instead of `induction`
  induction d <;>
    simp <;>
    rintro ⟨⟩
  done

@[simp]
lemma equiv_class_of_Monday (d : Week) : (⟦Week.Mon⟧ : Quotient Week_setoid) = ⟦d⟧ ↔
    d ∈ ({Week.Mon, Week.Tue, Week.Wed, Week.Thu, Week.Fri} : Set _) := by
  -- `rcases d with _ | _ | _ | _ | _ | _ | _ <;>` also works instead of `induction`
  induction d <;>
    simp <;> try rfl
  · rintro ⟨⟩
  · rintro ⟨⟩
  done

--  `≃` is the symbol for an `Equiv
#print Equiv

/-!
An `Equiv` is a structure with two input types `α` and `β` and 4 fields:
* `toFun`     -- a function `α → β`;
* `invFun`    -- a function `β → α`;
* `left_inv`  -- a proof that `invFun` is a left-inverse to `toFun`;
* `right_inv` -- a proof that `invFun` is a right-inverse to `toFun`.
-/

def Equiv.ff : Quotient Week_setoid ≃ Bool where
  -- the function from the quotient to `Bool` is the `Quotient.lift` of the function `week_end?`.
  -- in maths, it is more common to say that `week_end?` "descends" to the quotient.
  toFun := Quotient.lift week_end? (fun a b => id)
  -- the function from `Bool` to the quotient assigns `true` to `⟦.Sun⟧` and `false` to `⟦.Mon⟧`
  invFun b := if b then ⟦.Sun⟧ else ⟦.Mon⟧
  -- it is now up to you to prove that these two functions are inverses of each other!
  -- the tactic `hint_inverse` will give you a hint on how to start the proof!
  left_inv := by
    rintro ⟨d⟩
    dsimp only
    split_ifs
    · apply (equiv_class_of_Sunday d).mpr
      induction d <;> aesop
    · apply (equiv_class_of_Monday d).mpr
      induction d <;> aesop
    done
  right_inv := by
    simp only
    done

end TPwL
