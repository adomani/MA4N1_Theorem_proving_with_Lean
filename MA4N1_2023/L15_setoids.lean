import Mathlib.Tactic

namespace TPwL_setoids

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

instance parity_setoid : Setoid ℤ where
  r x y := 2 ∣ x - y
  iseqv := {
    refl := by
      intros
      exact? says exact Int.ModEq.dvd rfl
    symm := by
      intros x y
      exact dvd_sub_comm.mp
      done
    trans := by
      intros x y z
      convert dvd_add using 2
      · simp
      · infer_instance
      · infer_instance
      done
  }

--  `≃` is the symbol for an `Equiv
#print Equiv

/-!
An `Equiv` is a structure with two input types `α` and `β` and 4 fields:
* `toFun`     -- a function `α → β`;
* `invFun`    -- a function `β → α`;
* `left_inv`  -- a proof that `invFun` is a left-inverse to `toFun`;
* `right_inv` -- a proof that `invFun` is a right-inverse to `toFun`.
-/

lemma equiv_class_of_zero (d : ℤ) :
    (⟦0⟧ : Quotient parity_setoid) = ⟦d⟧ ↔ 2 ∣ d := by
  simp only [Quotient.eq]
  conv_rhs => rw [← sub_zero d]
  exact comm
  done

lemma equiv_class_of_one (d : ℤ) :
    (⟦1⟧ : Quotient parity_setoid) = ⟦d⟧ ↔ 2 ∣ d - 1 := by
  simpa only [Quotient.eq] using comm
  done

--  This lemma is part of the Friday support class
lemma two_dvd_sub_one_iff (d : ℤ) : 2 ∣ d - 1 ↔ ¬ 2 ∣ d := by
  sorry
  done

/-!
The next `example` is an excuse to highlight the use of `Quotient.lift`
-/

#check Quotient.lift

/-!
`Quotient.lift` is the result that says that a function on the quotient "is the same"
as a function on the original set that is constant on equivalence classes.

In passing, note that the (data-carrying) fields `toFun` and `invFun` have a strong impact
on how easy it is to prove the subsequent results.
In particular, I stated the lemmas `equiv_class_of_zero, equiv_class_of_one` and
`two_dvd_sub_one_iff` to get the proofs working.

Note also how `decide_eq_decide` in `toFun` taints the proofs.
-/

example : Quotient parity_setoid ≃ Bool where
  -- the function from the quotient to `Bool` is the `Quotient.lift` of the function
  -- "Does 2 divide `x`?".
  -- in maths, it is more common to say that the function "descends" to the quotient.
  toFun := Quotient.lift (fun x => 2 ∣ x) (fun x y xy => decide_eq_decide.mpr (Int.dvd_iff_dvd_of_dvd_sub xy))
  -- the function from `Bool` to the quotient assigns `true` to `⟦0⟧` and `false` to `⟦1⟧`
  invFun b := if b then ⟦0⟧ else ⟦1⟧
  left_inv := by
    rintro ⟨d⟩
    dsimp only
    split_ifs with h
    · apply (equiv_class_of_zero d).mpr
      convert h
      rw [← decide_eq_decide]
      simp only [Bool.decide_coe]
    · apply (equiv_class_of_one d).mpr
      apply (two_dvd_sub_one_iff d).mpr
      convert h
      rw [← decide_eq_decide]
      simp
    done
  right_inv := by
    simp only
    done

end

end TPwL_setoids
