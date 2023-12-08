import Mathlib.Tactic
import MA4N1_2023.help_me

namespace TPwL_setoids_week_end_questions

/-!
#  `Setoid`s and equivalence relations
-/

--  A left-over lemma from the lecture on Tuesday
lemma two_dvd_sub_one_iff (d : ℤ) : 2 ∣ d - 1 ↔ ¬ 2 ∣ d := by
  sorry
  done

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
  -- Lean is expecting a term of type `Week`, so `.Sat` gets parsed as `Week.Sat`
  | .Sat => true
  | .Sun => true
  -- every other day of the `Week` returns `false`
  | _ => false

instance Week_setoid : Setoid Week where
  r x y := week_end? x = week_end? y
  iseqv := by
    sorry
    done

--  If you like an equivalent but more obfuscated version of the instance above, here it is!
/-
instance : Setoid Week where
  r := (work? · = work? ·)
  iseqv := { refl  := fun _ => rfl
             symm  := fun {_ _} => .symm
             trans := fun {_ _ _} => .trans }
-/

namespace Week

@[simp]
lemma sat_sun : (⟦Sat⟧ : Quotient Week_setoid) = ⟦Sun⟧ := by
  sorry
  done

example : (⟦Sat⟧ : Quotient Week_setoid) ≠ ⟦Mon⟧ := by
  sorry
  done

example : (⟦Sat⟧ : Quotient Week_setoid) ≠ ⟦Mon⟧ := by
  sorry
  done

lemma equiv_class_of_Sunday (d : Week) : (⟦Sun⟧ : Quotient Week_setoid) = ⟦d⟧ ↔
    d ∈ ({Sat, Sun} : Set _) := by
  sorry
  done

lemma equiv_class_of_Monday (d : Week) : (⟦Mon⟧ : Quotient Week_setoid) = ⟦d⟧ ↔
    d ∈ ({Mon, Tue, Wed, Thu, Fri} : Set _) := by
  sorry
  done

example : Quotient Week_setoid ≃ Bool where
  -- the function from the quotient to `Bool` is the `Quotient.lift` of the function `week_end?`.
  -- in maths, it is more common to say that `week_end?` "descends" to the quotient.
  toFun := Quotient.lift week_end? (fun a b => id)
  -- the function from `Bool` to the quotient assigns `true` to `⟦.Sun⟧` and `false` to `⟦.Mon⟧`
  invFun b := if b then ⟦Sun⟧ else ⟦Mon⟧
  -- it is now up to you to prove that these two functions are inverses of each other!
  -- the tactic `hint_inverse` will give you a hint on how to start the proof!
  left_inv := by
    sorry
    done
  right_inv := by
    sorry
    done

end Week

end TPwL_setoids_week_end_questions
