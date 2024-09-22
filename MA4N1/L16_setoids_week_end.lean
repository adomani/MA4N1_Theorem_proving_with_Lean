import Batteries.Tactic.Lemma
import Mathlib.Tactic
import MA4N1.help_me

#allow_unused_tactic Lean.Parser.Tactic.done

namespace TPwL_setoids_week_end

/-!
#  `Setoid`s and equivalence relations
-/

--  A left-over lemma from the lecture on Tuesday
lemma two_dvd_sub_one_iff (d : ℤ) : 2 ∣ d - 1 ↔ ¬ 2 ∣ d := by
  constructor <;> intro h
  · omega
  · omega
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
    constructor
    · exact? says exact fun x => rfl
    · exact? says exact fun {x y} a => id a.symm
    · intros x y z xy yz
      exact xy.trans yz
    done

--  If you like an equivalent but more obfuscated version of the instance above, here it is!
/-
instance : Setoid Week where
  r := (week_end? · = week_end? ·)
  iseqv := { refl  := fun _ => rfl
             symm  := fun {_ _} => .symm
             trans := fun {_ _ _} => .trans }
-/

namespace Week

@[simp]
lemma sat_sun : (⟦Sat⟧ : Quotient Week_setoid) = ⟦Sun⟧ := by
  exact Quotient.eq.mpr rfl
  done

example : (⟦Sat⟧ : Quotient Week_setoid) ≠ ⟦Mon⟧ := by
  intro h
  simp only [Quotient.eq] at h
  cases h
  done

example : (⟦Sat⟧ : Quotient Week_setoid) ≠ ⟦Mon⟧ := by
  simp only [ne_eq, Quotient.eq]
  rintro ⟨⟩
  done

lemma equiv_class_of_Sunday (d : Week) : (⟦Sun⟧ : Quotient Week_setoid) = ⟦d⟧ ↔
    d ∈ ({Sat, Sun} : Set _) := by
  -- `rcases d with _ | _ | _ | _ | _ | _ | _ <;>` also works instead of `induction`
  induction d <;>
    simp <;>
    rintro ⟨⟩
  done

lemma equiv_class_of_Monday (d : Week) : (⟦Mon⟧ : Quotient Week_setoid) = ⟦d⟧ ↔
    d ∈ ({Mon, Tue, Wed, Thu, Fri} : Set _) := by
  -- `rcases d with _ | _ | _ | _ | _ | _ | _ <;>` also works instead of `induction`
  induction d <;>
    simp <;>
    (try rfl) <;>
    rintro ⟨⟩
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
    rintro ⟨d⟩
    dsimp only
    split_ifs with h
    · apply d.equiv_class_of_Sunday.mpr
      induction d <;> cases h <;> simp
    · simp only [Bool.not_eq_true] at h
      apply d.equiv_class_of_Monday.mpr
      induction d <;> cases h <;> simp
    done
  right_inv := by
    rintro (x|x) -- split into `true`/`false`
    · simp [week_end?]
    · simp [week_end?]
    done

end Week

end TPwL_setoids_week_end
