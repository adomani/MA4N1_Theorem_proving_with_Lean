import Mathlib.Tactic

namespace TPwL_Ri_easy_questions

/-!

#  Defining the complex numbers

In this exercise sheet, you will prove that the complex numbers form a field.

Some parts of the argument are tricky: I will give *very* few spoilers to begin with,
so that you have a chance to try it out for yourself.
However, if you want to have some hints, do skip ahead, since there are lots of pointers below!

##  The setup

We define our version of the complex numbers, and we call it `Ri` (i.e. `ℝ` with `i`).
Thus, `Ri` is simply a pair of real numbers, like `point` from the lectures.
-/

@[ext]  -- notice the `ext` attribute: we've taken this onboard!
structure Ri : Type where
  re : ℝ    -- we suggestively called the two fields `re` and `im`,
  im : ℝ    -- to convey our expectation.

/-!
We are going to define the "data" fields of a `Field` before we prove that `Ri` is a field.
While this is not strictly necessary, it turns out to be a *huge* advantage to have the
definitions before-hand: this is related to some of the spoilers for this file!

In fact, we begin by showing that `Ri` is a `CommRing`, leaving the proof that it is a field for later.
Thus, we define `Add`, `Mul`, `Zero`, `One` and `Neg`.
-/

instance : Add Ri  where add a b := ⟨a.re + b.re, a.im + b.im⟩
instance : Mul Ri  where mul a b := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
instance : Neg Ri  where neg a   := ⟨- a.re, -a.im⟩
instance : Zero Ri where zero    := ⟨0, 0⟩
instance : One Ri  where one     := ⟨1, 0⟩

/-!
The following 10 lemmas have virtually no mathematical context and their proof is `rfl`:
this is Lean's way of saying that they follow from the definitions in a very strong sense.

However, stating them and giving them the `simp` tag means that Lean will apply them
whenever we call `simp`: if you tried proving that `Ri` is a `CommRing` without seeing these
lemmas, you will notice a great difference before and after!
-/
@[simp] lemma re_add {a b : Ri} : (a + b).re = a.re + b.re := rfl
@[simp] lemma im_add {a b : Ri} : (a + b).im = a.im + b.im := rfl

@[simp] lemma re_mul {a b : Ri} : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] lemma im_mul {a b : Ri} : (a * b).im = a.re * b.im + a.im * b.re := rfl

@[simp] lemma re_neg {a : Ri} : (- a).re = - a.re := rfl
@[simp] lemma im_neg {a : Ri} : (- a).im = - a.im := rfl

@[simp] lemma re_zero : (0 : Ri).re = 0 := rfl
@[simp] lemma im_zero : (0 : Ri).im = 0 := rfl

@[simp] lemma re_one : (1 : Ri).re = 1 := rfl
@[simp] lemma im_one : (1 : Ri).im = 0 := rfl

/-!
We are now ready to prove that `Ri` is a `CommRing`.

The "data" fields
* `add  := (· + ·)`
* `mul  := (· * ·)`
* `neg  := (- ·)`
* `zero := 0`
* `one  := 1`

have already been provided above, so we no longer need to give them here.
-/
instance : CommRing Ri where
  add_assoc     := by sorry
  zero_add      := by sorry
  add_zero      := by sorry
  add_comm      := by sorry
  left_distrib  := by sorry
  right_distrib := by sorry
  zero_mul      := by sorry
  mul_zero      := by sorry
  mul_assoc     := by sorry
  one_mul       := by sorry
  mul_one       := by sorry
  add_left_neg  := by sorry
  mul_comm      := by sorry

/-!

##  Dealing with inverses

Now that we proved that `Ri` is a `CommRing`, let's conclude by showing that it is in fact a `Field`!

As before, we provide the only remaining "data" field, `Inv`, separately.
Notice that Lean wants us to label `Inv` as `noncomputable`.
This is not a big deal: we want to prove theorems about `Ri`, not "computing" anything with it!
(If you are curious, comment out `noncomputable` to see what Lean says:
ultimately, the "noncomputability" is a consequence of the fact that the real numbers are non-computable.
This only means that there is no algorithm to decide if two real numbers are equal or not -- hardly surprising!)
-/

noncomputable
instance : Inv Ri where
  inv a := ⟨a.re / (a.re ^ 2 + a.im ^ 2), - a.im / (a.re ^ 2 + a.im ^ 2)⟩

/-!
We learned our lesson: let's prove our silly `rfl` lemmas about `Inv.inv`.
-/

@[simp] lemma re_inv {a : Ri} : (a⁻¹).re =   a.re / (a.re ^ 2 + a.im ^ 2) := rfl
@[simp] lemma im_inv {a : Ri} : (a⁻¹).im = - a.im / (a.re ^ 2 + a.im ^ 2) := rfl

--  Hint: you may find this lemma useful!
#check add_eq_zero_iff'

lemma add_square_eq_zero {a b : ℝ} (ha : a ^ 2 + b ^ 2 = 0) :
    a = 0 ∧ b = 0 := by
  sorry
  done

/-!
Here you may find the tactic `contrapose!` useful!
Read the documentation below to see what it does, in case it is not clear from the name!
-/

#help tactic contrapose

lemma add_square_ne_zero {a : Ri} (ha : a ≠ 0) :
    a.re ^ 2 + a.im ^ 2 ≠ 0 := by
  sorry
  done

/-!
Hint: there is a tactic that I have not yet mentioned, but that I found useful for proving this instance.
The tactic is called `apply_fun` (see below for the documentation of the tactic).
The way in which I used it, is to generate an equality between the real parts of two equal real numbers.
The real numbers in question were equal "by contradiction" and `apply_fun` allowed me to exploit
results about the real numbers to close a goal.
-/

#help tactic apply_fun

noncomputable
instance : Field Ri where
  exists_pair_ne := by
    sorry
    done
  mul_inv_cancel a ha := by
    sorry
    done
  inv_zero := by
    sorry
    done

end TPwL_Ri_easy_questions
