import Mathlib.Tactic

namespace TPwL

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

macro "solve" : tactic => `(tactic| intros <;> ext <;> try ( simp <;> ring ; done ))

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
  add_assoc     := by solve
  zero_add      := by solve
  add_zero      := by solve
  add_comm      := by solve
  left_distrib  := by solve
  right_distrib := by solve
  zero_mul      := by solve
  mul_zero      := by solve
  mul_assoc     := by solve
  one_mul       := by solve
  mul_one       := by solve
  add_left_neg  := by solve
  mul_comm      := by solve

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
  --  `rwa` means "try `assumption` after the rewrite"
  rwa [← sq_eq_zero_iff, ← sq_eq_zero_iff (a := b), ← add_eq_zero_iff'] <;>
  exact sq_nonneg _
  done

lemma add_square_ne_zero {a : Ri} (ha : a ≠ 0) :
    a.re ^ 2 + a.im ^ 2 ≠ 0 := by
  contrapose! ha
  ext
  · exact (add_square_eq_zero ha).left
  · exact (add_square_eq_zero ha).right
  done

noncomputable
instance : Field Ri where
  exists_pair_ne := by
    use 0
    use 1
    intro h
    apply_fun Ri.re at h
    simp? at h says simp only [re_zero, re_one, zero_ne_one] at h
    done
  mul_inv_cancel a ha := by
    ext
    · simp? says simp only [re_mul, re_inv, im_inv, re_one]
      rw [← mul_div_assoc, ← mul_div_assoc, div_sub_div, div_eq_one_iff_eq]
      · ring
      all_goals
      · simp? says simp only [ne_eq, mul_eq_zero, or_self]
        exact add_square_ne_zero ha
    · simp
      rw [← mul_div_assoc, ← mul_div_assoc, div_add_div, div_eq_zero_iff]
      · ring_nf; simp
      all_goals exact add_square_ne_zero ha
    done
  inv_zero := by solve

end TPwL
