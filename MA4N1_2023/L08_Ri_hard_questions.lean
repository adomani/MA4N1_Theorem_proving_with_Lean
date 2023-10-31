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
  add_assoc     := by
    sorry
    done
  zero_add      := by
    sorry
    done
  add_zero      := by
    sorry
    done
  add_comm      := by
    sorry
    done
  left_distrib  := by
    sorry
    done
  right_distrib := by
    sorry
    done
  zero_mul      := by
    sorry
    done
  mul_zero      := by
    sorry
    done
  mul_assoc     := by
    sorry
    done
  one_mul       := by
    sorry
    done
  mul_one       := by
    sorry
    done
  add_left_neg  := by
    sorry
    done
  mul_comm      := by
    sorry
    done

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

--  Hint: you may find this lemma useful!
#check add_eq_zero_iff'

lemma add_square_eq_zero {a b : ℝ} (ha : a ^ 2 + b ^ 2 = 0) :
    a = 0 ∧ b = 0 := by
  sorry
  done

lemma add_square_ne_zero {a : Ri} (ha : a ≠ 0) :
    a.re ^ 2 + a.im ^ 2 ≠ 0 := by
  sorry
  done

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

end TPwL
