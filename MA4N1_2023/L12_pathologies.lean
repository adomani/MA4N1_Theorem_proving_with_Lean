import Mathlib.Tactic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace TPwL

/-!
#  Pathologies

This file shows some of the quirks and oddities appearing in `Lean/Mathlib`.

## Every function is "total"

What this means is that you are not allowed to leave a function undefined on
some (non-empty) subset of its domain.

Of course, you could imagine that you simply make sure that the domain of every function
is exactly the subset where your function makes sense.
While this is in theory possible, it is often better to work on the whole "natural" domain
and simply return (carefully chosen) arbitrary values on inputs where you would normally
not define your function.

Here are some simple examples.
-/

#eval 0 - 1
example : 0 - 1 = 0 := by exact rfl
/-!
Lean happily tells us that `0 - 1` equals `0`.
-/

#eval (1 : ℚ) / 0
example : (1 : ℚ) / 0 = 0 := by exact div_zero 1
/-!
Lean is just happily telling us that
* division by zero is correct;
* and that `1 / 0` has value `0`, in fact.
-/

example {q : ℚ} : q / 0 = 0 := by
  exact div_zero q
  done

/-
First, let's see a "high-level" explanation:
* we want to define `(· / ·) : ℚ → ℚ → ℚ`;
* we know what to do when the second input is non-zero;
* in set-theory, we simply say "let's not define division when the denominator is `0`".

A more "low-level" explanation is that

**there is a cost to every definition that you make.**

Thus, if you want the denominator input to your division function to be non-zero,
you are going to have to roll your sleeves up and define the "Type of non-zero rational numbers".
After you have defined this Type, you will have to start proving some theorems about it --
these theorems will likely be complete trivialities, but you will have to devote time to doing that.
You will also have to relate "non-zero rational numbers" to "rational numbers that could be zero".

Of course, this is something that *can* be done, and you can certainly find situations in `Mathlib`
where this is the preferred route.

However, there are also other situations where it is simply much more convenient to work with
`junk values`: you define your function everywhere, trying to make your life simpler.
Naturally, for the results that are "really" interesting, some extra assumption will show up.
Nevertheless, as a rule of thumb, the more you can hold on making these assumptions,
the easier it will be to use your results, because you will not have to provide these assumptions
every time you use your lemmas.
-/

--  The `Std` division on `ℚ`.
example : (2 : ℚ) / 1 = 2 := by
  exact div_one 2
  done

--  Let's roll our own

/-- `myDiv p q h` is the result of division of `p` by `q` with the assumption `h` that `q` is non-zero. -/
def myDiv (p q : ℚ) (h : q ≠ 0) : ℚ := p / q


/--
error: failed to synthesize instance
  OfNat (1 ≠ 0 → ℚ) 2
---
error: unsolved goals
⊢ myDiv 2 1 = 2-/
#guard_msgs in
example : myDiv 2 1 = 2 := by
  done

example : myDiv 2 1 (by exact one_ne_zero) = 2 := by
  unfold myDiv
  exact div_one 2
  done

example : (1 : ℚ) / 2 + 1 / 2 = 1 := by
  exact add_halves 1
  done

example : myDiv 1 2 (by exact two_ne_zero) + myDiv 1 2 (by exact two_ne_zero) = 1 := by
  unfold myDiv
  exact add_halves 1
  done

/--
error: unsolved goals
⊢ 0 ≠ 0
---
error: unsolved goals
⊢ myDiv 1 0 (_ : 0 ≠ 0) = 0
-/
#guard_msgs in
example : myDiv 1 0 (by
  _
) = 0 := by
  done

-- Finally, an example of a result where you cannot get away with the expected non-zero assumption

/--
error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.
-/
#guard_msgs in
example {q : ℚ} : q / q = 1 := by exact?
-- `exact?` does not find this result.
-- For a good reason: it is not true!
example : (0 : ℚ) / 0 = 0 := by exact?

-- So, let's try again!
--[fill in your guess!]

/-!
# Conclusion

It is important to know how everything is defined!

Lean will help checking that what you formalised is correct.
It will not check that what you formalised agrees with your intuitive idea!

However, with Lean it is extremely easy to recurse into every definition and see how every
object is defined from "first principles".
In "informal" maths, this is not always straightforward, not only because you may not have access
to some sources, but also because
* sometimes/often definitions can be context-dependent,
* there may be conflicting conventions in the literature,
* there may be implicit assumptions that may not be clear to someone who is just starting,
* ...

These are some of the reasons why formalization is useful!
-/

noncomputable
def step (r : ℝ) : ℝ := if r < 0 then 0 else 1

#check deriv

--  The proof of this example appears in the file for the support class for Week 7
example : deriv step = 0 := by
  sorry
  done

end TPwL
