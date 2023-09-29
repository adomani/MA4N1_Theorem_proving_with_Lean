import Mathlib.Tactic

/-!
#  Pathologies

This file shows some of the quirks and oddities used in `Lean/Mathlib`.

## Every function is "total"

What this means is that you are not allowed to leave a function undefined on
some (non-empty) subset of its domain.

Of course, you could imagine that you simply make sure that the domain of every function
is exactly the subset where your function makes sense.
While this is in theory possible, it is often better to work on the whole "natural" domain and
simply return arbitrary values on inputs where you would normally not define your function.

Here are some simple examples.
-/

#eval 0 - 1
example : 0 - 1 = 0 := by exact rfl

#eval (1 : ℚ) / 0
example : (1 : ℚ) / 0 = 0 := by exact div_zero 1
/-
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
-/

def myDiv (p q : ℚ) (h : q ≠ 0) : ℚ := p / q

example : (2 : ℚ) / 1 = 2 := by
  exact div_one 2
  done

example : myDiv 2 1 = 2 := by
  done

example : myDiv 2 1 (by exact one_ne_zero) = 2 := by
  unfold myDiv
  exact div_one 2
  done

example : (1 : ℚ) / 2 + 1 / 2 = 1 := by
  exact add_halves 1

example : myDiv 1 2 (by exact two_ne_zero) + myDiv 1 2 (by exact two_ne_zero) = 1 := by
  simp only [myDiv]
  exact add_halves 1

example : myDiv 1 0 (by
  _
) = 0 := by
  done
