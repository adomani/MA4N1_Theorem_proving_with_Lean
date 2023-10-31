import Mathlib.Tactic

/-!

#  Performing calculations in Lean

Very likely, you will find yourself having to perform some calculation while working on your project.
Here we go over some of the tools and tactics available to support this part of the proof.

##  `calc` blocks

The first tool that we introduce is `calc`.
This usually creates very readable code for chaining together long sequences of
* equalities (`=`);
* weak inequalities weak (`≤`);
* strict inequalities (`<`);
* and more!

First, let's see the syntax.
If the goal has the shape `a ≤ b` (or also `a < b` or `a = b`), then we can write
```lean
calc a ≤ c := by sorry
     c ≤ d := by sorry
     ...
     z ≤ b := by sorry
```
and Lean will chain the proofs together for us.
The syntax is a little fiddly and it may take a little time to get used to.
Here are some pointers.
* Unless your expressions are very short, I suggest leaving `calc` on the previous line and
  beginning the following line with `a ≤ c := ...`.
* If all LHS begin with the same indentation, then you are good!
* Most of the times, you do not need to repeat the LHS, since Lean will know that it is the same
  as the previous RHS.
* Most of the times, you can leave out the final RHS, since Lean will assume that it is the final term.

The "most of the times" above may really not apply in certain situations!

Let's begin with some simple examples.
-/

--  First, one to get the syntax working.
example : 0 < 10 := by calc
  _ < 1     := by norm_num
  _ ≤ 2     := by norm_num  -- indent me more or less to see an error message
  _ = 1 + 1 := by norm_num
  _ ≤ 10    := by norm_num

--  annoying: can we use `calc`?
example {n : ℕ} {x : ℝ} (h : 1 ≤ x) : n ≤ n * x := by
  rw [← mul_one n]
  sorry
  done

--  `calc` can help dealing with "casts"
example : (1 : ℝ) ≤ 3 := by
  sorry
  done

--  you can nest the uses of `calc`
example {n : ℕ} {x : ℝ} (h : 1 ≤ x) : n + 1 ≤ n * x + 3 := by calc
  (_ : ℝ) ≤ n * 1 + 1 := by rw [mul_one]
  _ ≤ n * x + 1 := add_le_add_right (mul_le_mul rfl.le h zero_le_one n.cast_nonneg) ..
  _ ≤ _ := by
    apply add_le_add_left
    calc
      (1 : ℝ) = ((1 : ℕ) : ℝ) := by exact Nat.cast_one.symm
      _ ≤ ((3 : ℕ) : ℝ) := by refine Nat.cast_le.mpr ?_; exact Nat.le_three_of_sqrt_eq_one rfl
      _ ≤ _ := by exact Eq.le rfl

--  try replacing the `<` by `≤` or doing other changes and see how Lean reacts.
example : (0 : ℝ) < 10 := by calc
  (_ : ℝ) < 1 := by norm_num
  _ ≤ 2       := by norm_num
  _ = 1 + 1   := by norm_num
  _ ≤ 10      := by norm_num
