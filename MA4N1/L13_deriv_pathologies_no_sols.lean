import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace TPwL_deriv_pathologies_no_sols

/-!
#  Pathologies of `deriv`

This file shows some of the quirks and oddities appearing in `Lean/Mathlib`.

To get some practice, we use `deriv` and `derivWithin:
-/

#check deriv
#check derivWithin

/-- The real function that is `0` before `0` and `1` starting from `0`. -/
noncomputable
def step (r : ℝ) : ℝ := if r < 0 then 0 else 1

/-!
As mentioned in the lecture, we are going to show that the derivative of the
function `step` is identically `0`.
This exploits the "pathological" definition of setting to `0` the `deriv`ative
at `p` of a function that is not differentiable at `p`.

Due to how the function `step` is defined, you may find it convenient to use
that it is constant on `{x : ℝ | x < 0}` and also on `{x : ℝ | x < 0}`.

You may want to use that the derivative of a *globally* constant function
coincides with the derivative of `step` on an appropriate open set.
Lemmas that relate values of possibly different functions at certain arguments
are typically referred to as "congruence" lemmas.
In this case, you may look at `derivWithin_congr`.
-/

-- useful lemmas: `derivWithin_of_isOpen, deriv_const, derivWithin_congr`
theorem derivWithin_step_of_neg {r : ℝ} (h0 : r < 0) :
    derivWithin step {x | x ≠ 0} r = 0 := by
  sorry
  done

-- copy-paste the previous proof and fix?
theorem derivWithin_step_of_pos {r : ℝ} (h0 : 0 < r) :
    derivWithin step {x | x ≠ 0} r = 0 := by
  sorry
  done

-- tactic `by_cases` and then use the previous results.
theorem derivWithin_step_of_ne_zero {r : ℝ} (h0 : r ≠ 0) :
    derivWithin step {x | x ≠ 0} r = 0 := by
  sorry
  done

-- Use that `{x : ℝ | x ≠ 0}` is open.
theorem deriv_step_of_ne_zero {r : ℝ} (h0 : r ≠ 0) :
    deriv step r = 0 := by
  sorry
  done

-- funny consequence of the pathologies: `IsLocalMax.deriv_eq_zero`
-- also useful `IsMaxOn.isLocalMax`
theorem deriv_step_zero : deriv step 0 = 0 := by
  sorry
  done

--  `eq_or_ne` may be useful here
example : deriv step = 0 := by
  sorry
  done

end TPwL_deriv_pathologies_no_sols
