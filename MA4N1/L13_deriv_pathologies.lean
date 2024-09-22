import Mathlib.Analysis.Calculus.LocalExtr.Basic

#allow_unused_tactic Lean.Parser.Tactic.«done»

namespace TPwL_deriv_pathologies

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
  have : derivWithin (fun _ : ℝ => (0 : ℝ)) {x | x < 0} r = 0 := by
    rw [derivWithin_of_isOpen]
    · exact deriv_const r 0
    · exact isOpen_Iio
    · exact h0
  conv_rhs => rw [← this]
  rw [derivWithin_of_isOpen, ← derivWithin_of_isOpen (s := {x : ℝ | x < 0})]
  · unfold step
    rw [derivWithin_congr]
    · intros x hx
      aesop
    · aesop
  · exact isOpen_gt' 0
  · exact h0
  · exact isOpen_ne
  · exact h0.ne
  done

-- copy-paste the previous proof and fix?
theorem derivWithin_step_of_pos {r : ℝ} (h0 : 0 < r) :
    derivWithin step {x | x ≠ 0} r = 0 := by
  have : derivWithin (fun _ : ℝ => (1 : ℝ)) {x | 0 < x} r = 0 := by
    rw [derivWithin_of_isOpen]
    · exact deriv_const r 1
    · exact isOpen_Ioi
    · exact h0
  conv_rhs => rw [← this]
  rw [derivWithin_of_isOpen, ← derivWithin_of_isOpen (s := {x : ℝ | 0 < x})]
  · unfold step
    rw [derivWithin_congr]
    · intros x hx
      simp_all
      linarith -- overkill, `exact hx.le` would have sufficed
    · simp only [ite_eq_right_iff, zero_ne_one]
      intro c
      linarith
  · exact isOpen_lt' 0
  · exact h0
  · exact isOpen_ne
  · exact h0.ne'
  done

-- tactic `by_cases` and then use the previous results.
theorem derivWithin_step_of_ne_zero {r : ℝ} (h0 : r ≠ 0) :
    derivWithin step {x | x ≠ 0} r = 0 := by
  by_cases r0 : r < 0
  · exact derivWithin_step_of_neg r0
  · apply derivWithin_step_of_pos
    -- the following was the first result of `apply?`
    refine lt_of_le_of_ne' ?_ h0
    exact? says exact not_lt.mp r0
  done

-- Use that `{x : ℝ | x ≠ 0}` is open.
theorem deriv_step_of_ne_zero {r : ℝ} (h0 : r ≠ 0) :
    deriv step r = 0 := by
  rw [← derivWithin_of_isOpen (s := {x | x ≠ 0})]
  · exact? says exact derivWithin_step_of_ne_zero h0
  · exact? says exact isOpen_ne
  · exact? says exact h0
  done

-- funny consequence of the pathologies: `IsLocalMax.deriv_eq_zero`
-- also useful `IsMaxOn.isLocalMax`
theorem deriv_step_zero : deriv step 0 = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply IsMaxOn.isLocalMax (s := Set.univ)
  · intros x _
    unfold step
    aesop
  · simp
  done

--  `eq_or_ne` may be useful here
example : deriv step = 0 := by
  ext r
  simp only [Pi.zero_apply]
  rcases eq_or_ne r 0 with rfl | h0
  · exact? says exact deriv_step_zero
  · exact? says exact deriv_step_of_ne_zero h0
  done

end TPwL_deriv_pathologies
