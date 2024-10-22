import Mathlib.Tactic

#allow_unused_tactic Lean.Parser.Tactic.done

namespace Pisa

open Function Polynomial NNReal

namespace Nat

/-
#  Generalizations, automation, `exact?`, `simp`, tactics

As it happens, someone comes along and says:

"I just learned a cool fact!  A polynomial with coefficients in `ℕ` is monotone!"

Let's formalize this result!

Let's also think about what it really means...

Surely they intended to say that viewing a polynomial with coefficients in `ℕ`
as a function `ℕ → ℕ`, we obtain a monotone function.
-/

variable  (f : ℕ[X])        -- `f` is a polynomial with coefficients in `ℕ`
          (P : ℕ[X] → Prop) -- `P` is a property of polynomials: `P f` may be
                            -- true or false

example : Monotone (fun n ↦ f.eval n) := by
  refine Polynomial.induction_on' f ?_ ?_
  · intros f g hf hg
    simp only [eval_add]
    exact? says exact Monotone.add hf hg
  · intros n a x y xy
    simp only [eval_monomial]
    gcongr
  done

end Nat

/-
Now that we proved it for `ℕ`, let's generalize to `ℝ≥0`.

Copy-paste the above, change `ℕ` to `ℝ≥0` and fix the issues.
-/
namespace nnreal

variable  (f : ℝ≥0[X])        -- `f` is a polynomial with coefficients in `ℝ≥0`
          (P : ℝ≥0[X] → Prop) -- `P` is a property of polynomials: `P f` may be
                            -- true or false

end nnreal

/-!
What happens if we copy-paste the above and change `ℕ` to `ℝ`?
-/
namespace real

variable  (f : ℝ[X])        -- `f` is a polynomial with coefficients in `ℝ`
          (P : ℝ[X] → Prop) -- `P` is a property of polynomials: `P f` may be
                            -- true or false

end real

/-!
How can we further generalize this?
-/
namespace general

variable {R} [Semiring R]
variable  (f : R[X])        -- `f` is a polynomial with coefficients in `R`
          (P : R[X] → Prop) -- `P` is a property of polynomials: `P f` may be
                            -- true or false

end general

/-
Finally, let's confirm that the more general result proves to the special cases that we know.
-/

example (f : ℕ[X]) : Monotone (fun n ↦ f.eval n) := by
  sorry
  done

example (f : ℝ≥0[X]) : Monotone (fun n ↦ f.eval n) := by
  sorry
  done

--  -->  Semiring --> Comm --> Ordered --> Canonically

end Pisa
