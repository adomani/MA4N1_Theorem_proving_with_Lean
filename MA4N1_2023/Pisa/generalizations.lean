import Mathlib.Tactic

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

theorem my_induction
    (P_zero  : P 0)
    (P_add   : ∀ p q, P p → P q → P (p + q))
    (P_X_pow : ∀ n : ℕ, P (X ^ n)) :
    P f := by
  refine Polynomial.induction_on' f ?_ ?_
  · exact P_add
  · intros n a
    simp [← C_mul_X_pow_eq_monomial]  -- replace `monomial n a` with `a * X ^ n`
    -- proceed by induction on `a`
    induction a with
    | zero => simp [P_zero]
    | succ a ha =>
      simp [add_mul]
      apply P_add _ _ ha (P_X_pow _)
  done

example : Monotone (fun n ↦ f.eval n) :=
by
  apply my_induction f _
  -- verify assumption `P_zero`
  · simp [monotone_const]
  -- verify assumption `P_add`
  · intros f g hf hg
    convert Monotone.add hf hg
    simp
  -- verify assumption `P_X_pow`
  · intro n
    simp
    apply Monotone.pow_right
    apply monotone_id
  done

end Nat

/-
Now that we proved it for `ℕ`, let's generalize to `ℝ≥0`.

Copy-paste the above, change `ℕ` to `ℝ≥0` and fix the issues.
-/
namespace nnreal

end nnreal

#lint

/-
Now that we proved it for `ℕ` and for `ℝ≥0`, let's generalize further.

Copy-paste the above and look for a common generalization of `ℕ` and `ℝ≥0`.
-/

namespace next

--  -->  Semiring --> Comm --> Ordered --> Canonically

end next

/-
Finally, let's confirm that the more general result proves to the special cases that we know.
-/

example (f : ℕ[X]) : Monotone (fun n ↦ f.eval n) :=
by
  sorry
  done

example (f : ℝ≥0[X]) : Monotone (fun n ↦ f.eval n) :=
by
  sorry
  done


end Pisa
