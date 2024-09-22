import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Archimedean

#allow_unused_tactic Lean.Parser.Tactic.«done»

namespace TPwL_limits_no_sols

/-!
#  Continuity in `Mathlib`

As I mentioned in the lectures, continuity and limits are defined in a way
that differs quite a bit to what you might be used.
This is done via `filter`s.

Nevertheless, the "standard" definition of continuity is available in `Mathlib`
and we will use the standard one, not the one using filters.

First, in case you are curious, `Filter.Tendsto` is `Mathlib`s way of talking about limits.
-/
#check Filter.Tendsto
/-!
Moving on, let's roll out our "standard" definition.
-/

/-- The limit of a sequence of real numbers. -/
def limit (f : ℕ → ℝ) (a : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |f n - a| < ε

/-!
Note that there is an existential (`∃`) in the definition of a limit.
To provide a witness of the existential, you can use the tactic `use`.

Here is an example of the `use` tactic.
Use ``use [your choice of a natural number bigger than `n`]``!
-/
example {n : ℕ} : ∃ m, n < m := by
  sorry
  done

example {a : ℝ} : limit (fun n => a) a := by
  sorry
  done

--  Hint: on an existential `H : ∃ x, P x`, the tactic `cases H` gives you access to an `x` and
--  the fact that it satisfies the proposition `P`.
--  Remember to wait for the lightbulb to fill in the syntax for `cases`!
--  Also, keep in mind that you have a "hidden" `∃` in the local context.
example {a b : ℝ} (f : ℕ → ℝ) (h : limit f a) : limit (fun n => f n + b) (a + b) := by
  sorry
  done

--  Hint: check what `half_pos` is!
example {a b : ℝ} (f g : ℕ → ℝ) (hf : limit f a) (hg : limit g b) :
    limit (fun n => f n + g n) (a + b) := by
  sorry
  done

/-
What follows can be *very* challenging: do not despair if you get stuck!

In the proposed solution, I used
* `Int.natAbs`, a function that takes an integer and returns its absolute value as a natural number;
* `Int.floor`, a function that takes a real number and returns its floor as an integer number;
* `le_trans`, a proposition that takes the proof of two inequalities of the form `a ≤ b` and `b ≤ c`
  as input and returns a proof of the inequality `a ≤ c`;

and various other tricks, including
* `LT.lt.le` converting a strict inequality `a < b` into a weak one `a ≤ b`;
* explicitly using double type-ascriptions to layer the steps in going from `ℕ`, to `ℤ`, to `ℝ`;
* ...

Part of the challenge is for you to find a much simpler proof of `no_limit_id` than the one that I propose!
-/

lemma aux1 (n : ℤ) : n ≤ Int.natAbs n := by
  sorry
  done

lemma aux (a : ℝ) : -1 ≤ (Int.natAbs ⌊a⌋) - a := by
  sorry
  done

lemma no_limit_id {a : ℝ} : ¬ limit (fun n => n) a := by
  sorry
  done

end TPwL_limits_no_sols
