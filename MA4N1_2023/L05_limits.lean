import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic

namespace TPwL

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
  use n + 1
  exact?
  done

example {a : ℝ} : limit (fun n => a) a := by
  unfold limit
  intros ε h
  use 0
  simp [h]
  done

--  Hint: on an existential `H : ∃ x, P x`, the tactic `cases H` gives you access to an `x` and
--  the fact that it satisfies the proposition `P`.
--  Remember to wait for the lightbulb to fill in the syntax for `cases`!
--  Also, keep in mind that you have a "hidden" `∃` in the local context.
example {a b : ℝ} (f : ℕ → ℝ) (h : limit f a) : limit (fun n => f n + b) (a + b) := by
  unfold limit
  intros ε hε
  cases h ε hε with
  | intro N h1 =>
    use N
    intro n Nn
    norm_num
    apply h1 _ Nn
  done

--  Hint: check what `half_pos` is!
example {a b : ℝ} (f g : ℕ → ℝ) (hf : limit f a) (hg : limit g b) :
    limit (fun n => f n + g n) (a + b) := by
  unfold limit
  intros ε hε
  cases hf (ε / 2) (half_pos hε) with
  | intro M h1 =>
    cases hg (ε / 2) (half_pos hε) with
    | intro N h2 =>
      use max M N
      intro n MNn
      dsimp
      rw [add_sub_add_comm]
      apply lt_of_le_of_lt (abs_add (f n - a) (g n - b))
      refine lt_of_lt_of_le (add_lt_add (h1 n ?_) (h2 n ?_)) ?_
      · exact le_of_max_le_left MNn   -- `exact?` works
      · exact le_of_max_le_right MNn  -- `exact?` works
      · norm_num
  done

/-
What follows can be *very* challenging: do not despair if you get stuck!

In the proposed solution, I used
* `Int.natAbs`, a function that takes an integer and returns its absolute value as a natural number;
* `Int.floor`, a function that takes a real number and returns its floor as an integer number;
* `le_trans`, a propositon that takes the proof of two inequalities of the form `a ≤ b` and `b ≤ c`
  as input and returns a proof of the inequality `a ≤ c`;

and various other tricks, including
* `LT.lt.le` converting a strict inequality `a < b` into a weak one `a ≤ b`;
* explicitly using double type-ascriptions to layer the steps in going from `ℕ`, to `ℤ`, to `ℝ`;
* ...

Part of the challenge is for you to find a much simpler proof of `no_limit_id` than the one that I propose!
-/

lemma aux1 (n : ℤ) : n ≤ Int.natAbs n := by
  exact?
  done

lemma aux (a : ℝ) : -1 ≤ (Int.natAbs ⌊a⌋) - a := by
  rw [neg_le_sub_iff_le_add]
  apply le_trans (b := (⌊a⌋ : ℝ) + 1)
  · apply (Int.lt_floor_add_one a).le
  · simp
    apply le_trans (b := (⌊a⌋ : ℝ))
    · exact Eq.le rfl
    · have := aux1 ⌊a⌋
      have : ⌊a⌋ ≤ ((Int.natAbs ⌊a⌋ : ℤ) : ℝ) := by
        exact?
      exact this
  done

lemma no_limit_id {a : ℝ} : ¬ limit (fun n => n) a := by
  unfold limit
  simp only [gt_iff_lt, not_forall, not_exists, not_lt, exists_prop]
  use 1
  simp
  intro n
  use (FloorRing.floor a).natAbs + 2 + n
  norm_num
  rw [← neg_add_eq_sub, ← add_assoc, ← add_assoc, neg_add_eq_sub]
  rw [le_abs]
  apply Or.inl
  have : (-1 : ℝ) + 2 + 0 ≤ ↑(Int.natAbs ⌊a⌋) - a + 2 + ↑n := by
    apply add_le_add
    · apply add_le_add
      · exact aux a
      · exact Eq.le rfl        -- `exact?` finds this
    · exact Nat.cast_nonneg n  -- `exact?` finds this
  norm_num at this
  assumption
  done

end TPwL
