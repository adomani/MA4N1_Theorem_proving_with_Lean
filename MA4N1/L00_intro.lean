import Mathlib.Tactic

namespace TPwL_intro

#check Bool   -- Bool : Type

#check Prop   -- Prop : Type
#check Sort   -- Prop : Type

#check Type   -- Type : Type 1
#check Sort 1 -- Type : Type 1

#check Type 1 -- Type 1 : Type 2
#check Sort 2 -- Type 1 : Type 2
/-  and so on. -/

#check and  -- and (x y : Bool) : Bool
#check or   -- or  (x y : Bool) : Bool
#check And  -- And (x y : Prop) : Prop
#check Or   -- Or  (x y : Prop) : Prop

#check (· ∧ ·)  -- fun x x_1 ↦ x ∧ x_1 : Prop → Prop → Prop

/-  Easy template for a `lemma`

lemma name_of_lemma assumptions : statement := by
  tactics ...
  done

* `lemma` instructs Lean that we are stating a lemma,
* `name_of_lemma` assigns a name to the lemma that we are about to state,
* `assumptions` is a (finite) sequence, possibly empty, of statements like
  `(n : ℕ) {z : ℤ} (h : n + n = n + 1)`,
* `statement` is what we actually want to prove, e.g. `n = 1` or `∃ k : ℕ, n = 2 * k`
  or whatever we want to prove,
* `tactics` are the steps that we communicate to Lean to guide it through the proof.

If we do not want to re-use our result, then we may not want to even give it a name.
In that case, we can use `example`.
The syntax is similar to the one of `lemma`,
except that we begin with `example` and we cannot give it a name:

example assumptions : statement := by
  tactics ...
  done

_A comment about `done`_
Technically, writing `done` at the end of a proof is not needed.
However, since Lean does a fair amount of second-guessing about what you might be trying to say,
informing it explicitly where the proof should finish helps it to produce more meaningful error messages.
In turn, producing better error messages means that you will find it easier to find your mistakes!
-/

example (p q : Prop) (hpq : p ∧ q) : q ∧ p := by
  sorry
  ---- this lemma exists and `exact?` finds it for us
  --constructor  -- splits the `and` in the goal into two separate goals
  --· cases hpq  -- place the cursor at the end of `hpq`, wait for 💡 to appear and click on it!
  --  assumption
  --· sorry  -- left to you!
  done

example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  sorry
  --apply hpq
  --assumption
  done

example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  sorry
  --apply hqr
  --apply hpq
  --assumption
  ---- "alternative" proofs
  --apply hqr (hpq hp)
  --exact hqr (hpq hp)
  --solve_by_elim
  --exact?
  done

/-
Often, proof assistants make us aware of concepts that we were using unconsciously.
One of these may be the different role that *assumption* and *conclusions* play in a proof.
For instance, if one of your *assumptions* is `a + b = 0 ∧ a - b = 0`,
then we should have access to both statements `a + b = 0` and `a - b = 0`.
However, if our *conclusion* is `a + b = 0 ∧ a - b = 0`,
then, effectively, we have to prove two equalities
* `a + b = 0`, and
* `a - b = 0`.

You can think of the conjunction `and` among the *assumptions* as giving you two assumptions
within the same proof.
You can think of the conjunction `and` among the *conclusions* as requiring you two *separate*
proofs with the same assumptions.

Exercise.
What changes if we replace `and` for `or` in the previous discussion?

Consequently, the tactics that we use may be different, based on whether "similar looking"
statements are assumptions or conclusions.

For instance, when we have an `and` assumption, we can use the `cases` tactic.
When we have an `and` conclusion, we can use the `constructor` tactic.
-/

example {n : ℕ} (h : n + n = n + 1) : n = 1 := by
  sorry
  ---- this lemma (or rather a more general version of it) exists and `exact?` finds it for us
  --have := add_right_inj (G := ℕ)
  ---- apply this.mp  -- fails, try to understand the error!
  --apply (this ?_).mp
  ---- look at the state now
  --· exact h
  ---- where did the other goal go?
  done

lemma zero_eq_zero : 0 = 0 := by
  rfl
  done

lemma zero_ne_one : 0 ≠ 1 := by
  exact?
  done
