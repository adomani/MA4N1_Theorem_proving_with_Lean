import Mathlib.Tactic

namespace TPwL

/-!
First, we begin with a warm-up working with divisors.
The symbol for "divides" is `∣`, that is `\mid`.
The symbol for "such that" that appears in the definition of a set is `|` -- they look the same, but are not the same!
In general, you can hover over any symbol and you should get information about how to type it.

In the following example, the tactic `interval_cases` can be useful.
If `a` is a variable in context, then calling `interval_cases a` looks for upper and lower bounds for `a` and
returns a goal for each possible value of `a`.
Note that if `a : ℕ`, then the lower bound of `0` is always available,
so you only need to have in context an upper bound of the form `a ≤ [some number]`.
However, if there is a better lower bound than `0`, then `interval_cases a` will use it.

You can take a look at the documentation for `interval_cases here:
-/
#help tactic interval_cases

/-!
Another tactic that might be useful is `simp_all`.
This tactic essentially applies `simp` everywhere recursively, until it makes no further progress.
-/
#help tactic simp_all

/-
Finally, remember the `ext` tactic: to show that certain equalities hold,
it suffices to show that the two sides have the same elements.
You can also use `ext a` to name the "common" element that the tactic extracts.
-/

example : {a : ℕ | a ∣ 6} = {1, 2, 3, 6} := by
  ext a
  simp
  constructor <;> intros h
  · have : a ≤ 6 := by
      apply Nat.le_of_dvd
      · exact Nat.succ_pos 5
      · exact h
    interval_cases a <;> simp_all
    done
  · cases h with
      | inl h =>
        simp_all
      | inr h =>
        cases h with
          | inl h =>
            simp_all
          | inr h =>
            cases h with
              | inl h =>
                simp_all
              | inr h =>
                cases h with
                  | refl => rfl
  done

/-!
The proof above probably looks more complicated than it "should".
Even compressing it a little, it feels clunky:
-/

example : {a : ℕ | a ∣ 6} = {1, 2, 3, 6} := Set.ext
  (⟨fun h => have := Nat.le_of_dvd (Nat.succ_pos 5) h; by interval_cases · <;> simp_all,
    fun h => by rcases h with rfl | rfl | rfl | rfl <;> simp_all⟩)

/-!
In some sense, our intuition is correct: we have made our life hard, by
formulating a statement about finite sets, without letting Lean know that this was the case.

The advantage of working with finite sets is that we can sometimes outsource proofs
to explicit enumerations that Lean performs automatically.
We can exploit this automation via the `decide` tactic.

However, for the `decide` tactic to work, we should set ourselves up by
having explicitly finite sets, and several algorithms that, behind the scenes,
will take care of the appropriate enumerations.

The automation behind `decide` is driven by `Decidable` instances.
For most of you, `Decidabl`ity will likely play a marginal (or inexistent) role.
But for some, it may be more important.

Here is a more automated approach to the example above.

First, we observe that the set of divisors of a natural number is already available in Lean:
-/

#check Nat.divisors

/-!
Even better: `Nat.divisors n` is not just a set, but a `Finset`.
`Finset` is one of the ways that Mathlib has of talking about finite sets.

Here is how we can revisit the example above:
-/

example : Nat.divisors 6 = {1, 2, 3, 6} := by decide

/-!
The first thing to note is that the proof is painless!

The second thing to note is that the statement is not exactly the same as what it was before.

Earlier, we were proving an equality of sets.
The fact that these sets were finite helped us in the proof (at the core, the proof was a case split),
but we never made Lean directly aware of this fact.

The latest version of the example is an equality of `Finset`s.
This means that someone has already taken care of verifying that
* `Nat.divisors n` yields a finite set (and they also took care of dealing with the case `Nat.divisors 0`);
* the notation `{1, 2, 3, 6}` can ambiguously mean `Set` or `Finset`, depending on context -- it meant `Set ℕ`
  earlier, it means `Finset ℕ` now.

Of course, the fact that this proof became painless is simply a reflection that the work is hiding somewhere else.
In this case, the work is making sure that Lean can really verify these proofs by enumeration, following
around the `Decidable` instances and working with `Finset`s.

Note that working with `Finset`s can be annoying!
-/

end TPwL
