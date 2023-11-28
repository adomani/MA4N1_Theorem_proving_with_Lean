import Mathlib.Tactic

namespace TPwL

/-!

#  Divisibility as an excuse to see more tactics

This exercise sheet proves some results on divisibility among natural numbers.

Before going into the actual exercises, I want to introduce the tactic `rcases`.
It is personally one of my favourite tactics, although it took me a while to
appreciate how useful it can be!
You would be surprised by how far you can get by with just `refine/apply` and `rcases`!

##  Digression on `rcases`

The `rcases` tactic is the recursive version of `cases`.
It has lot's of features, but in its most basic form it allows us to avoid long chains
of `cases x with ...`.
Here is a brief summary of some of its features.

If we have an assumption `h : p ∧ q` in our local context, then `rcases h with ⟨hp, hq⟩`
"deconstructs" the `And` and leaves the two hypotheses `hp : p, hq : q` in its place.

If we have an assumption `h : p ∨ q` in our local context, then `rcases h with hp | hq`
"deconstructs" the `Or` and produces two goals, one containing the hypothesis `hp : p`,
the other containing `hq : q`.

These deconstructions can be combined recursively.
-/

example {m n : ℕ} (h : (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = 2)) : m = 0 :=  by
  rcases h with ⟨m0, _n1⟩ | ⟨m0, _n2⟩ <;>
  exact m0
  done  -- do experiment with the code in this proof!

/-!
... and it can be used on `inductive` types as well:
-/
example {n : ℕ} : (n = 0) ∨ (n = 1) ∨ (n = 2) ∨ (3 ≤ n) :=  by
  --  the underscores represent, in succession,
  --  `Nat.zero`, `Nat.succ Nat.zero`, `Nat.succ (Nat.succ Nat.zero)` and the rest, that is
  --  `0`, `1`, `2`, `n + 1 + 1 + 1`
  rcases n with _ | _ | _ | _ <;>
  simp
  exact? says exact tsub_add_cancel_iff_le.mp rfl
  done  -- do experiment with the code in this proof!

/-!
One more feature: if destructuring you encounter an equality where one of the two
sides is a variable and the other side does not contain the variable,
you can write `rfl` in the corresponding `rcases` slot and `rcases` replaces
all occurrences of that variable by its value.
-/

example {n : ℕ} (h : (n = 0) ∨ (n = 1) ∨ (n = 2) ∨ (n = 3) ∨ (n = 4)) : n ≤ 4 :=  by
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    repeat apply Nat.succ_le_succ
  all_goals exact Nat.zero_le _
  done  -- do experiment with the code in this proof!

/-!
Take a look at the documentation for `rcases` to see more features.
-/

#help tactic rcases

/-!
Now that the aside is over, let's go to divisibility.

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

You can take a look at the documentation for `interval_cases` here:
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
  sorry
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

Let's now prove an "induction principle" for natural numbers that works on divisibility.

You may find `Nat.strongInductionOn` useful.
-/
#check Nat.strongInductionOn

lemma dvd_induction {P : ℕ → Prop} (n : ℕ)
    (P0 : P 0)
    (P1 : P 1)
    (P_mul : ∀ {p a}, Nat.Prime p → a ≠ 0 → a ≠ 1 → P a → P (p * a))
    (P_prime : ∀ {p}, Nat.Prime p → P p) :
    P n := by
  sorry
  done

/-!
This is something that may appear unfamiliar.

First, `open scoped Pointwise` means that we can access the features that are associated
with `Pointwise`.
Typical features include special notation, syntax, instances, and so on.
The reason they are only available inside an `open scoped` is that they may conflict with
some more common conventions, and you would not want to have the "unusual" instances affect
the "usual" ones all the time.

In the specific case of `Pointwise`, the main feature that we are after is the possibility
of multiplying `Finset`s.

The product of two `Finset`s is defined as the set of all pairwise products of one element
from each `Finset`.

For example,
-/
open scoped Pointwise

example : ({0, 1, 2} : Finset ℕ) * {3, 4} = {0, 3, 4, 6, 8} :=  by
  decide
  done  -- if you are curious, change the numbers and get some practice!

/-!
Our main goal will be to show that the (Fin)set of divisors of a product of two
natural numbers is the product of the sets of divisors of each factor.
If you never thought about multiplying sets of numbers, think about why the statement
is true and then get on with the proof!

In my proof, I conclude by using the `aesop` tactic.
This tactic is a proof-search tactic and is *very* useful!
In fact, the reason for not mentioning it earlier was precisely to get you
to learn how to do something on your own, so that when `aesop` fails,
you are not necessarily stuck!
-/

#help tactic aesop

lemma _root_.Nat.Prime.divisors_mul (n : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    Nat.divisors (p * n) = Nat.divisors p * Nat.divisors n := by
  sorry
  done

/-!
Our main result: the divisors of a product are the product of the divisors.
-/

example {m n : ℕ} : Nat.divisors m * Nat.divisors n = Nat.divisors (m * n) := by
  sorry
  done

end TPwL
