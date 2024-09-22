import Mathlib.Tactic

namespace TPwL_in_implicit_explicit

/-!
#  The `in` modifier

Several commands in Lean can be followed by an `in`.
From a strictly mathematical point of view, this is just a convenience and can be ignored.
However, as we are effectively writing code to check a mathematical proof,
it can be useful to know about this, to make the code sturdier and cleaner.

##  Scope

Many commands in Lean modify the environment.
For instance, `variable (n : ℕ)` introduces a generic natural number `n` in *all subsequent*
`lemma`s/`theorem`s/`example`s.

*All subsequent* really means "all until it doesn't anymore"!
This brings us to the concept of "scope".
There are various ways of influencing the scope of a command, but typically, any command
contained within a `section Title [...] end Title` block is "in scope" until the following `end`
and "out of scope" before being declared and after the following `end`.
-/

section There_is_n_here

-- `n` has not yet been declared
/--
error: unknown identifier 'n'
-/
#guard_msgs in
#check n  -- unknown identifier 'n'

variable (n : ℕ)

-- `n` has been declared and is in scope
#check n  -- `n : ℕ`

end There_is_n_here

-- `n` has been declared, but is out of scope
/--
error: unknown identifier 'n'
-/
#guard_msgs in
#check n  -- unknown identifier 'n'

/-

Other examples of commands to which the previous discussion applies are
* `open` (to open a `namespace/notation`);
* `open scoped` (to specifically open a `notation`, but not also the corresponding `namespace`);
* `set_option [option] true/false` (we saw the `set_option autoImplicit false`).

There is a command that helps us figure out what is in scope at any given location and what is not.

##  `#where`

The `#where` command tells you
* what `namespace`s are `open`,
* what `variable`s are declared,
* what `option`s have been set,

and so on.
-/
variable {R : Type*} [Ring R] (r : R)

#where

/-
Sometimes, you would like to limit the effect of one a command just to the following declaration.

For instance, you may be proving lemmas about one `Ring` and then you have one extra result to involves two.
Rather than having the second `Ring` polluting your environment, you can do this.
-/

example : 2 • r = r + r := by
  exact two_nsmul r
  done

#where

variable {S : Type*} [Ring S] (f : R →+* S) in  -- <--- note the `in` here!
example : f 0 = 0 := by
  exact RingHom.map_zero f
  done

#where

/-

#  Implicit vs explicit assumption in `lemma/theorem`

When stating a `lemma/theorem`, you have the option of declaring assumptions as implicit or explicit.

The proof of the corresponding result is completely oblivious to this choice.
However, when you then want to apply the result, the choice that you made will be *very* important.

Here is an example.
-/

--  it does not show, but the choice is `a` implicit, `a ≠ 0` explicit.
#print div_self

--  the following two lemmas differ in their name and whether `a` is explicit or not.
lemma div_ee (a : ℚ) (ha : a ≠ 0) : a / a = 1 := div_self ha
lemma div_ie {a : ℚ} (ha : a ≠ 0) : a / a = 1 := div_self ha

example (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) : a / a = b / b := by
  --  two explicit
  -- fails
  --apply  (div_ee ?_ ?_).trans

  -- works
  --apply  (div_ee _ ?_).trans

  -- works
  --apply  (div_ee a ?_).trans

  -- works
  --refine (div_ee ?_ ?_).trans ?_

  --  one implicit, one explicit
  -- works
  --apply  (div_ie ?_).trans

  -- works
  --  refine (div_ie ?_).trans ?_

  refine (div_ie ?_).trans (div_ie ?_).symm <;>
    assumption
  done

/-!

In the proofs above we used some notation that you may not have seen before.
When applying a previous result, you may want to
* pass it hypotheses that you have in context --
  the `a` in `div_ee a ?_`;
* create goals for some hypotheses --
  the `?_` in `div_ee a ?_`;
* ask Lean to fill those positions automatically --
  the `_` in `div_ee _ ?_`.

These variously annotated underscores are often referred to as *holes*.
Some tactic allow not to mention holes, like `apply`.
-/

example (a : ℚ) (ha : a ≠ 0) : a / a = 1 := by
  apply div_self  -- also `apply div_self _` works
  assumption
  done

/-!
Other tactics require all holes to be explicitly assigned.
-/

example (a : ℚ) (ha : a ≠ 0) : a / a = 1 := by
  -- fails
  --refine div_ee

  -- fails
  --refine div_ee _

  -- fails
  --refine div_ee _ _

  -- works
  --refine div_ee _ ?_

  -- works
  --refine div_ee ?_ ?_

  -- fails
  --refine div_ie

  -- works
  --refine div_ie ?_ ; assumption

  -- works
  refine div_self ha
  done

/-!

##  How to choose between implicit vs explicit?

There are not universal rules.
Also, the worst that can happen is that when you apply the lemma, you will have to
* either fill in lots of underscores for arguments that Lean could have figured out;
* or pass explicitly arguments that were marked as implicit using, for instance,
  `apply div_ie (a := 3)`.

It will not prevent you from proving what you want,
it may just make the process of formalization a little less automatic.

However, this is a principle that often applies.

*If a hypothesis/variable can be deduce from a later hypothesis, chances are that making it implicit is a good choice.*

In our example of `div_ee` vs `div_ie`, the hypotheses are
* `a : ℚ`;
* `ha : a ≠ 0`.

If, in whatever way, Lean figures out what `ha` should be,
it will have already figured out what `a` had to be.
Since eventually we need to pass enough information to Lean to fill in all arguments,
we may not need to pass it `a`, as `ha` will imply it.

Thus, *minimalistically*, we can hope that marking `a` as implicit is a good choice.

This is what `Mathlib` does in this case.

Lean also uses the *goal* to try to infer arguments, so an argument that can be reconstructed by looking at the goal
can in principle also be left implicit.
-/

#check add_comm
#check eq_div_iff_mul_eq'

/-
There could be subtle reasons why you may want to overrule this principle.
-/

#check add_zero

end TPwL_in_implicit_explicit
