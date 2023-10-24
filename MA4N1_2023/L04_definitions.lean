import Mathlib.Tactic

namespace TPwL

/-!

#  Developing an "API" around new definitions

First of all, `API` stands for `A`pplication `P`rogramming `I`nterface.
In the context of formalisation of mathematics,
it generically refers to (typically very trivial) results about a new concept that you have introduced.

For example, in the API for `Group` I would expect to find the statements that
* multiplying any element `g` of a group by the identity element returns the element `g`;
* multiplication is associative;
* multiplying a group element by its inverse gives the identity;
* the inverse of the inverse of an element is the element itself:

and so on.
Indeed, what we saw during the past lectures on `And, Or, Polynomial, natDegree, Group, orderOf`
was essentially the basic API results and then a little bit of extra theory that you could develop.

*Every* new definition in Lean should come with a (possibly small) API.
One important difference between informal and formal mathematics is that in informal mathematics
it is often easy to blur the distinction between genuinely different (and equivalent!) definitions.
Sometimes, even non-equivalent definitions may be used, depending on authors or context.

For example, you may have encountered "the" definition of the real numbers as
* Dedekind cuts of rational numbers;
* Cauchy sequences of rational numbers, up to equivalence;
* completion of the rational numbers, with respect to the absolute value;
* a complete, linearly ordered, Archimedean field;
* ...

When *formalising* the notion of real numbers, it is good practice to *pick one* definition and
prove that it is equivalent to all the others.
Once that is done, for a *user* of the formalisation, it should be irrelevant what the definition
*actually* is: they should have direct access to all the equivalent forms "from the API".

Ideally, the *user* should not need to know what the formal definition of `ℝ` is, but should be able to
convert between all the "usual" definitions by using lemmas in the library.

You saw some of this when you proved results about `orderOf` for groups.
The exercises were careful in *hiding* the actual definition, and making you go through the
property that you are familiar with:
the order is the smallest positive exponent of an element that gives the identity.

Let me emphasize:
*this is not `Mathlib`'s definition of order*!
But it is equivalent to it, and this is good enough.

Let's see this in practice, by developing a little API around the definition of the absolute value.
-/
def Abs (z : ℤ) : ℤ := if z < 0 then - z else z
/-
Note the syntax of `def`: it is very similar to the one of `theorem`.
We are defining a new concept, `Abs` (or rather `TPwL.Abs`, since we are inside the `TPwL`-namespace).
It takes an integer `z` as input and returns an integer.
The integer `Abs z` is defined by a case-split:
you can probably guess what the `if ... then ... else ...` syntax means!
-/

#check Abs 3
#check Abs (- 3)

#eval Abs (- 3)

lemma abs_eq_max (z : ℤ) : Abs z = max z (-z) := by
  -- since we proved *nothing* about `Abs`, this had better follow from the actual definition we gave!
  -- we access this by using `unfold`:
  unfold Abs
  split_ifs with h
  · -- here we would like to access the "API" around `max`
    -- we know that the `max` is equal to its second argument in this case, so...
    symm  -- swaps the two sides of an equality: Lean is *very* pedantic
    apply max_eq_right
    linarith  -- solves for us (in)-equalities that involve variables appearing linearly, more or less
    --  alternatively, this is how we could prove the `z ≤ -z` inequality:
    --  first, we use `h` and transitivity to reduce to proving that `0 ≤ -z`
    --  we actually end up using `h.le : z ≤ 0` and then transitivity
    --  note that `h.le.trans` exploits dot-notation twice: it stands for
    --  `LE.le.trans (LT.lt.le h)`, and uses that
    --  * the type of `h` begins with `LT.lt (it is a strict inequality);
    --  * the type of `LT.lt.le h = h.le` is `z ≤ 0` and it begins with `LE.le` (it is an inequality).
    --refine h.le.trans ?_
    --  the next `have` statement is there simply to make the following `exact?` succeed:
    --  we should guess that `h.le` should be the "right" assumption to close the goal.
    --have := h.le
    --exact?
  · simp at h -- to convert the `¬ z < 0` to `0 ≤ z`.  using `simp? at h` tells you the name of the lemma
    symm
    apply max_eq_left
    exact?
  done

lemma abs_zero : Abs 0 = 0 := by
  unfold Abs  -- this is not even needed in this case: `rfl` works directly
  split_ifs
  · exact rfl
  · exact rfl

--  following the approach from before, we can prove this result by `unfold`ing and splitting if's
lemma abs_neg (z : ℤ) : Abs (- z) = Abs z := by
  unfold Abs
  split_ifs with h k <;> linarith
  done

--  however... we may not need to do that!
example (z : ℤ) : Abs (- z) = Abs z := by
  rw [abs_eq_max, abs_eq_max, neg_neg, max_comm]
  done

/-
In fact, if the library already contains `max` and a well-developped API for it,
it may make sense to *define* `Abs` in terms of `max` and then develop the API
for `Abs` by relying on the one for `max` (and probably diverging from it, once
we get into more juicy facts).

Let's see how that would work out!
-/

def Abs' (z : ℤ) : ℤ := max z (-z)

lemma abs'_eq_max (z : ℤ) : Abs' z = max z (-z) := by
  rfl  -- this is just the definition!
  done

lemma abs'_neg (z : ℤ) : Abs' (- z) = Abs' z := by
  unfold Abs'
  rw [neg_neg, max_comm]
  done

lemma abs'_eq_abs (z : ℤ) : Abs' z = if z < 0 then - z else z := by
  unfold Abs'
  split_ifs with h
  · simp
    exact Int.le_of_lt h
  · simp at h ⊢
    assumption
  done

/-
This should feel like a much smoother experience!

The main reason is that we could rely on the API for `max`, rather than on "hard" automation,
provided for instance by `linarith`.

When formalising a new definition, try to keep as close as possible to definitions that already exist.
If you think that you have to make a big "leap", chances are that it will be easier to first define some
intermediate notion and then continue with what you want.

Lean will try hard to connect your "new" definition to the ones that it already knows about,
and it will be an easier experience for you to teach it new trick in small, incremental baby steps!

#  Instances

Sometimes, the "definition" that you want to make is to endow some "object" with some "structure":
for instance you may want to define the component-wise addition on pairs of integers and
prove that what you defined is an (additive) abelian group.

Lean has a special mechanism to keep track of such "definitions" which, for instance, automatically allows
you to use `+` as a notation for the operation.
Another great feature is that if your newly defined `+`-operation actually induces an abelian group
(i.e. you proved this!), then Lean will already know that therefore it is also an `AddMonoid` and you will
be able to use the lemmas that `Mathlib` has about `AddMonoid`s.

This mechanism is called the *typeclass system* and it is mostly painless to use.
When assuming such a hypothesis (e.g. you want to prove a result about groups or topological spaces),
then these assumptions are written inside square bracket (e.g. `[Group G]` or `[TopologicalSpace X]`).
If you want a new object `N` that you defined to be registered by Lean as a `Group N`, then you should
provide an `instance` of `Group` to `N`.

Here is an example.
We introduce the notion of an additive group to the pairs of integers.
-/

#check add_sub_cancel'

#synth AddCommMonoid (ℤ × ℤ)
#check add_sub_cancel' (0 : ℤ × ℤ)

@[ext]
structure point where
  x : ℤ
  y : ℤ

#check point
#print point
#print point.x
#print point.y

--  `inductive` is another way of generating definitions.
--  i will not spend much time on it today, but there is *a lot* that can be said about them!
--  if it turns out to be relevant for your projects, I will prepare a lecture about it.
inductive nat
  | zero : nat
  | succ (n : nat) : nat

--  Let's try with a definition of `even`
def even (n : Nat) : Prop := match n with
  | 0     => True
  | n + 1 => ¬ even n

#check Nat

example : even 2 := by
  unfold even
  unfold even
  unfold even
  trivial
  done

example : ¬ even 3 := by
  unfold even
  unfold even
  unfold even
  unfold even
  trivial
  done

example {n : ℕ} (h : even n) : even (n + 2) := by
  unfold even
  unfold even
  simpa
  done

--  a little unwieldy
example : even 8 := by
  unfold even
  unfold even
  unfold even
  unfold even
  unfold even
  unfold even
  unfold even
  unfold even
  unfold even
  trivial
  done

example (n : ℕ) : even (2 * n) := by
  induction n with
  | zero => simp? -- `simp` is stuck, since it does not know that `even 0` is `True`
                  -- let's teach it!
  | succ n ih => sorry
  done

--  Let's try with a different definition of `even`
def even' (n : Nat) : Prop := match n with
  | 0     => True
  | 1     => False
  | n + 2 => even' n

example : even' 8 := by
  unfold even'
  unfold even'
  unfold even'
  unfold even'
  unfold even'
  trivial     -- move me up!

end TPwL
