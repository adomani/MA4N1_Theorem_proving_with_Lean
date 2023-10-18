import Mathlib.Tactic

/-!
#  Groups

Working with the implementation of groups in Mathlib is very similar to what we already did with polynomials.
After all, polynomials have two operations and, with respect to each, they share a large common set of axioms
with the axioms for a group.

The main difference between multiplication (or addition) in semirings and groups is the existence of inverses/opposites.
We will come back to this in a moment.

One possibly surprising choice in Mathlib is that there are two (mathematically equivalent) definitions of groups,
depending on whether the operation is denoted by `*` or by `+`:
* the groups with multiplication as the operation are called `Group` in Mathlib;
* the groups with addition as the operation are called `AddGroup` in Mathlib.

My experience is that I got used pretty quickly to this and there are automated ways of converting results about
"multiplicative" groups to results about "additive" groups.

The takeaway is that, unless you have some good reason for wanting to work with an additive group,
stick with multiplicative notation.

Back to inverses (or opposites -- I will concentrate on multiplicative notation from now on).

##  `⁻¹` or `/`?

There are (at least) two ways of talking about inverses of elements:
-/

-- Let `G` be a (multiplicative) group and let `g, h` be elements of `G`
variable {G : Type} [Group G] {g h : G}

-- good, we can multiply elements of a group
#check g * h

-- we can take inverses of elements of a group
#check g⁻¹

-- and we can form more complicated expressions
#check g ^ 2 * h ^ (- 4 : ℤ) * g

/-!
All of the above is about `⁻¹`, i.e. `Inv`.
-/
#check Inv

-- There is also `Div`...
#check g / h

-- Mathematically is not great-looking, but let's check that it is what we expect
example : g / h = g * h⁻¹ := by
  exact?

/-
Ok, so that is really the definition of division.

Finally, the main property of inverses:
-/
example : g * g⁻¹ = 1 := by
  exact?

/-
Two comments.
* Can you guess how is the lemma stating the identity `g⁻¹ * g = 1` is called?
* Did you see that we simply used `1` and Lean was happy with it?
-/

/-!
#  Exercises
-/

example {a : G} : (a⁻¹)⁻¹ = a := by
  sorry

example {a b c : G} : a * (b * c) * a⁻¹ = (a * b * a⁻¹) * (a * c * a⁻¹) := by
  sorry

example {a b c : G} : a⁻¹ * (b * c) * a = (a⁻¹ * b * a) * (a⁻¹ * c * a) := by
  sorry
