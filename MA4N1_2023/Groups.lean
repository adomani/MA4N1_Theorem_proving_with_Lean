import Mathlib.Tactic

namespace TPwL

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

variable (a b c : G)

example : (a⁻¹)⁻¹ = a := by
  exact inv_inv a
  done

lemma conj_mul : a * (b * c) * a⁻¹ = (a * b * a⁻¹) * (a * c * a⁻¹) := by
  exact conj_mul.symm
  done

example : a⁻¹ * (b * c) * a = (a⁻¹ * b * a) * (a⁻¹ * c * a) := by
  -- the "boring" way
  simp [← mul_assoc]
  done

example : a⁻¹ * (b * c) * a = (a⁻¹ * b * a) * (a⁻¹ * c * a) := by
  -- the "recycle the lemma we already proved" way
  convert conj_mul a⁻¹ b c <;>
  simp
  done

/-
For elements of groups, we may be interested in computing their order.
Mathlib calls the order `orderOf g` (and `addOrderOf a` in the case of an additive group).
-/

--  In fact, the order is defined for a `Monoid`, not only for groups.  Oh, well.
#check orderOf

-- feel free to free-style this, but read on if you want hints!
example : addOrderOf (2 : ZMod 5) = 5 := by
  sorry
  done

/-
In the example above, you may be in the following situation:
* you (hopefully) know the meaining of `orderOf/addOrderOf` in maths;
* you are confronted with the Mathlib implementation of that definition.

How do we proceed?

First, we could "Go to definition" and check if `Mathlib`s definition happens to be
directly mirroring the one that we already know:
-/

#print orderOf
/-
def orderOf.{u_1} : {G : Type u_1} → [inst : Monoid G] → G → ℕ :=
fun {G} [Monoid G] x => Function.minimalPeriod (fun x_1 => x * x_1) 1

Ok, that probably did not go according to plan.
Even cleaning the output above for readability:

def orderOf : the inputs are a `Monoid` `G` and an element of `G`; the output is in `ℕ`
The processed definition is:
if `x ∈ G`, then `orderOf x` is the "`Function.minimalPeriod`" of the function
`G → G` given by `y => x * y`.

We can probably guess what `minimaPeriod` is,
we can probably convince ourselves that this coincides with our "standard" definition.

However, whoever wrote this definition did it because it "worked better for Lean",
but surely they must have wanted the definition that we expect!

This means that we should look for a lemma the proves that whatever the actual
`Mathlib` implementation is, it is equivalent to the "mathematical" one.

Such lemmas are often named `<property>_def`, `<property>_iff`, or something like this.
-/

#check orderOf_eq_iff
/-
orderOf_eq_iff.{u_1} {G : Type u_1} [inst✝ : Monoid G] {x : G} {n : ℕ} (h : 0 < n) :
  orderOf x = n ↔ x ^ n = 1 ∧ ∀ (m : ℕ), m < n → 0 < m → x ^ m ≠ 1

**Much better!**
Longer, but better!
Hopefully, you recognise the assertion now:
assuming the `n` is strictly positive,
the statement `orderOf x = n` is equivalent to the conditions
* `x ^ n = 1`
* for all `m` strictly between `0` and `n`, `x ^ m` is not `1`.

I hope that you recognise this!

Thus, presumably when you are getting familiar with `orderOf`, you will begin by
using `rw [orderOf_eq_iff]` and continue working with the definition that you know.
(Note that `rw` works not only with equalities, but also with iffs.)

*Aside.*
Probably, in the long run, you may appreciate the *actual* implementation and you will
be able to take advantage also of that, but, thanks for the equivalence,
in theory there is no need.

One more twist: what replaces the power in `x ^ n = 1` in the case of an `AddGroup`?
Let's find out!
-/

#check addOrderOf_eq_iff
/-
addOrderOf_eq_iff.{u_1} {G : Type u_1} [inst✝ : AddMonoid G] {x : G} {n : ℕ} (h : 0 < n) :
  addOrderOf x = n ↔ n • x = 0 ∧ ∀ (m : ℕ), m < n → 0 < m → m • x ≠ 0

So, `x ^ n = 1` became `n • x = 0`.
That may look more or less reasonable, except, possibly for `•`:
this is the "scalar product" operation.
In this case, it allows you to multiply a natural number `n` and an element of a generic
`AddGroup` `x`.
Indeed, it is just like the power, but for iterated addition.
In easy cases, using `simp` may clear this.
If you find yourself having to actually work with `•`, note that its name is
`nsmul` (`s`calar `mul`tiplication by `n`atural numbers -- there is also `smul`).
Thus, you may look for lemmas involving `nsmul` to help out -- but this will not
be necessary in this exercise sheet!

Let's go back to proving the result that we stated above.
-/

example : addOrderOf (2 : ZMod 5) = 5 := by
  rw [addOrderOf_eq_iff]
  simp
  norm_num
  done

example : addOrderOf (3 : ZMod 6) = 2 := by
  rw [addOrderOf_eq_iff]
  simp
  norm_num
  done

/-
Finally, a small quirk:
`orderOf/addOrderOf` returns a natural number for *every* element of every (`Add`)`Group`.
Also for the elements that may not have finite order.
What is the order of an element that does not have finite order?
Well, it must be a natural number and `Mathlib`s convention is that it is `0`.

In this case, a relevant lemma is `addOrderOf_eq_zero_iff'`.

Here is an example.
-/

example : addOrderOf (1 : ℤ) = 0 := by
  rw [addOrderOf_eq_zero_iff']
  intros n n0
  simp
  exact Nat.pos_iff_ne_zero.mp n0
  done

/-

-/

end TPwL
