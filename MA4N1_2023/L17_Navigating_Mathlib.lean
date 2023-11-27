import Mathlib.Tactic

namespace TPwL

/-!
#  Finding lemmas in `Mathlib`

This file covers some of the techniques that I use to find results in a part of `Mathlib`
that I do not already know.

It is a series of tips and tricks that may work in some situation!

##  Get familiar with `Mathlib`s naming convention!

[Mathlib's naming convention](https://leanprover-community.github.io/contribute/naming.html)
is *very* useful for finding what are the names of theorems.
It takes a while to get used to it, but it is definitely worth it!

The general principle is that the name should describe the *syntax* of the statement.

To first approximation, ignore upper/lower-casing and imagine that every capital letter
really stands for `_` followed by the corresponding lower-case letter.
There is information encoded in the casing, but in my opinion, it is mostly a distraction
than an added value.
-/

--#check Nat.succ_eq_add_one
--#check Continuous.add
--#check Polynomial.natDegree_add_le

/-!
Also, the general rule is that if the statement has a LHS and a RHS, then the RHS should be
simpler than the LHS.
A common assumption is also that the RHS should be the "obvious simplification" of the RHS.
-/
--#check true_and
--#check false_and
--#check map_add

/-!
Some parts of the name follow some convention.
For instance, `of` usually introduces an assumption.
-/

--#check lt_of_le_of_lt

end TPwL
