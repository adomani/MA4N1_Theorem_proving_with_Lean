import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev

namespace TPwL

/-!
#  Finding lemmas in `Mathlib`

This file covers some of the techniques that I use to find results in a part of `Mathlib`
that I do not already know.

It is a series of tips and tricks that may work in some situation!

#  Get familiar with `Mathlib`s naming convention!

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

/-!
#  Use autocompletion (Ctrl-Space) to guess the name of a lemma

If you have an idea of how the name of the lemma should start, type the beginning and then
press `Ctrl-Space`.
You will get an auto-complete dialog that will suggest how to fill in the rest of the name.
It also gives useful type information for the statement, to fine-tune the search.

After getting more familiar with the naming convention, this is my method of choice,
and certainly the first attempt that I make at finding a lemma name.
Honestly, the success rate of this method greatly increases with time,
so it may not feel very efficient at the beginning, but it should improve!

#  Produce a *M*inimal *W*orking *E*xample first...

Producing a [#mwe](https://leanprover-community.github.io/mwe.html) is a very good way to
isolate what the issue is and removing unnecessary complications.

Also, once you have a #mwe, you can easily share it with others and they will be able
to see quickly what the problem is and may be able to help.
Even better, the process of producing a #mwe often suggests to *you* what the next step should be!

#  ... and see if automation helps!

And even if that is not the case, maybe `exact?` will prove the result for you?
Or `simp`?  `aesop`?  `hint`?
(`hint` requires a more recent version of `Mathlib` than the one on which this project is based.
I might update `Mathlib` soon, but wanted to avoid doing it during the term, to avoid having
to revisit the proofs that may brake with the update.)

#  `have` inside a proof and/or `extract_goal`

If you have an idea of what the next step is, and it would require using several assumptions
from the local context, then there are a couple of options.

1.  You could add a `have new_hyp : <statement> := by sorry` and try to fill in the `sorry`
    by some combination of the above tactics.
2.  You could use `extract_goal` to create a standalone goal with the current goal and
    its assumptions, to try to produce a #mwe and reduce to the above cases.

#  [Loogle](https://loogle.lean-lang.org/)

Loogle is a search engine that allows you to look for lemmas in `Mathlib` using various filters.
You can restrict to lemmas that contain
* certain `Type`s,
* certain names,
* an implication,
* and so on.

You can also mix such conditions and there is an extensive syntax for specifying exactly
what you are looking for.

It takes some time getting used to, but it can be very powerful!

For instance, say that we are looking for
-/
#check sq_sum_le_card_mul_sum_sq
/-!
We might try
`Finset.sum, _ ^ _, LE.le`

and then maybe

`Finset.sum, Finset.card, _ ^ _, LE.le`

#  [Moogle](https://www.moogle.ai/)

This is an AI-based search that takes "natural language" as input.
Suppose that we are still trying to look for `sq_sum_le_card_mul_sum_sq`.
We could try

`the sum of the squares is less than or equal to the square of the sum`.

#  Look at the source code

This is actually something that I do regularly.
It is very easy to get to a reasonable place in the library using the "Go to definition"
menu, or `Ctrl-click`.
Once you are in a relevant file, scroll around for lemmas that look similar to the one
that you want, if you can find them.
Chances are, you will find inspiration to help you get unstuck!

#  Global search inside the `.lean` files

Since the naming convention takes into account the *syntax* of the statement,
looking for "fundamental theorem of calculus" as a lemma name may not be productive.
However, the documentation should include this information, at least for "well-known"
results.
In such cases, a global search among the `mathlib` files can be useful.

Here is an example of what you can do with a Unix-like command-line.

`grep "undamental.*calculus" $( find lake-packages/mathlib/ -name '*.lean' )`
-/

end TPwL
