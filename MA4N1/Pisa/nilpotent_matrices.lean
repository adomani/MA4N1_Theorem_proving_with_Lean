import Mathlib.Tactic.Recall
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

section Origin_of_the_question

/-!
[Source](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Nilpotent.20implies.20trace.20zero/near/381540803)
-/

variable (R : Type _) [CommRing R] {n : Type _} [DecidableEq n] [Fintype n]

/-! This is a question asked on the [Lean Zulip chat](https://leanprover.zulipchat.com/). -/

-- I don't suppose anyone has a proof of this lying around:
-- Fairly sure `IsReduced` suffices (at least in commutative case) but
-- I'll settle for a proof over a field.
example [IsReduced R] {A : Matrix n n R} (h : IsNilpotent A) :
    A.trace = 0 := sorry

/-!
The question is very precise, but it leaves a few lingering follow-up questions.

* Is the statement true?
* Can the hypothesis `IsReduced R` be removed?
* Can `CommRing R` be weakened to `Ring R`?  Or even `Semiring R`?

Possible first reactions.

* Over a field, the result is true: the trace is the sum of the eigenvalues and
  all the eigenvalues of a nilpotent matrix are `0`.
* Over an integral domain -- also, since an integral domain embeds in its field of fractions.
* Nilpotent elements are clearly an issue: if `ε ∈ R` is non-zero and nilpotent,
  then the `1 × 1` matrix `(ε)` has trace that is nonzero!

What if we weaken the statement to `IsNilpotent A.trace`?
Since the question assumes `IsReduced R`, the trace being nilpotent is the same as the trace being `0`.
But, now the counterexample with a ring containing nilpotents no longer contradicts this statement!
-/

--  Could maybe this be true?  Notice that `IsReduced` no longer appears and
--  the conclusion is that the trace is *nilpotent*, as opposed to `0`.
--  The ring is still a `CommRing`.
example {A : Matrix n n R} (h : IsNilpotent A) :
    IsNilpotent A.trace := sorry

/-!
#  Enter the main tool

About a month before this question had been asked, this result had arrived into `Mathlib`:
-/

#check Polynomial.isUnit_iff_coeff_isUnit_isNilpotent

/-!
How about this?

Assume that `A ^ N = 0`.

Start with the identities

`I = I - (tA) ^ (N + 1)`
`  = (I - tA)(I + tA + ... + (tA) ^ N)`.

Compute determinants on both sides and use that the determinant of a product is the product of the determinants.

Deduce that the determinant of `(I - tA)` is an invertible polynomial.
Therefore all its coefficients of positive degree are nilpotents.

Is this right? If only I had a proof assistant at hand...

The rest of this file develops the tools that should allow you to formalize the above proof
in the following hour!
-/

end Origin_of_the_question

section CommRing

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

open Polynomial

recall Matrix.charpolyRev (M : Matrix n n R) := det (1 - (X : R[X]) • M.map C)

namespace Matrix

variable (M : Matrix n n R)

example (hM : IsNilpotent M) : IsUnit (charpolyRev M) := by
  sorry
  done

end Matrix

end CommRing

/-!
#  Extra credit

Can you weaken `CommRing R` to `Ring R`?
-/

variable {R : Type*} [Ring R] {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n R)
open Matrix

example (hM : IsNilpotent M) : IsNilpotent M.trace := sorry
