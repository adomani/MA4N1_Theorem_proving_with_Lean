import Mathlib.Tactic

namespace MA4N1

section Presentation
/-!
#  Preliminaries

The exercises cover several different notions:
* `Polynomial` rings  `R[X]`;
* `natDegree`s of `Polynomial`s.

I will certainly not have time to talk about all of the above, but you are of course more than
welcome to explore on your own and to ask lots of questions!

##  `Polynomial`

The structure `Polynomial` takes a (Semi)`Ring` as input and returns...
the `Mathlib` formalization of polynomials!
-/

section Polynomials

variable {R : Type*} [Semiring R] {r : R}

#check Polynomial R
#guard_msgs(drop error) in
#check R[X]

open Polynomial

#check R[X]
#guard_msgs(drop error) in
#check R[Y]

-- ##  Basic constructors

-- ###  `C` -- the constants
-- the extended name is `Polynomial.C`
#check C r

example {s : R} : C (r * s) = C r * C s := by
  exact?

-- ###  `X` -- the variable
-- the extended name is `Polynomial.X`
#check (X : R[X])
#check X

-- ###  `monomial` -- the... monomials
-- we are not actually going to use them
#check monomial 3 r

example {n : ℕ} : C r * X ^ n = monomial n r := by
  exact?

example : ((X + C 1) ^ 2 : R[X]) = X ^ 2 + 2 * X + 1 := by
  rw [sq, mul_add, add_mul, add_mul, ← sq, add_assoc, add_assoc]
  simp     -- clears the `C`s
  congr 1  -- matches the common parts of the expressions
  rw [← add_assoc, two_mul]

example : ((X + C r) ^ 2 : R[X]) = X ^ 2 + 2 * C r * X + C r ^ 2 := by
  rw [sq, mul_add, add_mul, add_mul, ← sq, add_assoc, add_assoc, X_mul_C]
  congr 1  -- matches the common parts of the expressions
  rw [← add_assoc, two_mul, ← add_mul, sq]

variable {S} [CommSemiring S] in
example : ((X + 1) ^ 2 : S[X]) = X ^ 2 + 2 * X + 1 := by
  ring

variable {S} [CommSemiring S] in
example : ((X + C 1) ^ 2 : S[X]) = X ^ 2 + C 2 * X + C 1 := by
  simp?
  ring

#check natDegree

--  Lean may not always have enough information to fill in typeclass arguments
#guard_msgs(drop error) in
example : natDegree 1 = 0 := by
  exact?

#guard_msgs(drop error) in
example : natDegree (C r * X + C 1) = 1 := by
  exact?  -- we are missing a hypothesis!

--  prove using `natDegree_add_eq_left_of_natDegree_lt`
example [Nontrivial R] : natDegree (X + C 1) = 1 := by
  rw [natDegree_add_eq_left_of_natDegree_lt]
  exact?
  simp?

--  One thing that could be useful for some of the exercises.
--  The evaluation of polynomials in `R[X]` at a fixed polynomial `p` is a ring homomorphism
--  `R[X] →+* R[X]`.
--  This is called `Polynomial.aeval` in `Mathlib`.

noncomputable
example {R} [CommRing R] (p : R[X]) : R[X] →+* R[X] :=
(aeval p).toRingHom

/-
###  Pitfall: disappearing `C`s

The exact shape of a lemma in `Mathlib` is what makes it applicable or not in any given situation.
On the one hand, not all combinations of lemmas with/without `C` in statements about `Polynomial`s
are available.
On the other hand, `simp` will try to remove `C`s in your expressions, if it can.
This means that `exact?` might have found a lemma *before* applying `simp` and may fail afterwards:
-/
example [Nontrivial R] : natDegree (X + C 1) = 1 := by
  --simp  --uncomment this `simp` and `exact?` fails
  exact?

end Polynomials

end Presentation

section Exercises
/-
# Exercises
-/

open Polynomial

variable {R : Type*} [CommRing R]
/-!
Polynomials in Mathlib are denoted by the familiar notation `R[X]`.
This notation is available because of the line `open Polynomial` just inside this section.
Without `open Polynomial`, the notation is `Polynomial R`.

Note that the `R` in `R[X]` is a `CommRing` and you can replace it by whatever (Semi)ring you want.
The `[X]` part is hard-coded: it instructs Lean to consider polynomials in one variable over `R`.
For instance, `#check R[Y]` yields an `unknown identifier 'Y'` error.

Of course, the name of the variable in `R[X]` is `X`, so the notation is internally consistent,
but you do not get the option of changing it, at least not easily!

Also, the "obvious" inclusion `R ↪ R[X]` is denoted by `C` (for `C`onstants).
The full name is `Polynomial.C`, but we are inside `open Polynomial`, so `C` suffices.

Thus, `X ^ 3 + C 3 * X - C 2` represents the polynomial that you might write in TeX as
$x ^ 3 + 3 x - 2$.
-/

--  The following exercises get you familiar with `natDegree`s of polynomials.
section natDegree

example : natDegree (X + 1 : ℤ[X]) = 1 := by
  sorry
  done

example : natDegree (C 0 * X ^ 2 + C 3 * X : ℤ[X]) = 1 := by
  sorry
  done

example (h2 : (2 : R) = 0) (h3 : (3 : R) = 0) : (0 : R) = 1 := by
  sorry
  done

lemma aux [Nontrivial R] (h2 : (2 : R) ≠ 0) :
    natDegree (C 4 * X ^ 2 : R[X]) < natDegree (C 2 * X ^ 3 : R[X]) := by
  sorry
  done

/-- Proof without automation -- I had prepared this before tactic `compute_degree` was merged. -/
example : natDegree (C 2 * X ^ 3 + C 4 * X ^ 2 + 1 : R[X]) ∈ ({0, 3} : Set ℕ) := by
  sorry
  done

/-- Proof with more automation -- works now that `compute_degree` is merged. -/
example : natDegree (C 2 * X ^ 3 + C 4 * X ^ 2 + 1 : R[X]) ∈ ({0, 3} : Set ℕ) := by
  sorry
  done

end natDegree

end Exercises

end MA4N1
