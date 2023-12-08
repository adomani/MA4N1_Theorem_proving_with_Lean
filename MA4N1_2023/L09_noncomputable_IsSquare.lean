import Mathlib.Tactic

namespace TPwL

/-!
#  A short introduction to `noncomputable` and `Decidable`

The concepts of `noncomputable` and of `Decidable` are somewhat related.
Further players that are involved in this area are `Classical` and the
difference between `Prop` and `Bool`.
Here, we try to give a light touch introduction to these topics, by giving
one example of a `noncomputable` definition and one of a `Decidable` instance.
You will see that `Prop` vs `Bool` also makes an appearance.
To avoid saying *nothing* about `Classical`, let's simply point out that,
within `open Classical` *every* `Prop` automatically acquires a `Decidable`
instance and can therefore be turned into a `Bool`.

##  `noncomputable`

Sometimes, when using Lean, you may receive a warning that some definition should be marked as
`noncomputable`.

For example, Lean tells us that the definition `Real_inv` bow should be `noncomputable`:
if in the code below, you comment out the `noncomputable`, Lean will give the following error:

  failed to compile definition, consider marking it as 'noncomputable' because it depends on
  'Real.instInvReal', and it does not have executable code
-/
noncomputable
def Real_inv (a : ℝ) : ℝ := a⁻¹

/-!
Let's investigate this a little more.

First, not all operations on `ℝ` are `noncomputable`:
-/
section computable_Reals
variable (a b : ℝ)

def Real_add : ℝ := a + b
def Real_sub : ℝ := a - b
def Real_mul : ℝ := a * b
end computable_Reals

/-!
What makes `Real_inv` "special"?  Or, rather, `noncomputable`?

Digging deeper into the definition, the culprit turns out to be the way in which `a⁻¹` is defined.
In order to "compute" `a⁻¹`, we should know whether `a` is `0` or not.
(Recall, that since functions in Lean must return a value for *every* input,
there is a convention that `0⁻¹ = 0`.)

On the one hand, if `a` is non-zero, then for any Cauchy sequence converging to `a`,
eventually the terms will be non-zero and the sequence of "inverses of non-zero terms" is Cauchy
and converges to `a⁻¹`.
(Given the convention on `0⁻¹ = 0`, we do not even have to worry about inverting the terms
of the Cauchy sequence that are equal to `0`.)

So far so good.

On the other hand, if `a` is `0`, then the sequence constantly equal to `0` is a Cauchy sequence
converging to `a⁻¹ = 0⁻¹ = 0`.
So... where is the issue?

As you may have guessed, it is the `if ... then ... else ...` split.
The `if`-clause asks us to decide whether the real number `a` is zero or not.
*This* is an undecidable problem: no algorithm exists to test this property.

Of course, in some cases, we may know that `a` is `0`, but the general question is undecidable.

Let's test this.
-/
noncomputable  -- comment this and Lean complains
def Real_is_zero (a : ℝ) : Bool := a = 0

--  No need to mark as `noncomputable`, since this is a `Prop`, not a `Bool`.
def Real_is_zero_Prop (a : ℝ) := a = 0

/-!
Hopefully, this clarified some possibly murky points.

You see that there is a subtle interaction between computability, `Prop`s and `Bool`s.

##  `Decidable`

`Decidable` is a typeclass that certain `Prop`ositions have.
Proving a `Decidable` instance on `(p : Prop)` means that
* either you produce a proof of `p`,
* or you produce a proof of the negation `¬ p` of `p`.

If you take a look at the constructors for `Decidable`, you see that there exactly two:
* `Decidable.isFalse` obtained by providing a proof of `¬ p`;
* `Decidable.isTrue` obtained by providing a proof of `p`.
-/
#print Decidable

/-!
Let's provide a `Decidable` instant to the predicate `IsSquare` on natural numbers.

Since there is a rich infrastructure of results available to provide `Decidable` instances,
we take advantage of the fact that Lean will be able to infer a `Decidable` instance on
`IsSquare` if we can prove that `IsSquare` is equivalent to another `Prop` for which Lean
already has a `Decidable` instance.

Thus, we begin by proving a lemma showing that `IsSquare` is equivalent to a different
(but equivalent!) `Prop`osition.
-/

theorem IsSquare_iff_mul_self {m : ℕ} : IsSquare m ↔ Nat.sqrt m * Nat.sqrt m = m := by
  rw [← Nat.exists_mul_self m, IsSquare]
  -- `rw` is not able to change the order of one of the equalities, since it does
  -- not "enter" the binders: the `∃` prevents `rw` from working in this case.
  -- `simp_rw [x]` is similar to `simp only [x]` and *does* enter binders.
  simp_rw [eq_comm]
  done

--  The following examples can be proved using the result above.
--  `norm_num` does not work before the `rw` and neither does `decide`.
example : IsSquare 36 := by
  --  decide  -- failed to synthesize `Decidable (IsSquare 36)`
  rw [IsSquare_iff_mul_self]
  norm_num
  done

example : ¬ IsSquare 20 := by
  --  decide  -- failed to synthesize  `Decidable ¬IsSquare 20`
  rw [IsSquare_iff_mul_self]
  norm_num
  done

--  Let's provide now the `Decidable` instance.
--  `decidable_of_iff'` takes as input a `Prop` that already has a `Decidable` instance
--  and a proof of the equivalence of the "`Decidable`" `Prop` and the not-yet-`Decidable`
--  one and "transports" the decidability.
instance {m : ℕ} : Decidable (IsSquare m) :=
  decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) IsSquare_iff_mul_self

--  The two examples above can now be proved using `decide`.
example : IsSquare 36 := by
  decide
  done

example : ¬ IsSquare 20 := by
  decide
  done

end TPwL
