/-

#  Generalizations, automation, `library_search`, `simp`, tactics

As it happens, someone comes along and says:

"I just learned a cool fact!  A polynomial with coefficients in `ℕ` is monotone!"

Let's formalize this result!

Let's also think about what it really means...

Surely they intended to say that viewing a polynomial with coefficients in `ℕ`
as a function `ℕ → ℕ`, we obtain a monotone function.

-/

/-
### import

tells Lean to learn basic mathematical facts
-/
import Mathlib.Tactic

/-
### namespace

means that if we construct something and we call it `X`
its real name is going to be `TPwL.X`.
useful to avoid name-clashes with pre-existing objects.
-/
namespace TPwL

/-
### open

`open whatever` instructs Lean that when we refer
to `X`, it should look for `X` or `whatever.X`.

`namespace`s are ubiquitous, thus `open` allows us to avoid
constantly writing `Function.[...]` or `Polynomial.[...]`.
-/
open Function Polynomial NNReal

namespace Nat

/-
### variables

`variables (x : X)` means that, from now on
(within the current `section`/`namespace`/...), if we write `x`
and Lean does not already know what `x` means, then it tries
to see if `(x : X)` works and uses it.

Useful to avoid repetitions in a group of results that have
common assumptions and notation.
-/
variable  (f : ℕ[X])        -- `f` is a polynomial with coefficients in `ℕ`
          (P : ℕ[X] → Prop) -- `P` is a property of polynomials: `P f` may be
                            -- true or false

/-
### Digression on `Prop`

`Prop` is the "generic Type of propositions".  Most of the times, you can
think of this as `true/false`.
(The Type of "actual" `true/false` is called `bool` and
`true` is really `tt`, `false` is really `ff`.)

Thus, when we write `P : ℕ[X] → Prop` we are introducing a function `P`
that takes a polynomial with coefficients in `ℕ` and returns `true`
or `false`.  For instance, "being monic" could be one such function.
Also, "the leading coefficient of `f` equals the first decimal digit
of the `deg f`-th odd perfect number, if it exists, and `1` otherwise".
-/

/-
### theorem/lemma

Presumably, you already know about this.

The syntax is
  `theorem <name_of_theorem> <hypotheses> : <conclusion> := <proof>`

* <name_of_theorem> is the identifier that we can then use to refer to it.
  It is like a `\label` in laTex.

* <hypotheses> is where we list the assumptions that we make.
  For instance `(a : ℕ)` or `[CommGroup G]` or `(f : ℕ → ℝ)` or
  `(Goldbach: ∀ n : ℕ, ∃ p q, Prime p ∧ Prime q ∧ p + q = n)`.

  Bonus: to "see" Type-inference at work, look at the outputs of
  ```lean
  #check     ∀ n, ∃ p q, Prime p ∧ Prime q ∧ p + q = n
  #check ∀ n : ℕ, ∃ p q, Prime p ∧ Prime q ∧ p + q = n
  ```

* <proof> is the actual proof term.
  Usually, this is a sequence of tactics inside a `by ... done` block.
-/
theorem my_induction
  (P_zero  : P 0)
  (P_add   : ∀ p q, P p → P q → P (p + q))
  (P_X_pow : ∀ n : ℕ, P (X ^ n)) :
  P f :=
by
  -- hover over `polynomial.induction_on'`
  refine Polynomial.induction_on' f ?_ ?_
  · -- `hint` reports `assumption`, among others
    -- `library_search` reports `exact P_add`
    exact P_add
  · intros n a
    simp [← C_mul_X_pow_eq_monomial]  -- replace `monomial n a` with `a * X ^ n`
    -- proceed by induction on `a`, call
    induction a with
    -- base case: `a = 0`
    | zero =>
      -- `simp?` to get some insight
      -- `rwa [CharP.cast_eq_zero, zero_mul]` also works
      simp [P_zero]
    -- * `a` the variable in the induction step
    -- * `ha` the inductive hypothesis
      -- induction step: `a → a + 1`
      -- `a.succ` stands for `Nat.succ a`: the `succ`essor function applied to `a`
      -- Lean "prefers" `Nat.succ` since it is one of the two "constructors" for `ℕ`.
    | succ a ha =>
      simp [add_mul]
      apply P_add _ _ ha (P_X_pow _)
  done

/-
### example

The same (almost) as `theorem`, except that we cannot assign it a name.
-/
example : Monotone (fun n ↦ f.eval n) :=
by
  apply my_induction f _
  · -- show that the `0`-polynomial is monotone
    simp
    exact?
    -- we can compact this to `simp [monotone_const]` or more explicitly `simp only [eval_zero, monotone_const]`
  · -- if two polynomials are monotone, then so is their sum
    intros f g hf hg
    -- use that the sum of two monotone functions is monotone
    -- we can find the name of the lemma using auto-completion (Ctrl-Space) and guessing
    convert Monotone.add hf hg
    simp
  · -- show that monomials are monotone
    intros
    simp
    apply Monotone.pow_right
    apply monotone_id
  done

end Nat

/-
Now that we proved it for `ℕ`, let's generalize to `ℝ≥0`.

Copy-paste the above, change `ℕ` to `ℝ≥0` and fix the issues.
-/
namespace nnreal

end nnreal

#lint

/-
Now that we proved it for `ℕ` and for `ℝ≥0`, let's generalize further.

Copy-paste the above and look for a common generalization of `ℕ` and `ℝ≥0`.
-/

namespace next

--  -->  semiring --> comm --> ordered --> canonically

end next

/-
Finally, let's confirm that the more general result proves to the special cases that we know.
-/

example (f : ℕ[X]) : Monotone (fun n ↦ f.eval n) :=
by
  sorry
  done

example (f : ℝ≥0[X]) : Monotone (fun n ↦ f.eval n) :=
by
  sorry
  done


end TPwL
