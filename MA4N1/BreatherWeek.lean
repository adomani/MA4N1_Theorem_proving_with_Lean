import Mathlib --.Tactic --.IntervalCases

/-!
#  Breather week, November 2025

This file is inspired by one of the outlines for this year's projects.

The main motivation is not necessarily to give the shortest possible proof of the final `example`,
but rather it is intended as a way of providing tools to avoid going "against" the automation.

In particular, in the final statement (which is *exactly* what we want to prove), there are two
main points that "complicate" the proof.

1. It uses `ℕ`-subtraction.  The use of subtraction among natural numbers should be avoided when
   possible. Besides, unless you know that the number that you are subtracting is not bigger than
   the original number, the answer is `0`, which is unlikely to be a useful notion.
   Of course, sometimes you really want to use it, but, even in such instances, try to limit its
   appearance to a minimum.
2. In the statement `m` and `n` are natural numbers, but they are immediately required to be
   strictly bigger than `2`.  This adds the burden of extra proofs.  It also means that the
   statement has 3 "natural" ranges:
   * `m < 3` or `n < 3`, where no solution is even considered;
   * `m < 6` and `n < 6`, where we can really find solutions;
   * `6 ≤ m` or `6 ≤ n`, where again there are no solutions.

To overcome these (minor) difficulties, we proceed in three steps.

### Step 1: `easy`
We first prove a result (`easy`) analogous to the one that we want, but "shifting" by `3`
the values of `m` and `n`, so that the condition that `m` and `n` are larger than `2`,
becomes simply the condition that they are non-negative, which is automatic for natural numbers.

In the proof, you can see that I provide the `m3` "hint". This is the "crucial" observation, giving
a bound for the values of `m`.
Once that is done, the main stumbling block that was the inequality with the product of two
variables, suddenly becomes a finite conjunction of *linear* equations in a single natural numbers,
which is something that the automation handles easily.

### Step 2: `shift`
Next, we show (`shift`) that the set that we actually care about is just a shift of the one that
we just proved.

Again, our "main" input after we let `ext; aesop` run, is providing two existential witnesses.
By inspecting the goal at that time, we easily see that the only options are the ones that we pass
via `use`.

After that, we take care of the cases in which `m < 2` or `n < 2` in a very compact way, using
pattern-matching in the `obtain` tactic.

An alternative would be to use
```lean
  by_cases fst3 : fst < 3
  · grind
  by_cases snd3 : snd < 3
  · grind
  simp_all -- a more thorough version of `simp`, that also simplifies and uses the hypotheses.
  convert right using 2
  grind
  grind
```

### Step 3: Putting everything together
We are now ready to prove the final result: we first use `rw` to reduce to showing the equality
of two concrete finite sets of natural numbers (one shifted), and then using `ext; aesop`
to finish off.

## Conclusion
This result in particular was not so hard that it was unfeasible to try and prove it directly.
However, the issues highlighted in the comments above apply more generally and sometimes may
make the difference between being able to formalise a result or not.
-/

lemma easy : {(m, n) : ℕ × ℕ | (m + 1) * (n + 1) < 4} =
    {(0, 0), (0, 1), (0, 2), (1, 0), (2, 0)} := by
  -- Use `ext`ensionality: two sets are equal if they have the same elements
  ext ⟨m, n⟩
  -- `aesop` is a general tactic that tries (mostly) reversible operations.
  aesop -- I would recommend replacing `aesop` by the output of `aesop?`.
  -- Add a hint that `m` is bounded.
  have m3 : m < 3 := by
    -- `grind` is another general purpose tactic that often allows to avoid tedious proofs
    grind
  -- `interval_cases m` makes Lean realise that `m` only has finitely many options
  -- and returns separate goals for each case.
  -- the `<;>` tactic combinator applies the tactic on the right to each goal
  -- produced by the tactic on the left.
  -- Effectively here we are solving by `grind` each possible case for `m`.
  interval_cases m <;> grind

lemma shift : (· + (3, 3)) '' {(m, n) : ℕ × ℕ | (m + 1) * (n + 1) < 4} =
    {(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4} := by
  ext
  aesop -- I would recommend replacing `aesop` by the output of `aesop?`.
  -- `use` is a way of providing a witness to an existential.
  use fst - 3, snd - 3
  -- This is somewhat compact: `obtain ... := fst` means do a case analysis on `fst`.
  -- Since `fst` is a natural number, the only "cases" are that `fst` could be
  -- `0, 1, 2, fst + 3`.
  -- The fact that we separate exactly these cases is communicated by the
  -- 3 underscores `_` separated by the "or" symbol `|`.
  -- We then use `grind`, except that the final case is outside of scope:
  -- `try tactic` means "if the tactic works, use it, otherwise, do nothing".
  obtain _|_|_|fst := fst <;> try grind
  -- Similar case split on `snd`, except that now `grind` solves all resulting goals.
  obtain _|_|_|snd := snd <;> grind

example : {(m, n) : Nat × Nat | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4} =
    {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} := by
  -- We use the lemmas that we proved.
  rw [← shift, easy]
  -- And then the common `ext; aesop` combination finishes the proof.
  ext
  aesop

open Polynomial

-- Defining the polynomial f(x) = x^n(a-bx)^n / n! (as a polynomial, not a function)
noncomputable def f_n (n : ℕ) (a : ℕ) (b : ℕ) : Polynomial ℚ :=
  (C (1 / (n.factorial : ℚ))) * (X^n * (C (a : ℚ) - C (b : ℚ) * X)^n)

noncomputable def nfact_f_n (n a b : ℕ) : Polynomial ℚ :=
  C (n.factorial : ℚ) * f_n n a b

-- Checking n!f(x) has integer coefficients
lemma nfact_f_n_integral_coeffs :
    ∀ (k a b n : ℕ), ∃ z : ℤ, (nfact_f_n n a b).coeff k = (z : ℚ) := by
  intros k a b n
  obtain ⟨f, hf⟩ := nfact_f_n_integral a b n
  rw [hf]  --  `simp_all` suffices here
  simp







-- Let's prove that there is a *polynomial* with integer coefficients that works.
lemma nfact_f_n_integral (a b n : ℕ) :
    ∃ f : ℤ[X], nfact_f_n n a b = f.map (algebraMap ℤ ℚ) := by
  unfold nfact_f_n f_n
  use X ^ n * (C (a : ℤ) - C (b : ℤ) * X) ^ n
  ext
  simp [field]

namespace first_attempt

lemma nfact_f_n_integral (a b n : ℕ) :
    ∃ f : ℤ[X], nfact_f_n n a b = f.aeval X := by
  unfold nfact_f_n f_n
  use X ^ n * (C (a : ℤ) - C (b : ℤ) * X) ^ n
  ext
  simp [field]

-- Checking n!f(x) has integer coefficients
lemma nfact_f_n_integral_coeffs :
    ∀ (k a b n : ℕ), ∃ z : ℤ, (nfact_f_n n a b).coeff k = (z : ℚ) := by
  intros k a b n
  obtain ⟨f, hf⟩ := nfact_f_n_integral a b n
  rw [hf]  --  `simp_all` suffices here
  use f.coeff k
  rw?  -- notice the appearence of `algebraMap`
  sorry

end first_attempt
