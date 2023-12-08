import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace TPwL_autoImplicits

/-!
#  Setting `autoImplicit` true or false

Lean's default set-up involves a feature called `autoImplicit`.
This means that if you start typing code in a fresh `Lean` file,
`Lean` will try hard to make sense of what you are doing,
assuming *you* know exactly what you are doing!

Click on this link for an quick explanation

https://live.lean-lang.org/#code=--set_option%20autoImplicit%20false%0A--set_option%20relaxedAutoImplicit%20false%0A%0A%23check%20Nat.succ%0A%0Aexample%20%3A%20Nat.succ%20n%20%E2%89%A0%200%20%3A%3D%20by%0A%20%20sorry%0A%20%20done%0A%0Aexample%20%3A%20Nat.succ%20n_longName%20%E2%89%A0%200%20%3A%3D%20by%0A%20%20sorry%0A%20%20done%0A%0Adef%20mySucc%20(n%20%3A%20%E2%84%95)%20%3A%3D%20n%20%2B%201%0A%0A%23eval%20mySucc%203

The conclusion is that
* `set_option autoImplicit false` makes sure that `Lean` interprets as
  syntax errors all typos;
* `set_option relaxedAutoImplicit false` makes sure that `Lean` interprets as
  syntax errors all typos, except the *one-letter ones*.

My view on `autoImplicit`s is mixed:
* on the one hand, it is convenient to not have to introduce each symbol,
  and it feels good automation when `Lean` "gets it";
* on the other hand, it is *very* easy to actually have typos when you are
  writing code and not receiving feedback about this, since `Lean` interpreted
  your typo as an implicitly defined variable can be annoying.

For this reason, you may have noticed that, in most of the live-coding that happened
in the lectures, I ended up writing `set_option autoImplicit false` near the beginning
of the file.

##  Change `autoImplicit` defaults

Over the week-end, I have changed the default for this project:
`autoImplicit`s are now disabled by default on `MA4N1_2023`.

*Warning.*
`Lean` projects will likely have `autoImplicit`s on by default.

In order to change the `autoImplicit` setting for a whole project,
you should edit `lakefile.lean`.

Find the part of the code beginning with

`package «my_project» where [...]`

or
`package «my_project» := { [...]`

and convert it to
```lean
package «my_project» where
  -- add any package configuration options here
  moreServerArgs := #[ "-DautoImplicit=false" ]
```

Notice that `set_option [whatever]` are *scoped*:
if you only want to have some `autoImplicit` behaviour in some part of the code,
but not another, this would work.
-/

section autoImplicit_on

set_option autoImplicit true

--  useful `autoImplicit`: "gets" what `n` means
example : Nat.succ n ≠ 0 := by
  exact? says exact Nat.succ_ne_zero n
  done

--  useful `autoImplicit`: "gets" what `V` means
variable (G1 : SimpleGraph V)

#check G1
#check G1.Adj

--  unhelpful `autoImplicit`: misinterprets a typo
variable (G2 : simpleGraph)

--  and creates a weird environment with misleading errors.
#check G2

/--
error: invalid field notation, type is not of the form (C ...) where C is a constant
  G2
has type
  simpleGraph
-/
#guard_msgs in
#check G2.Adj

/--
error: application type mismatch
  G2.Adj
argument
  G2
has type
  simpleGraph : Sort ?u.121
but is expected to have type
  SimpleGraph ?m.124 : Type ?u.123
---
info: (sorryAx (SimpleGraph ?m.124) true).Adj : ?m.124 → ?m.124 → Prop
-/
#guard_msgs in
#check SimpleGraph.Adj G2

end autoImplicit_on

section what_is_n?
-- uncomment this `variable` to resolve the `unknown identifier 'n'` error below.
--variable {n : ℕ}

example : Nat.succ n ≠ 0 := by
  exact Nat.succ_ne_zero n
  done

end what_is_n?

/-!

Another potential issue is capitalization.

Lean is very much aware of capitalization!
Names that differ only in their capitalization are considered *different* by Lean.

In the old `Lean 3` days, the convention for almost every name was that they would
be written in all lower-case letters and replacing spaces (` `) by underscores (`_`).

Conventions changed in `Lean 4`, so now you see a big variation on upper/lower-case,
spaces and underscores in declaration names.
There are some [naming conventions](https://leanprover-community.github.io/contribute/naming.html),
but the rules are not completely straightforward and the (deprecated) habit from `Lean 3` is hard
to loose.

-/

open scoped Pointwise

lemma Nat.Prime.divisors_mul (n : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    Nat.divisors (p * n) = Nat.divisors p * Nat.divisors n := by
  ext a
  rw [Finset.mem_mul]
  --  the `says` combinator is essentially just a way of making the code more readable
  --  and maintainable.  For example `tac? says tac [...]` means:
  --  * we used the tactic `tac?` that produces some output like a `Try this`;
  --  * the output of `Try this` is `tac [...]`.
  --  This has several benefits:
  --  * the output of `tac?` may be very long and cluttered, but the call `tac?`
  --    itself may be very clear
  --  * the execution of `tac [...]` may be much faster than `tac` or `tac?`
  --  * if we change a lemma in the output of `tac?`, but `tac?` still works,
  --    we only have to re-run `tac?`, instead of having to find out what had
  --    generated `tac [...]`.
  simp? [hp.divisors, dvd_mul, Nat.dvd_prime hp] says
    simp only [Nat.mem_divisors, Nat.isUnit_iff, dvd_mul, Nat.dvd_prime hp, exists_and_left,
      exists_eq_or_imp, one_mul, exists_eq_right', exists_eq_left, ne_eq, mul_eq_zero, hp.divisors,
      Finset.mem_singleton, Finset.mem_insert, exists_eq_right]
  -- `aesop` can finish the proof from here
  -- below is a proof "by hand": let's see how we might discover it.
  constructor <;> intro h
  · rcases h with ⟨h | ⟨h, hh, rfl⟩, j⟩
    · simp [h, not_or.mp j]
    · simp [hh, not_or.mp j]
  · rcases h with ⟨h, j⟩ | ⟨b, ⟨bn, n0⟩, rfl⟩
    · simp [h, j]
      exact? says exact Nat.Prime.ne_zero hp
    · simp [bn, n0, Nat.Prime.ne_zero hp]
  done

end TPwL_autoImplicits
