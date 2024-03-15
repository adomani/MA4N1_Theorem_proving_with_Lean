#  Workaround for finding some information about non-finishing `aesop`

[Source](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/non-finishing.20.60aesop.3F.60/near/404962767)

```lean
import Mathlib.Tactic
import Aesop

--  add the following line to your files
@[aesop 1% unsafe apply] def sorryeh {A} : A := sorry

example {n : ℕ} (h : (n = 0 ∧ False) ∨ n = 1) : False := by
  aesop?
  sorry
```

This makes `aesop` try, as a last resource, `sorryeh`.
Since `sorryeh` produces a term of *anything*, it will close all goals.

The `1% unsafe` is a way of communicating to `aesop` that it should really only use this when all else fails.

The likely conclusion is that `aesop` will close all goals, either because it is really successful,
or because, after doing its thing, it will apply `sorryeh`.

Thus, `aesop?` will always print something!

And, if the last step was `apply sorryeh`, we simply erase it and we should be where we wanted to be!
