* Fix MA4N1_2023 file, so that it builds
* Check branch `typeclasses` and de-duplicate
  * L04_definitions: L157-174
  * L06_typeclass: L201-218


Add troubleshooting for `exact?` producing invalid code?

/-- We found a contradiction using an *implicit* natural number `n`. -/
theorem implicitContra {n : Nat} : False := sorry

example (n : Nat) : False := by
  -- exact? says exact implicitContra
  -- but it does not work!
  -- This does: notice the explicit passing of the implicit argument `n`.
  exact implicitContra (n := n)

/-- We found a contradiction using an *explicit* integer `n`. -/
theorem explicitContra (n : Int) : False := sorry

example (n : Int) : False := by
  exact?

/-!
##  A short explanation of why `exact?` produced code that is not working.

Internally, uses `apply` with lemmas that look like they might be useful.
These lemmas may leave side-goals that `exact?` tries to solve with `solve_by_elim`.

In the example above, `apply implicitContra`, leaves a goal of `⊢ Nat` that
`solve_by_elim` can solve, since *it* uses the local context and
is aware of the `n : Nat` assumption.

However, when `exact?` reconstructs the "one-line `exact ???`",
it only tries to fill in the *explicit* inputs of the lemma that works,
so it does not provide the (in this case obvious) implicit argument.

In the second case, `apply` finds `explicitContra`
(notice that now we are dealing with integers, since otherwise `exact?` would pick
up again `implicitContra`, as it appears earlier!).
Once the side-goal `n : Int` is solved, `exact?` is faced with providing an
`exact explicitContra` output.
This now requires passing an argument to `explicitContra` and `exact?` provides one.

*Conclusion*.
Sometimes, when `exact?` returns code that is not working, it is bug.

More often, though, when `exact?` returns code that is not working,
it is an indication that something else went wrong earlier!

In the example above, the issue was created by the fact that the value `n : Nat` in
`implicitContra` could not be inferred from the later expressions:
neither the remaining assumptions of the lemma (there were none!), nor the conclusion
(`False`) mention `n`.
In this case, you should seriously think whether you really want to leave `n` implicit
or make it explicit.
-/
