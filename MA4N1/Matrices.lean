import Mathlib.Tactic

#allow_unused_tactic Lean.Parser.Tactic.«done»

/-!
#  Matrices in Lean

As you know, the entries of a matrix are indexed by two natural numbers,
representing the rows and columns of the matrix.

In `Mathlib`, the formalisation of matrices starts with a function that takes
two "indices" and returns the corresponding entry of the matrix.
Thus, we should first of all decide where the entries live.
If we allow all natural numbers, then we are going to get (doubly) infinite matrices --
this may not be so good!

So, instead, we can start with two finite sets and
use these finite sets to index the entries of our matrix.

But... how do we get a finite set?
Of course, in many ways!

A convenient one is to use `Fin`.
`Fin` takes a natural number `n` and returns `Fin n`, the finite set `{0, 1,..., n-1}`.
-/

open Matrix

example {n : ℕ} : Nat.card (Fin n) = n := by
  simp
--  `Nat.card` is the cardinality of a set, as a natural number.  Hover over it to see the documentation.

--  A way of writing the 2×2 identity matrix (this ends up not being the most straightforward way!)
example : (fun i j : Fin 2 => if i = j then 1 else 0 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.one.one := by
  -- read below for some details on these tactics
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> rfl
/-
The proof above is useful since it displays some of the automation that exists.
Also, something along those lines would have to happen if you wanted to prove some facts about your own
kind of matrix for which there are no lemmas yet.

Tactics used in the proof
* `ext` is short for extensionality.
  If the goal is something that can be proved by checking it separately on all elements of "something",
  then `ext` introduces those variables and asks you to prove the result for the introduced elements.
  In this case, an identity between matrices holds if it holds entrywise.
  `ext` takes, optionally, the names of the new variables that it introduces.
* `fin_cases <var>` takes as input a variable that Lean can verify ranges in a finite set.
  It creates as many goals as the number of elements of this set and in each it specializes the variable to
  one of its possibilities.
  In this case, `i` and `j` are in `Fin 2`, so Lean replaces each by `0` or `1`.
* `<;>` is not really a tactic, but a "tactic combinator": it tells Lean to run the tactic the follows
  `<;>` on all the goals created by the tactic that precedes it.
  In this case, we want to have all possibilities of `i` and `j` instantiated as `0` or `1`.
* `simp` you should know: simplify and hope for the best!
* `rfl` is short for reflexivity.
  This is basically telling Lean to check that the goal is "just true" or "true by definition".
  Equality is somewhat hard, since the computer has a very very strict notion of what counts as equal.
  Mathematicians tend to have a very loose notion of equality and will happily identify very very different notions.
  `rfl` is a way for the computer to accept a little more than its very strict notion.
  In this case, the goals that `rfl` proves are
  (recall that the rows and columns of our matrices are indexed by `0` and `1`)
  * `1 = One.one 0 0` -- the `(0,0)` entry of the matrix `One.one` (the identity matrix) is `1`, and
  * `0 = One.one 0 1` -- the `(0,1)` entry of the matrix `One.one` (the identity matrix) is `0`.

Note that `ext; simp` is a fairly common pattern of proof for results that hold elementwise.
In this case, we are simply inserting the "case-split" `fin_cases`, since the arguments for different entries
depend on the actual entries.
-/

--  Better to use the dedicated notation!
example : !![1, 0; 0, 1] = 1 := by exact one_fin_two.symm -- found with `exact?`

--  Also, let's make `one_fin_two` into a `simp` lemma.
attribute [simp] one_fin_two

/-
Hopefully the notation is self-explanatory:
we can provide a matrix to Lean by using the following syntax
* the matrix entries are contained in a `!![...]` block;
* rows are inserted by comma-separated `,` entries;
* consecutive rows are separated by a colon `;`.

The syntax allows rectangular (i.e. not necessarily square) matrices.
For legibility (especially if we have bigger matrices), we could write the `2 × 2` identity matrix as
-/
#check !![1, 0;
          0, 1]
/-
although, admittedly, for such a small matrix, the single-line expression might be clearer.
-/

--  let's prove a not fully trivial result about matrices!
example {n : ℕ} : !![1, 1; 0, 1] ^ n = !![1, n; 0, 1] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ih]
    simp
  done

/-
The `!![...]` notation is useful for writing "explicit" matrices,
but if you have a "generic" `m × n` matrix it will not help.
In fact, how *do* we write a generic `m × n`?
-/

variable {m n : Type} (M : Matrix m n ℝ)
/-
`m` and `n` are *arbitrary* sets, `M` is a real-valued matrix
whose rows are indexed by `m` and
whose columns are indexed by `n`.

This is maybe not so common: rows and columns are often *finite*... here we go!
-/
variable [Fintype m] [Fintype n]
/-
Finiteness is a property of the set that is expressed by a typeclass.
In fact, by several typeclasses, but `Fintype` may be the one that is most useful for us.
-/
