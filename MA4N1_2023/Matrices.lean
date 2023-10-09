import Mathlib.Tactic

open Matrix

/-

As you know, the entries of a matrix are indexed by two natural numbers,
representing the rows and columns of the matrix.

In `Mathlib`, the formalisation of matrices starts with a function that takes
two "indices" and returns the corresponding entry of the matrix.
Thus, we should first of all decide where the entries live.
If we allow all natural numbers, then we are going to get (doubly) infinite matrices --
this may not be so good!

So, instead, we can start with two finite sets and
use these finite sets to index the entries of our matrix.

So... how do we get a finite set?

Of course, in many ways!
A convenient one is to use `Fin`.
`Fin` is a Type that takes a natural number `n` and returns `Fin n`,
the finite set `{0, 1,..., n-1}`.
-/

example {n : ℕ} : Nat.card (Fin n) = n := by
  simp

--  A way of writing the 2×2 identity matrix (this ends up not being the most straightforward way!)
example : (fun i j : Fin 2 => if i = j then 1 else 0 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.one.one := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> rfl
/-
The proof above is useful since it displays some of the automation that exists.
Also, something along those lines would have to happen if you wanted to prove some facts about your own
kind of matrix for which there are no lemmas yet.
-/

--  Better to use the dedicated notation!
example : !![1, 0; 0, 1] = 1 := by simp

example {n : ℕ} : !![1, 1; 0, 1] ^ n = !![1, n; 0, 1] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    simp
  done
