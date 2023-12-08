import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open Matrix

/-!
#  Esercizi sulle matrici nilpotenti

In questo file, suggerisce una dimostrazione del risultato seguente:

Se la matrice `M` è nilpotente, allora tutti i coefficienti del polinomio
`det (1 - M * X)` sono nilpotenti, tranne il coefficiente di `X ^ 0`.

In particolare, la traccia della matrice `M` è nilpotente.
-/

variable {R n : Type*} [CommRing R] [DecidableEq n] [Fintype n]

open Matrix in
example (M : Matrix n n R) {N : ℕ} (hM : M ^ N = 0) {n : ℕ} (hn : n ≠ 0) :
    IsNilpotent ((charpolyRev M).coeff n) := by
  sorry
  done

/-!
#  Preliminari

Iniziamo con qualche lemma semplice, per imparare un po' come interagire con matrici,
determinanti e altre cose.

###  Alcune identità in anelli

`Mathlib` contiene già molte identità di base tra elementi di anelli.

Cominciamo con una identità facile.
-/
example (x y : R) (n : ℕ) : x - y ∣ x ^ n - y ^ n := by
  exact? says exact sub_dvd_pow_sub_pow x y n
  done

/-!
Tuttavia, il risultato qui sopra non è quello che vogliamo!

Nella nostra applicazione, l'anello `R` sarà realmente l'anello delle matrici a coefficienti in `R`.
Il risultato di prima non lo possiamo usare, perché assume che `R` è commutativo.

La versione non-commutativa, in cui assumiamo che `x` e `y` commutano è anche già in `Mathlib`.

In questo esempio, `x` e `y` sono elementi di una anello qualsiasi
-/
example {A : Type*} [Ring A] {x y : A} (h : Commute x y) (n : ℕ) :
    x - y ∣ x ^ n - y ^ n := by
  exact? says exact Commute.sub_dvd_pow_sub_pow h n
  done

/-!
###  Determinanti

Nella nostra dimostrazione, usiamo anche qualche determinante.

Il determinante di una matrice quadrata è `Matrix.det`
(poiché abbiamo scritto `open Matrix` più sopra, possiamo riferirci con `det` a `Matrix.det`).

Come ci possiamo aspettare, `det` è una funzione che associa a una matrice a coefficienti in `R`
un elemento di `R`.
-/
#check det

example : det (1 : Matrix n n R) = 1 := by
  exact? says exact det_one
  done

/-! Fate attenzione alle coercizioni (`↑`) (coersions) che facciamo inserire a Lean con le
ascrizioni (type-ascriptions) esplicite.
-/
example (a b : ℕ) : ((a * b : ℕ) : Matrix n n R) = (a * b) := by
  exact? says exact Nat.cast_mul a b
  done

/-! Le matrici sono costruite a partire dalle funzioni con due argomenti.
La tattica `ext` può essere utile per dimostrare il risultato seguente.
-/
example : (fun i j => if i = j then 1 else 0 : Matrix (Fin 2) (Fin 2) R) =
    (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  split_ifs with h
  · simp [h]
  · exact? says exact (one_apply_ne h).symm
  done
/-!
_Nota._
Questa non è la maniera più diretta di definire la matrice identità: nell'esercizio
successivo vediamo una maniera migliore.
-/
example : !![1, 0; 0, 1] = 1 := by
  simp
  done

/-!
Per il prossimo esempio, può essere utile usare `det_smul`.
-/
#check det_smul

example : det (2 : Matrix n n R) = 2 ^ (Fintype.card n) := by
  convert det_smul 1 (2 : R)
  · rw [← @algebraMap_eq_smul]
    ext i j
    simp
  · rw [det_one, mul_one]
  done

/-!
###  Unità

Non useremo quasi nulla sulle unità, ma appariranno nell'equivalenza

`i coefficienti non-costanti di un polynomio sono nilpotenti ↔ il polinomio è invertibile`

Il comando `#print` qui sotto non mostra un'informazione importante, che però possiamo
ottenere mettendo il cursore sulla `u` in `∃ u` nell'infoview.
-/
#print IsUnit
/-!
Il tipo di `u` è `Mˣ = Units M`, il tipo delle unità di `M`.
-/
#print Units

/-!
Quindi, `IsUnit` è semplicemente il predicato su `R` che decide se un elemento `a` ammette o meno
un inverso destro e sinistro; ovvero se `a` "è" o meno una unità.
-/

/-- In un anello, un elemento che divide `1` è una unità. -/
example {a : R} (h : a ∣ 1) : IsUnit a := by
  exact? says exact isUnit_of_dvd_one h
  done

#help tactic apply_fun
#help tactic conv

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

section CommRing

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

open Polynomial

recall Matrix.charpolyRev (M : Matrix n n R) := det (1 - (X : R[X]) • M.map C)

namespace Matrix

variable (M : Matrix n n R)

--  why did I not find this lemma already?
theorem map_pow (N : ℕ) : (M ^ N).map C = M.map C ^ N := by
  induction N with
    | zero => simp
    | succ N => simp [pow_succ, *]
  done

theorem isUnit_charpolyRev {N : ℕ} (hM : M ^ N = 0) : IsUnit (charpolyRev M) := by
  apply isUnit_of_dvd_one
  have : 1 = 1 - ((X : R[X]) • M.map C) ^ N := by
    simp [smul_pow, ← map_pow, hM]
  apply_fun det at this
  rw [det_one] at this
  rw [this]
  obtain ⟨A, h⟩ : 1 - (X : R[X]) • M.map C ∣ 1 - ((X : R[X]) • M.map C) ^ N := by
    conv_rhs => rw [← one_pow N]
    exact Commute.sub_dvd_pow_sub_pow (by simp) N
  rw [h]
  simp [charpolyRev]
  done

example {N : ℕ} (hM : M ^ N = 0) {n : ℕ} (hn : n ≠ 0) :
    IsNilpotent ((charpolyRev M).coeff n) := by
  obtain ⟨-, h⟩ := (Polynomial.isUnit_iff_coeff_isUnit_isNilpotent).mp (isUnit_charpolyRev M hM)
  apply h _ hn
  done

end Matrix

end CommRing

/-!

#  Extra credit

Can you weaken `CommRing R` to `Ring R`?
-/

variable {R : Type*} [Ring R] {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n R)
open Matrix

theorem Matrix.isNilpotent_trace_of_isNilpotent' (hM : IsNilpotent M) :
    IsNilpotent M.trace := sorry
