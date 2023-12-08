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
  sorry
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
  sorry
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
  sorry
  done

/-! Fate attenzione alle coercizioni (`↑`) (coersions) che facciamo inserire a Lean con le
ascrizioni (type-ascriptions) esplicite.
-/
example (a b : ℕ) : ((a * b : ℕ) : Matrix n n R) = (a * b) := by
  sorry
  done

/-! Le matrici sono costruite a partire dalle funzioni con due argomenti.
La tattica `ext` può essere utile per dimostrare il risultato seguente.
-/
example : (fun i j => if i = j then 1 else 0 : Matrix (Fin 2) (Fin 2) R) =
    (1 : Matrix (Fin 2) (Fin 2) R) := by
  sorry
  done
/-!
_Nota._
Questa non è la maniera più diretta di definire la matrice identità: nell'esercizio
successivo vediamo una maniera migliore.
-/
example : !![1, 0; 0, 1] = 1 := by
  sorry
  done

/-!
Per il prossimo esempio, può essere utile usare `det_smul`.
-/
#check det_smul

example : det (2 : Matrix n n R) = 2 ^ (Fintype.card n) := by
  sorry
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
  sorry
  done

/-!
Assume that `M ^ N = 0`.

Start with the identities

`I = I - (tM) ^ (N + 1)`
`  = (I - tM)(I + tM + ... + (tM) ^ N)`.

Compute determinants on both sides and use that the determinant of a product is the product of the determinants.

Deduce that the determinant of `(I - tM)` is an invertible polynomial.
Therefore all its coefficients of positive degree are nilpotents.

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
  sorry
  done

/-!
Per la dimostrazione di `isUnit_charpolyRev` ho usato (tra le altre) le due tattiche
`apply_fun` e `conv`.

`apply_fun f` è utile per applicare la stessa funzione `f` ai due lati dell'uguaglianza nel
risultato principale.
Funziona anche con `apply_fun at h`, quando vogliamo applicare `f` ai due lati dell'ipotesi `h`.
La tattica cerca (un po') di trovare l'ipotesi che `f` è iniettiva.
Se non riesce a dimostrare che `f` è iniettiva, produce anche un side-goal `⊢ f.Injective`.

Qui sotto potete leggere la documentazione di `apply_fun`.
-/
#help tactic apply_fun

/-!
L'altra tattica è `conv`.
La sintassi e l'uso sonoe molto estesi, ma una forma comune è di usare `conv_lhs` o `conv_rhs`
quando il goal è un'uguaglianza.
Per esempio, `conv_lhs => rw [one_mul]` permette di riscrivere `one_mul` solo a sinistra
dell'uguale e non anche a destra.

Come prima, se volete più informazioni, la documentazione di `conv` la potete leggere qui sotto.
-/

#help tactic conv

/-!
Questo è il risultato principale: il polinomio caratteristico "rovesciato" di una matrice
nilpotente è un'unità.
-/
theorem isUnit_charpolyRev {N : ℕ} (hM : M ^ N = 0) : IsUnit (charpolyRev M) := by
  obtain ⟨A, h⟩ : 1 - (X : R[X]) • M.map C ∣ 1 - ((X : R[X]) • M.map C) ^ N := by
  sorry
  done

/-!
Per concludere e collegare il risultato precedente al fatto che i coefficienti del
polinomio caratteristico rovesciato sono nilpotenti usiamo
`Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`.
-/

#check Polynomial.isUnit_iff_coeff_isUnit_isNilpotent

example {N : ℕ} (hM : M ^ N = 0) {n : ℕ} (hn : n ≠ 0) : IsNilpotent ((charpolyRev M).coeff n) := by
  sorry
  done

end Matrix

end CommRing

/-!

#  Extra credit

Se avete finito presto gli esercizi, ecco un'ultima domanda:
se siamo interessati solo alla traccia della matrice, si può sostituire
l'ipotesi `CommRing R` con `Ring R`?

Ovvero, se una matrice a coefficienti in un anello *non-necessariamente commutativo*
è nilpotente, è vero che la traccia della matrice è nilpotente?

Qui sotto, trovate la formalizzazione dell'enunciato.
-/

variable {R : Type*} [Ring R] {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n R)
open Matrix

--  Dimostrare o trovare un controesempio.
theorem Matrix.isNilpotent_trace_of_isNilpotent' (hM : IsNilpotent M) :
    IsNilpotent M.trace := sorry
