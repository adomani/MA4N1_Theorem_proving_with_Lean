import Mathlib.Tactic.Recall
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

#allow_unused_tactic Lean.Parser.Tactic.done

section Origine_della_domanda

/-!
[Fonte](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Nilpotent.20implies.20trace.20zero/near/381540803)
-/

variable (R : Type _) [CommRing R] {n : Type _} [DecidableEq n] [Fintype n]

/-! Questa è una domanda che è apparsa sulla [chat di Zulip su Lean](https://leanprover.zulipchat.com/). -/

-- I don't suppose anyone has a proof of this lying around:
-- Fairly sure `IsReduced` suffices (at least in commutative case) but
-- I'll settle for a proof over a field.
example [IsReduced R] {M : Matrix n n R} (h : IsNilpotent M) :
    M.trace = 0 := sorry

/-!
La domanda è molto precisa, ma lascia qualche domanda irrisolta.

* È vero il risultato?
* Si può eliminare l'ipotesi `IsReduced R`?
* Si può indebolire `CommRing R` a `Ring R`?  O perfino a `Semiring R`?

Possibili reazioni iniziali.

* Su un camp, il risultato è vero: la traccia è la somma degli autovalori e
  tutti gli autovalori di una matrice nilpotente sono `0`.
* Su un dominio di integrità, stesso risultato, poiché un dominio si immerge nel suo campo delle frazioni.
* La presenza di elementi nilpotenti è chiaramente un problema: se `ε ∈ R` è non nullo e nilpotente,
  allora la matrice `1 × 1` `(ε)` ha traccia che non è nulla!

E se cambiamo la conclusione a `IsNilpotent M.trace`?
Poiché la domanda assume `IsReduced R`, se la traccia è nilpotente allora è automaticamente nulla.
E inoltre, il controesempio con un anello con nilpotenti non è in contraddizione immediata con l'enunciato!

Può essere che il risultato qui sotto sia vero?
Osserviamo che `IsReduced` non è più un'ipotesi e
la conclusione è che la traccia è *nilpotente*, invece di essere nulla.
L'anello continua a essere un `CommRing` (ovvero, è *commutativo*).
-/
example {M : Matrix n n R} (h : IsNilpotent M) :
    IsNilpotent M.trace := sorry

/-!
#  Entra il risultato principale

Circa un mese prima che la domanda qui sopra fosse proposta, questo risultato era arrivato in `Mathlib`:
-/

#check Polynomial.isUnit_iff_coeff_isUnit_isNilpotent

/-!
Proviamo così.

Assumiamo che `M` sia nilpotente: `M ^ N = 0`.

Iniziamo con le identità

`I = I - (tM) ^ (N + 1)`
`  = (I - tM)(I + tM + ... + (tM) ^ N)`.

Calcoliamo i determinanti dei due lati e usiamo che il determinante di un prodotto è il prodotto
dei determinanti.

Deduciamo che il determinante di `(I - tM)` è un polinomio invertibile.
Pertanto, tutti i suoi coefficienti di grado positivo sono nilpotenti.
-/

end Origine_della_domanda

section CommRing

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

open Polynomial

recall Matrix.charpolyRev (M : Matrix n n R) := det (1 - (X : R[X]) • M.map C)

namespace Matrix

variable (M : Matrix n n R)

--  Il risultato che dimostreremo nel file di esercizi.
example {N : ℕ} (hM : M ^ N = 0) {n : ℕ} (hn : n ≠ 0) : IsNilpotent ((charpolyRev M).coeff n) := by
  sorry
  done

end Matrix

end CommRing

/-!
#  Extra credit

Possiamo indebolire `CommRing R` a `Ring R`?
-/

variable {R : Type*} [Ring R] {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n R)
open Matrix

example (hM : IsNilpotent M) : IsNilpotent M.trace := sorry
