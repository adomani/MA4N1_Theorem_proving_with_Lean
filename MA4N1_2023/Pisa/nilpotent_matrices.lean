import Mathlib.Tactic.Recall
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

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

theorem IsUnit_charpolyRev_of_IsNilpotent (hM : IsNilpotent M) : IsUnit (charpolyRev M) := by
  rcases hM with ⟨N, hM⟩
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

end Matrix
