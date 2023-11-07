import Mathlib.Tactic

theorem IsSquare_iff_mul_self {m : ℕ} : IsSquare m ↔ Nat.sqrt m * Nat.sqrt m = m := by
  rw [← Nat.exists_mul_self m, IsSquare]
  simp_rw [eq_comm]
  done

instance : DecidablePred (@IsSquare ℕ _) :=
  fun m => decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) IsSquare_iff_mul_self

example : IsSquare 36 := by
  decide
