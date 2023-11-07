import Mathlib.Tactic

instance : DecidablePred (@IsSquare ℕ _) :=
  fun m => decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) <| by
    simp_rw [←Nat.exists_mul_self m, IsSquare, eq_comm]

def no_three_square_product (s : Finset ℕ) : Prop :=
  ∀ x y z : s, x ≠ y ∧ y ≠ z ∧ z ≠ x → ¬IsSquare (x * y * z : ℕ)

instance : DecidablePred no_three_square_product := fun _ => Fintype.decidableForallFintype

theorem main : no_three_square_product {2, 3, 4, 5} := by
  decide
