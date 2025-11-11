import Mathlib.Tactic.IntervalCases

lemma easy : {(m, n) : ℕ × ℕ | (m + 1) * (n + 1) < 4} =
    {(0, 0), (0, 1), (0, 2), (1, 0), (2, 0)} := by
  -- Use `ext`ensionality: two sets are equal if they have the same elements
  ext ⟨m, n⟩
  -- `aesop` is a general tactic that tries (mostly) reversible operations.
  aesop -- I would recommend replacing `aesop` by the output of `aesop?`.
  -- Add a hint that `m` is bounded.
  have f10 : m < 3 := by
    -- `grind` is another general purpose tactic that often allows to avoid tedious proofs
    grind
  -- `interval_cases m` makes Lean realise that `m` only has finitely many options
  -- and returns separate goals for each case.
  -- the `<;>` tactic combinator applies the tactic on the right to each goal
  -- produced by the tactic on the left.
  -- Effectively here we are solving by `grind` each possible case for `m`.
  interval_cases m <;> grind

lemma shift : (· + (3, 3)) '' {(m, n) : ℕ × ℕ | (m + 1) * (n + 1) < 4} =
    {(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4} := by
  ext
  aesop -- I would recommend replacing `aesop` by the output of `aesop?`.
  -- `use` is a way of providing a witness to an existential.
  use fst - 3, snd - 3
  -- This is somewhat compact: `obtain ... := fst` means do a case analysis on `fst`.
  -- Since `fst` is a natural number, the only "cases" are that `fst` could be
  -- `0, 1, 2, fst + 3`.
  -- The fact that we separate exactly these cases is communicated by the
  -- 3 underscores `_` separated by the "or" symbol `|`.
  -- We then use `grind`, except that the final case is outside of scope:
  -- `try tactic` means "if the tactic works, use it, otherwise, do nothing".
  obtain _|_|_|fst := fst <;> try grind
  -- Similar case split on `snd`, except that now `grind` solves all resulting goals.
  obtain _|_|_|snd := snd <;> grind

example : {(m, n) : Nat × Nat | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4} =
    {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} := by
  -- We use the lemmas that we proved.
  rw [← shift, easy]
  -- And then the common `ext; aesop` combination finishes the proof.
  ext
  aesop
