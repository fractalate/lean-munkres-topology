import Mathlib.Tactic
import Mathlib.Data.Real.Basic

open Finset

-- Part A
--
-- Given the statement:
--
--   If x < 0, then x^2 - x > 0
--
-- write the contrapositive and converse, then determine which of the three
-- statements are true.
--
-- The contrapositive is:
--
--   If x^2 - x ≤ 0, then x ≥ 0
--
-- The converse is:
--
--   If x^2 - x > 0, then x < 0


-- The original statement given is true.
theorem MunkresCh1Ex3PartA1 {U} (x : ℝ) : x < 0 → x^2 - x > 0 := by
  sorry

-- The contrapositive must then also be true.
theorem MunkresCh1Ex3PartA2 {U} (x : ℝ) : x^2 - x ≤ 0 → x ≥ 0 := by
  sorry

-- The converse is not true. If x = 2, then x^2 - x = 2 > 0, but ¬(x < 0).
theorem MunkresCh1Ex3PartA3 {U} : ∃ x ∈ R, ¬(x^2 - x > 0 → x < 0) := by
  -- TODO: Something like this
  use 2
  simp


-- Part B
--
-- Given the statement:
--
--   If x > 0, then x^2 - x > 0
--
-- write the contrapositive and converse, then determine which of the three
-- statements are true.
--
-- The contrapositive is:
--
--   If x^2 - x ≤ 0, then x ≤ 0
--
-- The converse is:
--
--   If x^2 - x > 0, then x > 0

-- The original statement given is not true. If x = 1/2, then x > 0, but x^2 - x = -1/4.
theorem MunkresCh1Ex3PartB1 {U} : ∃ x ∈ R, ¬(x > 0 → x^2 - x > 0) := by
  -- TODO: Something like this
  use 0.5
  simp

-- The contrapositive must then also not be true.
theorem MunkresCh1Ex3PartB2 {U} : ∃ x ∈ R, ¬(x^2 - x ≤ 0 → x ≤ 0) := by
  -- TODO: Something like this
  use 0.5
  simp

-- The converse is not true. If x = -1/2, then x^2 - x = 3/4, but ¬(x > 0).
theorem MunkresCh1Ex3PartB3 {U} : ∃ x ∈ R, ¬(x^2 - x > 0 → x > 0) := by
  use -0.5
  simp
