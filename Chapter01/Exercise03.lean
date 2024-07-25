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
theorem MunkresCh1Ex3PartA1 (x : ℝ) : x < 0 → x^2 - x > 0 := by
  intro xlt0
  simp
  have x2g0 : x^2 > 0 := by
    exact sq_pos_of_neg xlt0
  exact gt_trans x2g0 xlt0

-- The contrapositive must then also be true.
theorem MunkresCh1Ex3PartA2 (x : ℝ) : x^2 - x ≤ 0 → x ≥ 0 := by
  intro x2lex
  simp at x2lex
  have x2ge0 : x^2 ≥ 0 := by
    exact sq_nonneg x
  exact ge_trans x2lex x2ge0

-- The converse is not true. If x = 2, then x^2 - x = 2 > 0, but ¬(x < 0).
theorem MunkresCh1Ex3PartA3 : ∃ x : ℝ, ¬(x^2 - x > 0 → x < 0) := by
  use 2
  simp
  linarith


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
theorem MunkresCh1Ex3PartB1 : ∃ x : ℝ, ¬(x > 0 → x^2 - x > 0) := by
  use 1/2
  simp
  refine inv_le_inv_of_le ?inequality.ha ?inequality.h
  linarith
  linarith

-- The contrapositive must then also not be true.
theorem MunkresCh1Ex3PartB2 : ∃ x : ℝ, ¬(x^2 - x ≤ 0 → x ≤ 0) := by
  use 1/2
  simp
  refine inv_le_inv_of_le ?inequality.ha ?inequality.h
  linarith
  linarith

-- The converse is not true. If x = -1/2, then x^2 - x = 3/4, but ¬(x > 0).
theorem MunkresCh1Ex3PartB3 : ∃ x : ℝ, ¬(x^2 - x > 0 → x > 0) := by
  use -0.5
  simp
  ring
  constructor

  refine div_pos ?h.left.ha ?h.left.hb
  exact three_pos
  exact four_pos

  refine one_div_nonneg.mpr ?h.right.a
  exact zero_le_two
