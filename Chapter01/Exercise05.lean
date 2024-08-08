import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset


-- Note for future attempts: I'd like to express the statements in the original
-- element-based notation used in the book, e.g., ∃ A ∈ AA, x ∈ ⋃₀ AA → x ∈ A.


-- This statement
--   ∃ A ∈ AA, x ∈ ⋃₀ AA → x ∈ A
-- is not generally true. If AA = {{1}, {2}}, then ⋃₀ AA = {1, 2} and
-- {1, 2} is neither a subset of {1} nor {2}.
-- The statement can also be written
--   ∃ A ∈ AA, ⋃₀ AA ⊆ A
-- which we do here.
theorem MunkresCh1Ex5PartA1 {U} [h : Nontrivial U]
    : ∃ AA : Set (Set U), ¬(∃ A ∈ AA, ⋃₀ AA ⊆ A) := by
  obtain ⟨a, ⟨b, anb⟩⟩ := h
  use {{a}, {b}}
  simp
  push_neg
  constructor
  rw [@ne_comm]
  assumption
  assumption

-- This statement
--   ∃ A ∈ AA, x ∈ ⋃₀ AA → x ∈ A
-- has the converse
--   ∃ A ∈ AA, x ∈ A → x ∈ ⋃₀ AA
-- which is not generally true. If AA is empty, then there is no such A to
-- satisfy the statement. We work with an equivalent statement
--   ∃ A ∈ AA, A ⊆ ⋃₀ AA
theorem MunkresCh1Ex5PartA2 {U} (AA : Set (Set U))
    : ∃ A ∈ AA, A ⊆ ⋃₀ AA := by
  sorry


-- The statement
--   ∀ A ∈ AA, x ∈ ⋃₀ AA → x ∈ A
-- is not generally true. If AA = {{1}, {2}}, then ⋃₀ AA = {1, 2} and
-- {1, 2} is not a subset of {1} nor {2}.
-- The statement can also be written
--   ∀ A ∈ AA, ⋃₀ AA ⊆ A
-- which we do here.
theorem MunkresCh1Ex5PartB {U} [h : Nontrivial U]
    : ∃ AA : Set (Set U), ¬(∀ A ∈ AA, ⋃₀ AA ⊆ A) := by
  obtain ⟨a, ⟨b, anb⟩⟩ := h
  use {{a}, {b}}
  simp
  push_neg
  intro
  assumption

-- The statement
--   ∃ A ∈ AA, x ∈ ⋂₀ AA → x ∈ A
-- is true when AA is nonempty. When AA is empty, the statement is not true
-- since no A ∈ AA exists. We work with the equivalent statement for the case
-- where AA is non-empty.
--   ∃ A ∈ AA, ⋂₀ AA ⊆ A.
theorem MunkresCh1Ex5PartC {U} (AA : Set (Set U)) [h : Nonempty AA]
    : ∃ A ∈ AA, ⋂₀ AA ⊆ A := by
  obtain ⟨A, h2⟩ := h
  use A
  constructor
  assumption
  intro x xNAA
  apply xNAA at h2
  assumption

-- The statement
--   ∀ A ∈ AA, x ∈ ⋂₀ AA → x ∈ A
-- is true. We work with the equivalent statement
--   ∀ A ∈ AA, ⋂₀ AA ⊆ A.
theorem MunkresCh1Ex5PartD {U} (AA : Set (Set U))
    : ∀ A ∈ AA, ⋂₀ AA ⊆ A := by
  intro A AAA
  intro x xNAA
  apply xNAA at AAA
  assumption
