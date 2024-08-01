import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset


-- This statement
--   ∃ A ∈ AA, x ∈ ⋃₀ AA → x ∈ A
-- is not generally true. If AA = {{1}, {2}}, then ⋃₀ AA = {1, 2} and
-- {1, 2} is neither a subset of {1} nor {2}.
-- The statement can also be written
--   ∃ A ∈ AA, ⋃₀ AA ⊆ A
-- which we do here.
theorem MunkresCh1Ex5PartA {U} [h : Nontrivial U]
    : ∃ AA : Set (Set U), ¬(∃ A ∈ AA, ⋃₀ AA ⊆ A) := by
  obtain ⟨a, ⟨b, anb⟩⟩ := h
  use {{a}, {b}}
  simp
  push_neg
  constructor
  rw [@ne_comm]
  assumption
  assumption

-- TODO: This is tricky, but this is the form I'd like to prove for part A.
-- The (x : U) needed to make the expression x ∈ ⋃₀ AA → x ∈ A work
-- syntactically means that x is some pre-existing element that must be
-- contended with during the proof. Is there some way to create the x where
-- it's needed, instead of as a precondition to the theorem?
theorem MunkresCh1Ex5PartA2 {U} [h : Nontrivial U] (x : U)
    : ∃ AA : Set (Set U), ¬(∃ A ∈ AA, x ∈ ⋃₀ AA → x ∈ A) := by
  sorry

-- Unsure whether this is true.
theorem MunkresCh1Ex5PartB {U} (x : U) (AA : Set (Set U))
    : ∀ A ∈ AA, x ∈ ⋃₀ AA → x ∈ A := by
  sorry

-- Unsure whether this is true.
theorem MunkresCh1Ex5PartC {U} (x : U) (AA : Set (Set U))
    : ∃ A ∈ AA, x ∈ ⋂₀ AA → x ∈ A := by
  sorry

-- Unsure whether this is true.
theorem MunkresCh1Ex5PartD {U} (x : U) (AA : Set (Set U))
    : ∃ A ∈ AA, x ∈ ⋂₀ AA → x ∈ A := by
  sorry
