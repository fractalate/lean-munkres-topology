import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset


-- Unsure whether this is true.
theorem MunkresCh1Ex5PartA {U} (x : U) (AA : Set (Set U))
    : ∃ A ∈ AA, x ∈ ⋃₀ AA → x ∈ A := by
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
