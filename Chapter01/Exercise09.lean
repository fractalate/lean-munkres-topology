import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset

-- DeMorgan's Law for arbitrary unions.
theorem MunkresCh1Ex9PartA {U} (AA : Set (Set U))
  : (⋃ A ∈ AA, A)ᶜ = ⋂ A ∈ AA, Aᶜ := by
  simp

-- DeMorgan's Law for arbitrary intersections.
theorem MunkresCh1Ex9PartB {U} (AA : Set (Set U))
  : (⋂ A ∈ AA, A)ᶜ = ⋃ A ∈ AA, Aᶜ := by
  simp
