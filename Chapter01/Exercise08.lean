import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset

-- If |A| = 2, then |𝒫(A)| = 4.
theorem MunkresCh1Ex8PartA {U} (A : Finset U) (h : A.card = 2) : (powerset A).card = 4 := by
  simp
  rw[h]
  simp

-- If |A| = 1, then |𝒫(A)| = 2.
theorem MunkresCh1Ex8PartB {U} (A : Finset U) (h : A.card = 1) : (powerset A).card = 2 := by
  simp
  rw[h]
  simp

-- If |A| = 3, then |𝒫(A)| = 8.
theorem MunkresCh1Ex8PartC {U} (A : Finset U) (h : A.card = 3) : (powerset A).card = 8 := by
  simp
  rw[h]
  simp

-- If |A| = 0, then |𝒫(A)| = 1.
theorem MunkresCh1Ex8PartD {U} (A : Finset U) (h : A.card = 0) : (powerset A).card = 1 := by
  simp
  rw[h]
  simp

-- 𝒫 is called the powerset of A because it's cardinality is 2 to the _power_
-- of the cardinality of the set. Notationally:
--
-- If |A| = N, then |𝒫(A)| = 2^N.
theorem MunkresCh1Ex8PartE {U} (n : ℕ) (A : Finset U) (h : A.card = n) : (powerset A).card = 2^n := by
  simp
  rw[h]
