import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Topology.Basic
import Mathlib.Init.Set
import Mathlib.Data.Set.Basic

open CategoryTheory
open Topology
open Set
-- is classical reasoning really necessary for the definition of
-- the indiscret topological space?
open Classical

namespace Discret

instance : TopologicalSpace a where
  IsOpen (_ : Set a) := True
  isOpen_univ := by simp
  isOpen_inter := by simp
  isOpen_unionₛ := by simp

-- samples
def x : Set Nat := {1, 2, 3}
example := IsOpen x
example (y : Set a) := IsOpen y

end Discret

namespace Indiscret

instance : TopologicalSpace a where
  IsOpen (x : Set a) := (x = univ) ∨ (x = ∅)
  isOpen_univ := by simp
  isOpen_inter := by
    intro x y hx hy
    cases hx with
    | inr h =>
        have : x ∩ y = ∅ := by simp[h]
        apply Or.inr
        assumption
    | inl h =>
        have : x ∩ y = y := by simp[h]
        cases hy with
        | inr h2 =>
          have : x ∩ y = ∅ := by simp[h2]
          apply Or.inr ; assumption
        | inl h2 =>
          have : x ∩ y = univ := by simp[h2, h]
          apply Or.inl ; assumption
  isOpen_unionₛ s f := byCases
    (fun h : univ ∈ s =>
      have : univ ⊆ ⋃₀ s := le_supₛ h
      have : ⋃₀ s = univ := Set.eq_univ_of_univ_subset this
      Or.inl this)
    (fun h : ¬(univ ∈ s) => byCases
      (fun h2 : s = ∅ =>
        have : ⋃₀ s = ∅ := by simp[h2]
        Or.inr this)
      (fun _ : ¬(s = ∅) =>
        have h3 : ∀ t, t ∈ s -> t ⊆ ∅ := fun t =>
          fun h4 : t ∈ s =>
            have h5 : t = univ ∨ t = ∅ := f t h4
            Or.elim h5
              (fun h6 : t = univ => by
                rw[h6] at h4
                exact absurd h4 h)
              (fun h6 => Iff.mpr Set.subset_empty_iff h6)
        have : ⋃₀ s = ∅ := by
          have h4 : ∀ t, t ∈ s -> t ⊆ ∅ := fun t =>
            fun h5 : t ∈ s => h3 t h5
          have h5 : ⋃₀ s ⊆ ∅ := supₛ_le h4
          exact Set.eq_empty_of_subset_empty h5
        Or.inr this))

-- samples
def n : Set Nat := univ
example : IsOpen n := Or.inl rfl
def s : Set Nat := setOf (fun x => x <= 3)
example : ¬IsOpen s :=
  (fun h : IsOpen s => Or.elim h
    (fun x : s = univ =>
      have h2 : ¬4 <= 3 := by simp
      have h3 : 4 ∉ s := Iff.mpr Set.nmem_setOf_iff h2
      have h4 : 4 ∈ s := by simp[x]
      absurd h4 h3)
    (fun x : s = ∅ => by
      have h2 : 1 <= 3 := by simp
      have h3 : 1 ∈ s := Iff.mpr Set.mem_setOf h2
      rw[x] at h3
      exact Iff.mp (Set.mem_empty_iff_false 1) h3))

end Indiscret
