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
  isOpen_inter (x : Set a) (y : Set a) hx hy := by
    have : (x = univ) ∨ (x = ∅) := hx
    show (x ∩ y = univ) ∨ (x ∩ y = ∅)
    cases hx with
    | inr _ =>
      have : x = ∅ := by assumption
      suffices h : x ∩ y = ∅ from Or.inr h
      have : x ∩ y = ∅ := by simp[*]
      exact this
    | inl h =>
        have : x = univ := h
        show (x ∩ y = univ) ∨ (x ∩ y = ∅)
        have : x ∩ y = y := by simp[*]
        have : (y = univ) ∨ (y = ∅) := hy
        cases hy with
        | inr _ =>
          have : y = ∅ := by assumption
          suffices h2 : x ∩ y = ∅ from Or.inr h2
          have : x ∩ y = ∅ := by simp[*]
          exact this
        | inl _ =>
          have : y = univ := by assumption
          suffices h2 : x ∩ y = univ from Or.inl h2
          have : x ∩ y = univ := by simp[this, h]
          exact this
  isOpen_unionₛ s f := by
    have : Set (Set a) := s
    have : ∀ (t : Set a), t ∈ s → t = univ ∨ t = ∅ := f
    show (⋃₀ s = univ) ∨ (⋃₀ s = ∅)
    exact byCases
      (fun h : univ ∈ s => by
        suffices h2 : ⋃₀ s = univ from Or.inl h2
        have : univ ⊆ ⋃₀ s := le_supₛ h
        simp[*, Iff.mp Set.univ_subset_iff])
      (fun h : ¬(univ ∈ s) =>
        suffices h2 : ⋃₀ s = ∅ from Or.inr h2
        have h3 : ∀ t, t ∈ s -> t ⊆ ∅ := by
          intro t p
          have : Set a := t
          have : t ∈ s := p
          have : (t = univ) ∨ (t = ∅) := f t p
          cases this with
          | inl _ => simp[*] at p
          | inr _ => simp[*]
        have : ⋃₀ s = ∅ :=
          have : ⋃₀ s ⊆ ∅ := supₛ_le h3
          Set.eq_empty_of_subset_empty this
        this)

-- samples

section nat_is_open
  def nat : Set Nat := univ
  example : IsOpen nat := Or.inl rfl
end nat_is_open

section _1_2_3_is_not_open
  def s : Set Nat := {0, 1, 2, 3}
  example : ¬IsOpen s := by
    intro h
    have : s = univ ∨ s = ∅ := h
    cases h with
    | inl x =>
        have : s = univ := x
        have : ¬ 4 ∈ s := by simp[s]
        simp[x] at *
    | inr x =>
        have : s = ∅ := x
        have : 1 ∈ s := by simp[s]
        simp[x] at *

end _1_2_3_is_not_open

end Indiscret
