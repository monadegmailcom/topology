import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

open CategoryTheory Set ModuleCat

instance [Ring R] (X : ModuleCat R) : Functor (ModuleCat R) (ModuleCat R) where
  obj Y := of R (X × Y)
  map {Y Z} (f : Y ⟶ Z) : of R (X × Y) ⟶ of R (X × Z)
    := LinearMap.prodMap LinearMap.id f
