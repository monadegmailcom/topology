import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Rat.Basic
import Std.Data.Rat.Basic

open Set
open CategoryTheory

namespace pointed_set

structure Obj where
  carrier : Type u
  set : Set carrier
  point : carrier
  prop : point ∈ set

structure Mor (x : Obj) (y : Obj) where
  fxy : x.carrier -> y.carrier
  prop : MapsTo fxy x.set y.set
  prop2 : fxy x.point = y.point

instance : Category Obj where
  Hom := Mor
  id x := Mor.mk id (Set.mapsTo_id x.set) (by simp)
  comp := by
    intro x y z f g
    let fxz := g.fxy ∘ f.fxy
    let prop : fxz x.point = z.point := by calc
      fxz x.point = (g.fxy ∘ f.fxy) x.point := rfl
      _ = g.fxy (f.fxy x.point) := rfl
      _ = g.fxy y.point := by rw [f.prop2]
      _ = z.point := by rw [g.prop2]
    apply Mor.mk fxz (MapsTo.comp g.prop f.prop) prop

namespace samples

abbrev n := Obj.mk ℕ univ 2 (by simp)
abbrev z := Obj.mk ℤ univ 4 (by simp)
abbrev q := Obj.mk ℚ univ (mkRat 4 3) (by simp)
def f : n ⟶ z := Mor.mk (fun x => 2 * x) (by simp) (by norm_num)
def g : z ⟶ q := Mor.mk (fun x => mkRat x 3) (by simp) (by simp)
def h : n ⟶ q := f ≫ g

end samples
end pointed_set
