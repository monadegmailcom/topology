import Mathlib.Topology.Basic
import Mathlib.Topology.Category.Top.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real

open Topology
open Set
open CategoryTheory

structure TopSpace where
  carrier : Type u
  top : TopologicalSpace carrier
  basepoint : carrier

structure Mor (x : TopSpace) (y : TopSpace) where
  fxy : x.carrier -> y.carrier
  con : @Continuous x.carrier y.carrier
          x.top y.top fxy
  prop : fxy x.basepoint = y.basepoint

instance : Category TopSpace where
  Hom x y := Mor x y
  id x := Mor.mk id (@continuous_id x.carrier x.top)
            (by simp)
  comp := by
    intro x y z f g
    let fxz := g.fxy ∘ f.fxy
    let prop : fxz x.basepoint = z.basepoint := by calc
      fxz x.basepoint = (g.fxy ∘ f.fxy) x.basepoint := rfl
      _ = g.fxy (f.fxy x.basepoint) := rfl
      _ = g.fxy y.basepoint := by rw [f.prop]
      _ = z.basepoint := by rw [g.prop]

    apply Mor.mk (g.fxy ∘ f.fxy)
            (@Continuous.comp
                x.carrier y.carrier z.carrier
                x.top y.top z.top
                g.fxy f.fxy
                g.con f.con)
            prop

namespace sample

-- is there an easier way to define topR?
def topR : TopologicalSpace ℝ :=
  TopCat.topologicalSpaceUnbundled (TopCat.of ℝ)
def top : TopSpace := TopSpace.mk ℝ topR 1
def f : top ⟶ top := 𝟙 top
def g : top ⟶ top :=
  Mor.mk id (@continuous_id ℝ topR) (by simp)
def h : top ⟶ top := f ≫ g

end sample
