import Mathlib.Topology.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real

open Topology
open Set
open CategoryTheory

namespace top
structure TopSpace where
  carrier : Type u
  top : TopologicalSpace carrier

structure Mor (source : TopSpace) (dest : TopSpace) where
  f : source.carrier -> dest.carrier
  con : @Continuous source.carrier dest.carrier
          source.top dest.top f

instance : Category TopSpace where
  Hom x y := Mor x y
  id x := Mor.mk id
            (@continuous_id x.carrier x.top)
  comp := by
    intro x y z f g
    have fxy : Mor x y := f
    have fyz : Mor y z := g
    apply Mor.mk (fyz.f ∘ fxy.f)
            (@Continuous.comp
                x.carrier y.carrier z.carrier
                x.top y.top z.top
                fyz.f fxy.f
                fyz.con fxy.con)

namespace sample

-- is there an easier way to define topR?
def topR : TopologicalSpace ℝ :=
  TopCat.topologicalSpaceUnbundled (TopCat.of ℝ)
def top : TopSpace := TopSpace.mk ℝ topR
def f : top ⟶ top := 𝟙 top
def g : top ⟶ top :=
  Mor.mk id (@continuous_id ℝ topR)
def h : top ⟶ top := f ≫ g

end sample
end top
