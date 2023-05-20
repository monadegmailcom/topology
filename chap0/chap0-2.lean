import Mathlib.Topology.Basic
import Mathlib.Topology.Category.Top.Basic
import Mathlib.Init.Set
import Mathlib.Data.Set.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Algebra.Module.Basic

open Topology
open Set
open CategoryTheory

namespace topSpace

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

end topSpace

namespace module

structure Obj (R : Type u) [Semiring R] where
  M : Type v
  instMonoid : AddCommMonoid M
  instModule : Module R M

structure Mor [Semiring R] (s : Obj R) (d : Obj R) where
  sd : @LinearMap _ _ _ _ (RingHom.id _) _ _
          s.instMonoid d.instMonoid s.instModule d.instModule

instance [Semiring R] : Category (Obj R) where
  Hom := Mor
  id x :=
    have idLinearMap := @LinearMap.id _ _ _ x.instMonoid x.instModule
    Mor.mk idLinearMap
  comp := by
    intro x y z f g
    have xzLinearMap := @LinearMap.comp _ _ _ _ _ _
                          _ _ _
                          x.instMonoid y.instMonoid z.instMonoid _ _ _
                          _ _ _
                          _ g.sd f.sd

    apply Mor.mk xzLinearMap

namespace samples

def module1 : Module ℕ ℕ := AddCommMonoid.natModule
def obj1 : Obj ℕ := Obj.mk ℕ _ module1

def module2 : Module ℕ ℤ := AddCommMonoid.natModule
def obj2 : Obj ℕ := Obj.mk ℤ _ module2

def f : obj1 ⟶ obj1 := 𝟙 obj1

end samples
end module
