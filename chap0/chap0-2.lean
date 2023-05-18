import Mathlib.Topology.Basic
import Mathlib.Topology.Category.Top.Basic
import Mathlib.Init.Set
import Mathlib.Data.Set.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real

open Topology
open Set
open CategoryTheory

def tt := TopologicalSpace ℝ
def tmp1 : TopCat := TopCat.of ℝ
def tmp2 : TopCat := TopCat.of ℕ
def f : tmp1 ⟶ tmp1 := 𝟙 tmp1
def hom := TopCat.bundledHom
def top : TopologicalSpace ℝ
  := TopCat.topologicalSpaceUnbundled tmp1

namespace sample

end sample
