import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Rat.Basic

open Set
open CategoryTheory

namespace set
namespace from_scratch

structure Obj where
  carrier : Type u
  prop : carrier -> Prop

structure Mor (x : Obj) (y : Obj) where
  prop : x.carrier -> y.carrier -> Prop
  p1 : ∀ x' y', prop x' y' -> x.prop x' ∧ y.prop y'
  p2 : ∀ x' y' z', prop x' y' ∧ prop x' z' -> y' = z'

instance : CategoryStruct Obj where
  Hom := Mor
  id x :=
    let prop : x.carrier -> x.carrier -> Prop :=
          fun x' y' => x.prop x' ∧ x' = y'
    have p1 : ∀ x' y', prop x' y' -> x.prop x' ∧ x.prop y' := by
      intro _ _ ⟨h1, h2⟩
      simp [←h2, h1]
    have p2 : ∀ x' y' z', prop x' y' ∧ prop x' z' -> y' = z' := by
      intro _ _ _ ⟨⟨_,h1⟩,⟨_,h2⟩⟩
      rw [←h1,←h2]
    Mor.mk prop p1 p2
  comp := by
    intro x y z f g
    let prop : x.carrier -> z.carrier -> Prop
      := fun x' z' => ∃ y', f.prop x' y' ∧ g.prop y' z'
    have p1 : ∀ x' z', prop x' z' -> x.prop x' ∧ z.prop z' := by
      intro x' z' ⟨y', ⟨h1, h2⟩⟩
      apply And.intro
      . apply And.left (f.p1 x' y' h1)
      . apply And.right (g.p1 y' z' h2)
    have p2 : ∀ x' z1' z2', prop x' z1' ∧ prop x' z2' -> z1' = z2' := by
      intro x' z1' z2' ⟨h1, h2⟩
      have ⟨y1', i1⟩ := h1
      have ⟨y2', i2⟩ := h2
      have j : y1' = y2' := f.p2 x' y1' y2' (And.intro i1.left i2.left)
      rw [←j] at i2
      apply g.p2 y1' z1' z2' (And.intro i1.right i2.right)
    apply Mor.mk prop p1 p2

theorem propext2 (h1 h2 : a -> b -> Prop) :
  (∀ ta, ∀ tb, h1 ta tb ↔ h2 ta tb) → h1 = h2 := by
    intro h
    have h3 : ∀ ta, ∀ tb, h1 ta tb = h2 ta tb := by
      intro ta tb
      apply propext (h ta tb)
    apply funext₂ h3

theorem moreq (f g : Mor x y) :
  (∀ x' y', f.prop x' y' ↔ g.prop x' y') -> f = g := by
  intro h
  have h2 : f.prop = g.prop := propext2 f.prop g.prop h

/- does not work, why?
  cases f
  cases g
  simp[h2]
 -/

  apply calc
    f = ⟨f.prop, _, _⟩ := rfl
    _ = ⟨g.prop, _, _⟩ := by simp[h2]
    _ = g := rfl

instance : Category Obj where
  comp_id := by
    intro x y f
    have h : ∀ x', ∀ y', (f ≫ 𝟙 y).prop x' y' ↔ f.prop x' y' := by
      intro x' y'
      apply Iff.intro
      . intro h
        let ⟨y2', ⟨h2, h3⟩⟩ := h
        have h4 : y2' = y' := h3.right
        rw[h4] at h2
        exact h2
      . intro h
        let idy := CategoryStruct.id y
        show ∃ y2', f.prop x' y2' ∧ idy.prop y2' y'
        let h3 : y.prop y' := (f.p1 x' y' h).right
        let h4 : y' = y' := rfl
        have h2 : idy.prop y' y' := And.intro h3 h4
        exact ⟨y', And.intro h h2⟩
    apply moreq (f ≫ 𝟙 y) f h
  id_comp := by
    intro x y f
    let idx := CategoryStruct.id x
    have h : ∀ x' y', (idx ≫ f).prop x' y' ↔ f.prop x' y' := by
      intro x' y'
      apply Iff.intro
      . intro ⟨x2', ⟨h1, h2⟩⟩
        have h3 : x' = x2' := h1.right
        rw[←h3] at h2
        exact h2
      . intro h
        let idx := CategoryStruct.id x
        show ∃ x2', idx.prop x' x2' ∧ f.prop x2' y'
        let h3 : x.prop x' := (f.p1 x' y' h).left
        let h4 : x' = x' := rfl
        have h2 : idx.prop x' x' := And.intro h3 h4
        exact ⟨x', And.intro h2 h⟩
    apply moreq (idx ≫ f) f h
  assoc f g h := by
    let lhs := (f ≫ g) ≫ h
    let rhs := f ≫ (g ≫ h)
    have h : ∀ w' z', lhs.prop w' z' ↔ rhs.prop w' z' := by
      intro w' z'
      apply Iff.intro
      . intro ⟨y', ⟨h1, h2⟩⟩
        show ∃ x', f.prop w' x' ∧ (∃ y', g.prop x' y' ∧ h.prop y' z')
        let ⟨x', ⟨h3, h4⟩⟩ := h1
        exact ⟨x', And.intro h3 ⟨y', And.intro h4 h2⟩⟩
      . intro ⟨x', ⟨h1, h2⟩⟩
        show ∃ y', (∃ x', f.prop w' x' ∧ g.prop x' y') ∧ h.prop y' z'
        let ⟨y', ⟨h3, h4⟩⟩ := h2
        exact ⟨y', And.intro ⟨x', And.intro h1 h3⟩ h4⟩
    apply moreq lhs rhs h

namespace samples

abbrev n := Obj.mk ℕ (fun _ => True)
abbrev z := Obj.mk ℤ (fun _ => True)
abbrev q := Obj.mk ℚ (fun _ => True)

def f : n ⟶ z := Mor.mk (fun x y => y = 2 * x)
  (by intros; apply And.intro; exact True.intro; exact True.intro)
  (by simp)
def g : z ⟶ q := Mor.mk (fun x y => y = x / 3)
  (by intros; apply And.intro; exact True.intro; exact True.intro)
  (by simp)
def h : n ⟶ q := f ≫ g

end samples
end from_scratch

namespace with_set_function

structure Obj where
  carrier : Type u
  s : Set carrier

structure Mor (x : Obj) (y : Obj) where
  fxy : x.carrier -> y.carrier
  p : Set.MapsTo fxy x.s y.s

instance : Category Obj where
  Hom := Mor
  id x := Mor.mk id (Set.mapsTo_id x.s)
  comp f g := Mor.mk (g.fxy ∘ f.fxy) (MapsTo.comp g.p f.p)

namespace samples

abbrev n := Obj.mk ℕ univ
abbrev z := Obj.mk ℤ univ
abbrev q := Obj.mk ℚ univ
def f : n ⟶ z := Mor.mk (fun x => 2 * x) (by simp)
def g : z ⟶ q := Mor.mk (fun x => x / 3) (by simp)
def h : n ⟶ q := f ≫ g

end samples
end with_set_function
end set
