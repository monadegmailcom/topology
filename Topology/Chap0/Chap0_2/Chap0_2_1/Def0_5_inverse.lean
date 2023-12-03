import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Opposites

import Topology.Chap0.Chap0_2.Chap0_2_1.Ex0_3_opposite

open CategoryTheory

/- why is mathlib4 using typeclasses like this instead of plain properties
   like below?
class IsLeftInvertible [Category C] {X : C} {Y : C} (f : X ⟶ Y) where
  prop : ∃ g : Y ⟶ X, f ≫ g = 𝟙 X
class IsRightInvertible [Category C] {X : C} {Y : C} (f : X ⟶ Y) where
  prop : ∃ g : Y ⟶ X, g ≫ f = 𝟙 Y
-/

def is_left_inverse_of' [Category C] {X : C} {Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  : Prop := g ≫ f = 𝟙 Y

-- the infix version shadows the original version
infix:50 "is_left_inverse_of" => is_left_inverse_of'

def is_left_invertible [Category C] {X : C} {Y : C} (f : X ⟶ Y) : Prop
  := ∃ g, g is_left_inverse_of f

postfix:50 "is_left_invertible" => is_left_invertible

theorem left_inv_comp
  [Category C] {X : C} {Y : C} {Z : C}
  {f : X ⟶ Y} {f' : Y ⟶ X} {g : Y ⟶ Z} {g' : Z ⟶ Y}
  (p : f' is_left_inverse_of f) (q : g' is_left_inverse_of g)
  : (g' ≫ f') is_left_inverse_of (f ≫ g) := calc
    (f ≫ g) ≫ (g' ≫ f') = f ≫ (g ≫ g') ≫ f' := by simp
    _ = f ≫ 𝟙 Y ≫ f' := by rw[q]
    _ = f ≫ f' := by simp
    _ = 𝟙 X := by rw[p]

def is_right_inverse_of' [Category C] {X : C} {Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  : Prop := f ≫ g = 𝟙 X

infix:50 "is_right_inverse_of" => is_right_inverse_of'

def is_right_invertible' [Category C] {X : C} {Y : C} (f : X ⟶ Y) : Prop
  := ∃ g, g is_right_inverse_of f

postfix:50 "is_right_invertible" => is_right_invertible'

theorem left_right_inv_mutual_eq
  [Category C] {X : C} {Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  : f is_left_inverse_of g ↔ g is_right_inverse_of f := Iff.intro id id

theorem right_inv_comp
  [Category C] {X : C} {Y : C} {Z : C}
  {f : X ⟶ Y} {f' : Y ⟶ X} {g : Y ⟶ Z} {g' : Z ⟶ Y}
  (p : g' is_right_inverse_of g) (q : f' is_right_inverse_of f)
  : (g' ≫ f') is_right_inverse_of (f ≫ g) := by
    simp[←left_right_inv_mutual_eq] at *
    apply left_inv_comp p q

theorem left_right_inv_unique [Category C] {X : C} {Y : C}
  (g : Y ⟶ X) (h : Y ⟶ X) (f : X ⟶ Y)
  (p : g is_left_inverse_of f) (q : h is_right_inverse_of f)
  : g = h := calc
    g = 𝟙 Y ≫ g := by simp
    _ = (h ≫ f) ≫ g := by rw[←q]
    _ = h ≫ (f ≫ g) := by simp
    _ = h ≫ 𝟙 X := by rw[p]
    _ = h := by simp

def is_invertible' [Category C] {X : C} {Y : C} (f : X ⟶ Y) : Prop
  := f is_left_invertible ∧ f is_right_invertible

postfix:50 "is_invertible" => is_invertible'

theorem ex_common_inv [Category C] {X : C} {Y : C} (f : X ⟶ Y) :
  f is_invertible -> ∃ g, g is_left_inverse_of f ∧ g is_right_inverse_of f := by
    intro ⟨⟨g, l_inv⟩, ⟨h, r_inv⟩⟩
    have : g = h := left_right_inv_unique g h f l_inv r_inv
    rw [this] at l_inv
    exact ⟨h, ⟨l_inv, r_inv⟩⟩

def is_inverse_of' [Category C] {X : C} {Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  : Prop := f is_left_inverse_of g ∧ f is_right_inverse_of g

infix:50 "is_inverse_of" => is_inverse_of'

theorem inv_iff_ex_inverse [Category C] {X : C} {Y : C} (f : X ⟶ Y) :
  f is_invertible ↔ ∃ g : Y ⟶ X, g is_inverse_of f := by
    apply Iff.intro
    . apply ex_common_inv f
    . intro ⟨g, ⟨p, q⟩⟩
      exact ⟨⟨g, p⟩,⟨g, q⟩⟩

-- my invertibility is the same as mathlib's isomorphism property
theorem is_invertible_iff_is_iso
  [Category C] {X : C} {Y : C} (f : X ⟶ Y) : f is_invertible ↔ IsIso f := by
  apply Iff.intro
  . apply IsIso.mk ∘ (ex_common_inv f)
  . intro ⟨g, ⟨lhs, rhs⟩⟩
    exact ⟨⟨g, lhs⟩,⟨g, rhs⟩⟩

theorem id_is_invertible [Category C] (X : C) : 𝟙 X is_invertible :=
  ⟨⟨𝟙 X, Category.comp_id (𝟙 X)⟩, ⟨𝟙 X, Category.comp_id (𝟙 X)⟩⟩

def is_isomorphic_to' [Category C] (X Y : C) : Prop
  := ∃ f : X ⟶ Y, f is_invertible

infix:50 "is_isomorphic_to" => is_isomorphic_to'

-- to be isomorphic is an equivalence relation

theorem isomorphic_is_refl [Category C] : IsRefl C is_isomorphic_to' :=
  IsRefl.mk (fun X => ⟨𝟙 X, id_is_invertible X⟩)

theorem isomorphic_is_symm [Category C] : IsSymm C is_isomorphic_to' :=
  IsSymm.mk (fun _ _ X_iso_Y =>
    have ⟨f, f_inv⟩ := X_iso_Y
    have ⟨g, ⟨p, q⟩⟩ := ex_common_inv f f_inv
    ⟨g, ⟨⟨f, q⟩, ⟨f, p⟩⟩⟩)

theorem isomorphic_is_trans [Category C] : IsTrans C is_isomorphic_to' :=
  IsTrans.mk (fun _ _ _ X_iso_Y Y_iso_Z =>
    have ⟨f, f_inv⟩ := X_iso_Y
    have ⟨f', ⟨pf, qf⟩⟩ := ex_common_inv f f_inv
    have ⟨g, g_inv⟩ := Y_iso_Z
    have ⟨g', ⟨pg, qg⟩⟩ := ex_common_inv g g_inv
    have p : f ≫ g is_left_invertible := ⟨g' ≫ f', left_inv_comp pf pg⟩
    have q : f ≫ g is_right_invertible := ⟨g' ≫ f', right_inv_comp qg qf⟩
    ⟨f ≫ g, ⟨p, q⟩⟩
    )

/- equivalences with opposite category -/
theorem is_left_inv_of_iff_op_is_right_inv_of_op
  [Category C] {X : C} {Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  : f is_left_inverse_of g ↔ f.op is_right_inverse_of g.op := by
      apply Iff.intro
      . intro p
        exact calc
          f.op ≫ g.op = (g ≫ f).op := rfl
          _ = (𝟙 Y).op := by rw [p]
      . intro p
        exact calc
          g ≫ f = (f.op ≫ g.op).unop := rfl
          _ = (𝟙 (Opposite.op Y)).unop := by rw [p]

theorem is_right_inv_of_iff_op_is_left_inv_of_op
  [Category C] {X : C} {Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  : f is_right_inverse_of g ↔ f.op is_left_inverse_of g.op := calc
      f is_right_inverse_of g ↔ g is_left_inverse_of f
        := by rw[left_right_inv_mutual_eq]
      _ ↔ g.op is_right_inverse_of f.op
        := by rw[is_left_inv_of_iff_op_is_right_inv_of_op]

theorem is_left_inv_iff_op_is_right_inv [Category C] {X : C} {Y : C}
  (f : X ⟶ Y) : f is_left_invertible ↔ f.op is_right_invertible := by
    apply Iff.intro
    . intro ⟨g, p⟩
      have : g.op is_right_inverse_of f.op
        := Iff.mp (is_left_inv_of_iff_op_is_right_inv_of_op g f) p
      exact ⟨g.op, this⟩
    . intro ⟨g, p⟩
      let g' : Y ⟶ X := g.unop
      have : g = g'.op := rfl
      rw [this] at p
      have : g' is_left_inverse_of f
        := Iff.mpr (is_left_inv_of_iff_op_is_right_inv_of_op g' f) p
      exact ⟨g', this⟩

theorem is_right_inv_iff_op_is_left_inv [Category C] {X : C} {Y : C}
  (f : X ⟶ Y) : f is_right_invertible ↔ f.op is_left_invertible := by
    apply Iff.intro
    . intro ⟨g, h⟩
      use g.op
      exact Iff.mp (is_right_inv_of_iff_op_is_left_inv_of_op g f) h
    intro ⟨g, h⟩
    let g' : Y ⟶ X := g.unop
    have h2 : g'.op = g := Quiver.Hom.op_unop g
    rw [←h2] at h
    use g'
    exact (is_right_inv_of_iff_op_is_left_inv_of_op g' f).mpr h

theorem is_inv_iff_op_is_inv [Category C] {X : C} {Y : C} (f : X ⟶ Y) :
  f is_invertible ↔ f.op is_invertible := calc
    f is_invertible ↔ f is_left_invertible ∧ f is_right_invertible := by rfl
    _ ↔ f.op is_right_invertible ∧ f.op is_left_invertible
      := by rw [is_left_inv_iff_op_is_right_inv f,
                is_right_inv_iff_op_is_left_inv f]
    _ ↔ f.op is_left_invertible ∧ f.op is_right_invertible
      := by simp[and_comm]
    _ ↔ f.op is_invertible := by rfl
