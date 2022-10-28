/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.groupoid
import category_theory.is_connected

/-!
This file defines a few basic properties of groupoids.
-/

namespace category_theory

namespace groupoid

variables (C : Type*) [groupoid C]

section thin

/-- A groupoid is graph-like if it has no parallel arrows. -/
def is_thin := ∀ (c d : C), subsingleton (c ⟶ d)

lemma is_thin_iff : is_thin C ↔ ∀ (c : C), subsingleton (c ⟶ c) :=
begin
  refine ⟨λ h c, h c c, λ h c d, subsingleton.intro $ λ f g, _⟩,
  haveI := h d,
  calc f = f ≫ (inv g ≫ g) : by simp only [inv_eq_inv, is_iso.inv_hom_id, category.comp_id]
     ... = f ≫ (inv f ≫ g) : by congr
     ... = g               : by simp only [inv_eq_inv, is_iso.hom_inv_id_assoc],
end

end thin

section disconnected

/-- A subgroupoid is disconnected if it only has loops. -/
def is_disconnected := ∀ (c d : C), (c ⟶ d) → c = d

end disconnected

end groupoid

end category_theory
