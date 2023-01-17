/-
Copyright (c) 2023 Zach Murray. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Zach Murray.
-/
import category_theory.category.basic
import category_theory.limits.shapes.pullbacks
import category_theory.internal_category.basic
import category_theory.internal_functor.basic
import category_theory.internal_functor.category
import category_theory.internal_natural_transformation
import category_theory.isomorphism
open category_theory
open category_theory.limits

/-!
# Whiskering of Internal Functors and Internal Natural Transformations

Defines the left and right whiskerings of functors and natural transformations of internal
categories.

Given functors `F : 𝔻 ⟹ 𝔼` and `G,H : 𝔼 ⟹ 𝔽`, and a natural transformation
`α : internal_nat_trans G H`,
we define the natural transformation
`internal_whisker_left F α : internal_nat_trans (F › G) (F › H)` to have components
`F.obj ≫ α.app`.

Similarly, given functors `F,G : 𝔻 ⟹ 𝔼` and `H : 𝔼 ⟹ 𝔽`, and a natural transformation
`α : internal_nat_trans F G`, we define the natural transformation
`internal_whisker_right α H : internal_nat_trans (F › H) (G › H)` to have components
`α.app ≫ H.arr`.
-/

noncomputable theory

namespace category_theory

universes v u
variables {𝔸 : Type u} [category.{v} 𝔸]

section

variables {𝔻 𝔼 𝔽 : internal_category 𝔸}

@[simps]
def internal_whisker_left (F : 𝔻 ⟹ 𝔼) {G H : 𝔼 ⟹ 𝔽} (α : internal_nat_trans G H) :
  internal_nat_trans (F › G) (F › H) :=
{
  app := F.obj ≫ α.app,
  naturality' := by {
    simp only [← category.assoc, F.resp_source, F.resp_target],
    simp only [category.assoc],
    calc pullback.lift (F.arr ≫ G.arr) (F.arr ≫ (𝔼.t ≫ α.app)) (by simp *) ≫ 𝔽.c
          = F.arr ≫ pullback.lift G.arr (𝔼.t ≫ α.app) (by simp *) ≫ 𝔽.c             : by simp [pullback.lift_comp]
      ... = F.arr ≫ pullback.lift (𝔼.s ≫ α.app) H.arr (by simp *) ≫ 𝔽.c             : by simp [α.naturality]
      ... = pullback.lift (F.arr ≫ (𝔼.s ≫ α.app)) (F.arr ≫ H.arr) (by simp *) ≫ 𝔽.c : by simp [pullback.lift_comp],
  },
}

@[simps]
def internal_whisker_right {F G : 𝔻 ⟹ 𝔼} (α : internal_nat_trans F G) (H : 𝔼 ⟹ 𝔽) :
  internal_nat_trans (F › H) (G › H) :=
{
  app := α.app ≫ H.arr,
  resp_source' := by {
    simp only [category.assoc, ← H.resp_source],
    rw ← category.assoc,
    obviously,
  },
  resp_target' := by {
    simp only [category.assoc, ← H.resp_target],
    rw ← category.assoc,
    obviously,
  },
  naturality' := by {
    simp only [← category.assoc, internal_functor_comp.arr],
    have h : (F.arr ≫ H.arr) ≫ 𝔽.t = ((𝔻.t ≫ α.app) ≫ H.arr) ≫ 𝔽.s,
      by {simp only [category.assoc, symm H.resp_target, symm H.resp_source],
          simp only [← category.assoc], obviously},
    calc pullback.lift (F.arr ≫ H.arr) ((𝔻.t ≫ α.app) ≫ H.arr) h ≫ 𝔽.c
          = (pullback.lift F.arr (𝔻.t ≫ α.app) (by simp) ≫ arr_x_arr H) ≫ 𝔽.c : by simp
      ... = (pullback.lift F.arr (𝔻.t ≫ α.app) (by simp) ≫ 𝔼.c) ≫ H.arr : by {rw category.assoc, dunfold arr_x_arr, rw [← H.resp_comp, ← category.assoc]}
      ... = pullback.lift (𝔻.s ≫ α.app) G.arr _ ≫ 𝔼.c ≫ H.arr           : by simp only [α.naturality, category.assoc]
      ... = pullback.lift (𝔻.s ≫ α.app) G.arr _ ≫ arr_x_arr H ≫ 𝔽.c     : by {dunfold arr_x_arr, rw H.resp_comp}
      ... = pullback.lift ((𝔻.s ≫ α.app) ≫ H.arr) (G.arr ≫ H.arr) _ ≫ 𝔽.c : by {rw ← category.assoc, simp [-category.assoc]},
  },
}

end

end category_theory
