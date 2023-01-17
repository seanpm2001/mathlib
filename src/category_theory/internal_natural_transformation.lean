/-
Copyright (c) 2023 Zach Murray. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Zach Murray.
-/
import category_theory.category.basic
import category_theory.limits.shapes.pullbacks
import category_theory.internal_category.basic
import category_theory.internal_functor.basic
open category_theory
open category_theory.limits

/-!
# Internal Natural Transformations

Defines natural transformations between two functors of internal categories.
-/

noncomputable theory

namespace category_theory

universes v u
variables {𝔸 : Type u} [category.{v} 𝔸]

section

variables {𝔻 𝔼 : internal_category 𝔸}

structure internal_nat_trans_struct (F G : 𝔻 ⟹ 𝔼) :=
(app : 𝔻.Obj ⟶ 𝔼.Arr)
(resp_source' : app ≫ 𝔼.s = F.obj . obviously)
(resp_target' : app ≫ 𝔼.t = G.obj . obviously)

open internal_nat_trans_struct

restate_axiom internal_nat_trans_struct.resp_source'
restate_axiom internal_nat_trans_struct.resp_target'
attribute [simp] internal_nat_trans_struct.resp_source
attribute [simp] internal_nat_trans_struct.resp_target

@[ext]
protected lemma internal_nat_trans_struct.ext {F G : 𝔻 ⟹ 𝔼} {α β : internal_nat_trans_struct F G}
  (h : α.app = β.app) : α = β :=
begin
cases α,
cases β,
congr',
end

lemma internal_nat_trans_struct_lift₁ {F G : 𝔻 ⟹ 𝔼} (α : internal_nat_trans_struct F G) :
  F.arr ≫ 𝔼.t = (𝔻.t ≫ α.app) ≫ 𝔼.s := by simp

structure internal_nat_trans (F G : 𝔻 ⟹ 𝔼)
extends internal_nat_trans_struct F G :=
(naturality' : pullback.lift F.arr (𝔻.t ≫ app) (by simp) ≫ 𝔼.c =
               pullback.lift (𝔻.s ≫ app) G.arr (by simp) ≫ 𝔼.c . obviously)

open internal_nat_trans

restate_axiom internal_nat_trans.naturality'

@[ext]
protected lemma internal_nat_trans.ext {F G : 𝔻 ⟹ 𝔼} {α β : internal_nat_trans F G}
  (h : α.app = β.app) : α = β :=
begin
cases α,
cases β,
congr',
exact category_theory.internal_nat_trans_struct.ext h,
end

def vcomp {F G H : 𝔻 ⟹ 𝔼}
  (α : internal_nat_trans F G) (β : internal_nat_trans G H) :
  internal_nat_trans F H :=
{
  app := pullback.lift α.app β.app (by simp) ≫ 𝔼.c,
  naturality' := by {
    calc pullback.lift F.arr (𝔻.t ≫ pullback.lift α.app β.app (by simp) ≫ 𝔼.c) (by simp) ≫ 𝔼.c
          = pullback.lift (pullback.lift F.arr (𝔻.t ≫ α.app) (by simp) ≫ 𝔼.c) (𝔻.t ≫ β.app) (by simp) ≫ 𝔼.c : by simp [pullback.lift_comp]
      ... = pullback.lift (𝔻.s ≫ α.app) (pullback.lift (𝔻.s ≫ β.app) H.arr (by simp) ≫ 𝔼.c) (by simp) ≫ 𝔼.c : by simp [α.naturality, β.naturality]
      ... = pullback.lift (𝔻.s ≫ pullback.lift α.app β.app (by simp) ≫ 𝔼.c) H.arr (by simp) ≫ 𝔼.c            : by {simp only [← category.assoc, ← pullback.lift_comp], rw pullback.lift_assoc}
  }
}

namespace internal_nat_trans

protected def id (F : 𝔻 ⟹ 𝔼) :
  internal_nat_trans F F :=
{
  app := F.obj ≫ 𝔼.e,
}

@[simp]
protected lemma id_app' (F : 𝔻 ⟹ 𝔼) : (internal_nat_trans.id F).app = F.obj ≫ 𝔼.e := rfl

end internal_nat_trans

lemma vcomp_app {F G H : 𝔻 ⟹ 𝔼} (α : internal_nat_trans F G) (β : internal_nat_trans G H) :
  (vcomp α β).app = pullback.lift α.app β.app (by simp) ≫ 𝔼.c := rfl


@[simp]
lemma vcomp_id_comp {F G : 𝔻 ⟹ 𝔼} (α : internal_nat_trans F G) :
  vcomp (internal_nat_trans.id F) α = α :=
begin
ext,
simp only [vcomp, internal_nat_trans.id, ← α.resp_source, category.assoc],
simp,
end

@[simp]
lemma vcomp_id_comp_app {F G : 𝔻 ⟹ 𝔼} (α : internal_nat_trans F G) :
  pullback.lift (internal_nat_trans.id F).app α.app (by simp) ≫ 𝔼.c = α.app :=
begin
rw ← vcomp_app,
simp,
end

@[simp]
lemma vcomp_comp_id {F G : 𝔻 ⟹ 𝔼} (α : internal_nat_trans F G) :
  vcomp α (internal_nat_trans.id G) = α :=
begin
ext,
simp only [vcomp, internal_nat_trans.id, ← α.resp_target, category.assoc],
simp,
end

@[simp]
lemma vcomp_comp_id_app {F G : 𝔻 ⟹ 𝔼} (α : internal_nat_trans F G) :
  pullback.lift α.app (internal_nat_trans.id G).app (by simp) ≫ 𝔼.c = α.app :=
begin
simp only [← vcomp_app],
simp,
end

@[simp]
lemma vcomp_assoc {F G H K : 𝔻 ⟹ 𝔼}
  (α : internal_nat_trans F G) (β : internal_nat_trans G H) (η : internal_nat_trans H K) :
  vcomp (vcomp α β) η = vcomp α (vcomp β η) :=
begin
ext,
dunfold vcomp,
simp,
end

end

end category_theory
