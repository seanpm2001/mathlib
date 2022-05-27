/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.quadratic_form.isometry

/-! # Quadratic form on product and pi types

## Main definitions

* `quadratic_form.prod Q₁ Q₂`: the quadratic form constructed elementwise on a product
* `quadratic_form.pi Q`: the quadratic form constructed elementwise on a pi type

## Main results

* `quadratic_form.equivalent.prod`, `quadratic_form.equivalent.pi`: quadratic forms are equivalent
  if their components are equivalent
* `quadratic_form.nonneg_prod_iff`, `quadratic_form.nonneg_pi_iff`: quadratic forms are positive-
  semidefinite if and only if their components are positive-semidefinite.
* `quadratic_form.pos_def_prod_iff`, `quadratic_form.pos_def_pi_iff`: quadratic forms are positive-
  definite if and only if their components are positive-definite.

## Implementation notes

Many of the lemmas in this file could be generalized into results about sums of positive and
non-negative elements, and would generalize to any map `Q`  where `Q 0 = 0`, not just quadratic
forms specifically.

-/

universes u v w
variables {ι : Type*} {R : Type*} {M₁ M₂ N₁ N₂ : Type*} {Mᵢ Nᵢ : ι → Type*}
variables [ring R]
variables [add_comm_group M₁] [add_comm_group M₂] [add_comm_group N₁] [add_comm_group N₂]
variables [module R M₁] [module R M₂] [module R N₁] [module R N₂]
variables [Π i, add_comm_group (Mᵢ i)] [Π i, add_comm_group (Nᵢ i)]
variables [Π i, module R (Mᵢ i)] [Π i, module R (Nᵢ i)]

namespace quadratic_form

/-- Construct a quadratic form on a product of two modules from the quadratic form on each module.
-/
@[simps]
def prod (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) : quadratic_form R (M₁ × M₂) :=
Q₁.comp (linear_map.fst _ _ _) + Q₂.comp (linear_map.snd _ _ _)

/-- An isometry between quadratic forms generated by `quadratic_form.prod` can be constructed
from a pair of isometries between the left and right parts. -/
@[simps to_linear_equiv]
def isometry.prod {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂}
  {Q₁' : quadratic_form R N₁} {Q₂' : quadratic_form R N₂}
  (e₁ : Q₁.isometry Q₁') (e₂ : Q₂.isometry Q₂') : (Q₁.prod Q₂).isometry (Q₁'.prod Q₂'):=
{ map_app' := λ x, congr_arg2 (+) (e₁.map_app x.1) (e₂.map_app x.2),
  to_linear_equiv := linear_equiv.prod e₁.to_linear_equiv e₂.to_linear_equiv}

lemma equivalent.prod {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂}
  {Q₁' : quadratic_form R N₁} {Q₂' : quadratic_form R N₂}
  (e₁ : Q₁.equivalent Q₁') (e₂ : Q₂.equivalent Q₂') : (Q₁.prod Q₂).equivalent (Q₁'.prod Q₂'):=
nonempty.map2 isometry.prod e₁ e₂

/-- If a product is anisotropic then its components must be. The converse is not true. -/
lemma anisotropic_of_prod {R} [ordered_ring R] [module R M₁] [module R M₂]
  {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} (h : (Q₁.prod Q₂).anisotropic) :
  Q₁.anisotropic ∧ Q₂.anisotropic :=
begin
  simp_rw [anisotropic, prod_to_fun, prod.forall, prod.mk_eq_zero] at h,
  split,
  { intros x hx,
    refine (h x 0 _).1,
    rw [hx, zero_add, map_zero] },
  { intros x hx,
    refine (h 0 x _).2,
    rw [hx, add_zero, map_zero] },
end

lemma nonneg_prod_iff {R} [ordered_ring R] [module R M₁] [module R M₂]
  {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} :
  (∀ x, 0 ≤ (Q₁.prod Q₂) x) ↔ (∀ x, 0 ≤ Q₁ x) ∧ (∀ x, 0 ≤ Q₂ x) :=
begin
  simp_rw [prod.forall, prod_to_fun],
  split,
  { intro h,
    split,
    { intro x, simpa only [add_zero, map_zero] using h x 0 },
    { intro x, simpa only [zero_add, map_zero] using h 0 x } },
  { rintros ⟨h₁, h₂⟩ x₁ x₂,
    exact add_nonneg (h₁ x₁) (h₂ x₂), },
end

lemma pos_def_prod_iff {R} [ordered_ring R] [module R M₁] [module R M₂]
  {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} :
  (Q₁.prod Q₂).pos_def ↔ Q₁.pos_def ∧ Q₂.pos_def :=
begin
  simp_rw [pos_def_iff_nonneg, nonneg_prod_iff],
  split,
  { rintros ⟨⟨hle₁, hle₂⟩, ha⟩,
    obtain ⟨ha₁, ha₂⟩ := anisotropic_of_prod ha,
    refine ⟨⟨hle₁, ha₁⟩, ⟨hle₂, ha₂⟩⟩, },
  { rintro ⟨⟨hle₁, ha₁⟩, ⟨hle₂, ha₂⟩⟩,
    refine ⟨⟨hle₁, hle₂⟩, _⟩,
    rintro ⟨x₁, x₂⟩ (hx : Q₁ x₁ + Q₂ x₂ = 0),
    rw [add_eq_zero_iff' (hle₁ x₁) (hle₂ x₂), ha₁.eq_zero_iff, ha₂.eq_zero_iff] at hx,
    rwa [prod.mk_eq_zero], }
end

lemma pos_def.prod {R} [ordered_ring R] [module R M₁] [module R M₂]
  {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂}
  (h₁ : Q₁.pos_def) (h₂ : Q₂.pos_def) : (Q₁.prod Q₂).pos_def :=
pos_def_prod_iff.mpr ⟨h₁, h₂⟩

open_locale big_operators

/-- Construct a quadratic form on a family of modules from the quadratic form on each module. -/
def pi [fintype ι] (Q : Π i, quadratic_form R (Mᵢ i)) : quadratic_form R (Π i, Mᵢ i) :=
∑ i, (Q i).comp (linear_map.proj i : _ →ₗ[R] Mᵢ i)

@[simp] lemma pi_apply [fintype ι] (Q : Π i, quadratic_form R (Mᵢ i)) (x : Π i, Mᵢ i) :
  pi Q x = ∑ i, Q i (x i) :=
sum_apply _ _ _

/-- An isometry between quadratic forms generated by `quadratic_form.prod` can be constructed
from a pair of isometries between the left and right parts. -/
@[simps to_linear_equiv]
def isometry.pi [fintype ι] {Q : Π i, quadratic_form R (Mᵢ i)} {Q' : Π i, quadratic_form R (Nᵢ i)}
  (e : Π i, (Q i).isometry (Q' i)) : (pi Q).isometry (pi Q') :=
{ map_app' := λ x, by
    simp only [pi_apply, linear_equiv.Pi_congr_right_apply, linear_equiv.to_fun_eq_coe,
               isometry.coe_to_linear_equiv, isometry.map_app],
  to_linear_equiv := linear_equiv.Pi_congr_right (λ i, (e i : Mᵢ i ≃ₗ[R] Nᵢ i))}

lemma equivalent.pi [fintype ι] {Q : Π i, quadratic_form R (Mᵢ i)}
  {Q' : Π i, quadratic_form R (Nᵢ i)} (e : ∀ i, (Q i).equivalent (Q' i)) :
  (pi Q).equivalent (pi Q') :=
⟨isometry.pi (λ i, classical.choice (e i))⟩

/-- If a family is anisotropic then its components must be. The converse is not true. -/
lemma anisotropic_of_pi [fintype ι] {R} [ordered_ring R] [Π i, module R (Mᵢ i)]
  {Q : Π i, quadratic_form R (Mᵢ i)} (h : (pi Q).anisotropic) :
  ∀ i, (Q i).anisotropic :=
begin
  simp_rw [anisotropic, pi_apply, function.funext_iff, pi.zero_apply] at h,
  intros i x hx,
  classical,
  have := h (pi.single i x) _ i,
  { rw pi.single_eq_same at this,
    exact this, },
  apply finset.sum_eq_zero,
  intros j _,
  by_cases hji : j = i,
  { subst hji, rw [pi.single_eq_same, hx] },
  { rw [pi.single_eq_of_ne hji, map_zero] },
end

lemma nonneg_pi_iff [fintype ι] {R} [ordered_ring R] [Π i, module R (Mᵢ i)]
  {Q : Π i, quadratic_form R (Mᵢ i)} :
  (∀ x, 0 ≤ pi Q x) ↔ (∀ i x, 0 ≤ Q i x) :=
begin
  simp_rw [pi, sum_apply, comp_apply, linear_map.proj_apply],
  dsimp only,
  split,  -- TODO: does this generalize to a useful lemma independent of `quadratic_form`?
  { intros h i x,
    classical,
    convert h (pi.single i x) using 1,
    rw [finset.sum_eq_single_of_mem i (finset.mem_univ _) (λ j _ hji, _), pi.single_eq_same],
    rw [pi.single_eq_of_ne hji, map_zero], },
  { rintros h x,
    exact finset.sum_nonneg (λ i hi, h i (x i)), },
end

lemma pos_def_pi_iff [fintype ι] {R} [ordered_ring R] [Π i, module R (Mᵢ i)]
  {Q : Π i, quadratic_form R (Mᵢ i)} :
  (pi Q).pos_def ↔ (∀ i, (Q i).pos_def) :=
begin
  simp_rw [pos_def_iff_nonneg, nonneg_pi_iff],
  split,
  { rintros ⟨hle, ha⟩,
    intro i,
    exact ⟨hle i, anisotropic_of_pi ha i⟩, },
  { intro h,
    refine ⟨λ i, (h i).1, λ x hx, funext $ λ i, (h i).2 _ _⟩,
    rw [pi_apply, finset.sum_eq_zero_iff_of_nonneg (λ j hj, _)] at hx,
    { exact hx _ (finset.mem_univ _) },
    exact (h j).1 _ }
end

end quadratic_form
