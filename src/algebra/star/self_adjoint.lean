/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.star.basic
import group_theory.subgroup.basic

/-!
# Self-adjoint and skew-adjoint elements of a star additive group

This file defines `self_adjoint R` (resp. `skew_adjoint R`), where `R` is a star additive group,
as the additive subgroup containing the elements that satisfy `star x = x` (resp. `star x = -x`).
This includes, for instance, (skew-)Hermitian operators on Hilbert spaces.

## Implementation notes

* When `R` is a `star_module R₂ R`, then `self_adjoint R` has a natural
  `module (self_adjoint R₂) (self_adjoint R)` structure. However, doing this literally would be
  undesirable since in the main case of interest (`R₂ = ℂ`) we want `module ℝ (self_adjoint R)`
  and not `module (self_adjoint ℂ) (self_adjoint R)`. We solve this issue by adding the typeclass
  `[has_trivial_star R₃]`, of which `ℝ` is an instance (registered in `data/real/basic`), and then
  add a `[module R₃ (self_adjoint R)]` instance whenever we have
  `[module R₃ R] [has_trivial_star R₃]`. (Another approach would have been to define
  `[star_invariant_scalars R₃ R]` to express the fact that `star (x • v) = x • star v`, but
  this typeclass would have the disadvantage of taking two type arguments.)

## TODO

* Define `λ z x, z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `conj_act` for groups), and then state the fact that `self_adjoint R` is
  invariant under it.

-/

variables (R : Type*) {A : Type*}

/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
def self_adjoint [add_group R] [star_add_monoid R] : add_subgroup R :=
{ carrier := {x | star x = x},
  zero_mem' := star_zero R,
  add_mem' := λ x y (hx : star x = x) (hy : star y = y),
                show star (x + y) = x + y, by simp only [star_add x y, hx, hy],
  neg_mem' := λ x (hx : star x = x), show star (-x) = -x, by simp only [hx, star_neg] }

/-- The skew-adjoint elements of a star additive group, as an additive subgroup. -/
def skew_adjoint [add_comm_group R] [star_add_monoid R] : add_subgroup R :=
{ carrier := {x | star x = -x},
  zero_mem' := show star (0 : R) = -0, by simp only [star_zero, neg_zero],
  add_mem' := λ x y (hx : star x = -x) (hy : star y = -y),
                show star (x + y) = -(x + y), by rw [star_add x y, hx, hy, neg_add],
  neg_mem' := λ x (hx : star x = -x), show star (-x) = (- -x), by simp only [hx, star_neg] }

variables {R}

namespace self_adjoint

section add_group
variables [add_group R] [star_add_monoid R]

lemma mem_iff {x : R} : x ∈ self_adjoint R ↔ star x = x :=
by { rw [←add_subgroup.mem_carrier], exact iff.rfl }

@[simp, norm_cast] lemma star_coe_eq {x : self_adjoint R} : star (x : R) = x := x.prop

instance : inhabited (self_adjoint R) := ⟨0⟩

lemma bit0_mem {x : R} (hx : x ∈ self_adjoint R) : bit0 x ∈ self_adjoint R :=
by simp only [mem_iff, star_bit0, mem_iff.mp hx]

end add_group

section ring
variables [ring R] [star_ring R]

instance : has_one (self_adjoint R) := ⟨⟨1, by rw [mem_iff, star_one]⟩⟩

@[simp, norm_cast] lemma coe_one : ↑(1 : self_adjoint R) = (1 : R) := rfl

instance [nontrivial R] : nontrivial (self_adjoint R) := ⟨⟨0, 1, subtype.ne_of_val_ne zero_ne_one⟩⟩

lemma one_mem : (1 : R) ∈ self_adjoint R := by simp only [mem_iff, star_one]

lemma bit1_mem {x : R} (hx : x ∈ self_adjoint R) : bit1 x ∈ self_adjoint R :=
by simp only [mem_iff, star_bit1, mem_iff.mp hx]

lemma conjugate {x : R} (hx : x ∈ self_adjoint R) (z : R) : z * x * star z ∈ self_adjoint R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, mul_assoc]

lemma conjugate' {x : R} (hx : x ∈ self_adjoint R) (z : R) : star z * x * z ∈ self_adjoint R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, mul_assoc]

end ring

section comm_ring
variables [comm_ring R] [star_ring R]

instance : has_mul (self_adjoint R) :=
⟨λ x y, ⟨(x : R) * y, by simp only [mem_iff, star_mul', star_coe_eq]⟩⟩

@[simp, norm_cast] lemma coe_mul (x y : self_adjoint R) : ↑(x * y) = (x : R) * y := rfl

instance : has_pow (self_adjoint R) ℕ :=
⟨λ x n, ⟨(x : R) ^ n, by simp only [mem_iff, star_pow, star_coe_eq]⟩⟩

@[simp, norm_cast] lemma coe_pow (x : self_adjoint R) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n := rfl

instance : comm_ring (self_adjoint R) :=
function.injective.comm_ring _ subtype.coe_injective
  (self_adjoint R).coe_zero coe_one (self_adjoint R).coe_add coe_mul
  (self_adjoint R).coe_nsmul (self_adjoint R).coe_zsmul coe_npow

end comm_ring

section field

variables [field R] [star_ring R]

instance : has_inv (self_adjoint R) :=
{ inv := λ x, ⟨(x.val)⁻¹, by simp only [mem_iff, star_inv', star_coe_eq, subtype.val_eq_coe]⟩ }

@[simp, norm_cast] lemma coe_inv (x : self_adjoint R) : ↑(x⁻¹) = (x : R)⁻¹ := rfl

instance : has_div (self_adjoint R) :=
{ div := λ x y, ⟨x / y, by simp only [mem_iff, star_div', star_coe_eq, subtype.val_eq_coe]⟩ }

@[simp, norm_cast] lemma coe_div (x y : self_adjoint R) : ↑(x / y) = (x / y : R) := rfl

instance : has_pow (self_adjoint R) ℤ :=
{ pow := λ x z, ⟨x ^ z, by simp only [mem_iff, star_zpow₀, star_coe_eq, subtype.val_eq_coe]⟩ }

@[simp, norm_cast] lemma coe_zpow (x : self_adjoint R) (z : ℤ) : ↑(x ^ z) = (x : R) ^ z := rfl

instance : field (self_adjoint R) :=
function.injective.field _ subtype.coe_injective
  (self_adjoint R).coe_zero coe_one (self_adjoint R).coe_add coe_mul coe_inv coe_div
  (self_adjoint R).coe_nsmul (self_adjoint R).coe_zsmul coe_npow coe_zpow

end field

section has_scalar
variables [has_star R] [has_trivial_star R] [add_group A] [star_add_monoid A]

instance [has_scalar R A] [star_module R A] : has_scalar R (self_adjoint A) :=
⟨λ r x, ⟨r • x, by rw [mem_iff, star_smul, star_trivial, star_coe_eq]⟩⟩

@[simp, norm_cast] lemma coe_smul [has_scalar R A] [star_module R A] (r : R) (x : self_adjoint A) :
  ↑(r • x) = r • (x : A) := rfl

instance [monoid R] [mul_action R A] [star_module R A] : mul_action R (self_adjoint A) :=
function.injective.mul_action coe subtype.coe_injective coe_smul

instance [monoid R] [distrib_mul_action R A] [star_module R A] :
  distrib_mul_action R (self_adjoint A) :=
function.injective.distrib_mul_action (self_adjoint A).subtype subtype.coe_injective coe_smul

end has_scalar

section module
variables [has_star R] [has_trivial_star R] [add_comm_group A] [star_add_monoid A]

instance [semiring R] [module R A] [star_module R A] : module R (self_adjoint A) :=
function.injective.module R (self_adjoint A).subtype subtype.coe_injective coe_smul

end module

end self_adjoint

namespace skew_adjoint

section add_group
variables [add_comm_group R] [star_add_monoid R]

lemma mem_iff {x : R} : x ∈ skew_adjoint R ↔ star x = -x :=
by { rw [←add_subgroup.mem_carrier], exact iff.rfl }

@[simp, norm_cast] lemma star_coe_eq {x : skew_adjoint R} : star (x : R) = -x := x.prop

instance : inhabited (skew_adjoint R) := ⟨0⟩

lemma bit0_mem {x : R} (hx : x ∈ skew_adjoint R) : bit0 x ∈ skew_adjoint R :=
by rw [mem_iff, star_bit0, mem_iff.mp hx, bit0, bit0, neg_add]

end add_group

section ring
variables [ring R] [star_ring R]

lemma conjugate {x : R} (hx : x ∈ skew_adjoint R) (z : R) : z * x * star z ∈ skew_adjoint R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

lemma conjugate' {x : R} (hx : x ∈ skew_adjoint R) (z : R) : star z * x * z ∈ skew_adjoint R :=
by simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

end ring

section has_scalar
variables [has_star R] [has_trivial_star R] [add_comm_group A] [star_add_monoid A]

instance [monoid R] [distrib_mul_action R A] [star_module R A] : has_scalar R (skew_adjoint A) :=
⟨λ r x, ⟨r • x, by rw [mem_iff, star_smul, star_trivial, star_coe_eq, smul_neg r]⟩⟩

@[simp, norm_cast] lemma coe_smul [monoid R] [distrib_mul_action R A] [star_module R A]
  (r : R) (x : skew_adjoint A) : ↑(r • x) = r • (x : A) := rfl

instance [monoid R] [distrib_mul_action R A] [star_module R A] :
  distrib_mul_action R (skew_adjoint A) :=
function.injective.distrib_mul_action (skew_adjoint A).subtype subtype.coe_injective coe_smul

instance [semiring R] [module R A] [star_module R A] : module R (skew_adjoint A) :=
function.injective.module R (skew_adjoint A).subtype subtype.coe_injective coe_smul

end has_scalar

end skew_adjoint
