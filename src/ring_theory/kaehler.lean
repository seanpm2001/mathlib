/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/

import ring_theory.derivation.to_square_zero
import ring_theory.ideal.cotangent
import ring_theory.is_tensor_product

/-!
# The module of kaehler differentials

## Main results

- `kaehler_differential`: The module of kaehler differentials. For an `R`-algebra `S`, we provide
  the notation `Ω[S⁄R]` for `kaehler_differential R S`.
  Note that the slash is `\textfractionsolidus`.
- `kaehler_differential.D`: The derivation into the module of kaehler differentials.
- `kaehler_differential.span_range_derivation`: The image of `D` spans `Ω[S⁄R]` as an `S`-module.
- `kaehler_differential.linear_map_equiv_derivation`:
  The isomorphism `Hom_R(Ω[S⁄R], M) ≃ₗ[S] Der_R(S, M)`.
- `kaehler_differential.quot_ker_total_equiv`: An alternative description of `Ω[S⁄R]` as `S` copies
  of `S` with kernel (`kaehler_differential.ker_total`) generated by the relations:
  1. `dx + dy = d(x + y)`
  2. `x dy + y dx = d(x * y)`
  3. `dr = 0` for `r ∈ R`
- `kaehler_differential.map`: Given a map between the arrows `R → A` and `S → B`, we have an
  `A`-linear map `Ω[A⁄R] → Ω[B⁄S]`.

## Future project

- Define a `is_kaehler_differential` predicate.
-/

section kaehler_differential

open_locale tensor_product
open algebra

variables (R S : Type*) [comm_ring R] [comm_ring S] [algebra R S]

/-- The kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`. -/
abbreviation kaehler_differential.ideal : ideal (S ⊗[R] S) :=
ring_hom.ker (tensor_product.lmul' R : S ⊗[R] S →ₐ[R] S)

variable {S}

lemma kaehler_differential.one_smul_sub_smul_one_mem_ideal (a : S) :
  (1 : S) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : S) ∈ kaehler_differential.ideal R S :=
by simp [ring_hom.mem_ker]

variables {R}

variables {M : Type*} [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M]

/-- For a `R`-derivation `S → M`, this is the map `S ⊗[R] S →ₗ[S] M` sending `s ⊗ₜ t ↦ s • D t`. -/
def derivation.tensor_product_to (D : derivation R S M) : S ⊗[R] S →ₗ[S] M :=
tensor_product.algebra_tensor_module.lift ((linear_map.lsmul S (S →ₗ[R] M)).flip D.to_linear_map)

lemma derivation.tensor_product_to_tmul (D : derivation R S M) (s t : S) :
  D.tensor_product_to (s ⊗ₜ t) = s • D t :=
rfl

lemma derivation.tensor_product_to_mul (D : derivation R S M) (x y : S ⊗[R] S) :
  D.tensor_product_to (x * y) = tensor_product.lmul' R x • D.tensor_product_to y +
    tensor_product.lmul' R y • D.tensor_product_to x :=
begin
  apply tensor_product.induction_on x,
  { rw [zero_mul, map_zero, map_zero, zero_smul, smul_zero, add_zero] },
  swap, { rintros, simp only [add_mul, map_add, add_smul, *, smul_add], rw add_add_add_comm },
  intros x₁ x₂,
  apply tensor_product.induction_on y,
  { rw [mul_zero, map_zero, map_zero, zero_smul, smul_zero, add_zero] },
  swap, { rintros, simp only [mul_add, map_add, add_smul, *, smul_add], rw add_add_add_comm },
  intros x y,
  simp only [tensor_product.tmul_mul_tmul, derivation.tensor_product_to,
    tensor_product.algebra_tensor_module.lift_apply, tensor_product.lift.tmul',
    tensor_product.lmul'_apply_tmul],
  dsimp,
  rw D.leibniz,
  simp only [smul_smul, smul_add, mul_comm (x * y) x₁, mul_right_comm x₁ x₂, ← mul_assoc],
end

variables (R S)

/-- The kernel of `S ⊗[R] S →ₐ[R] S` is generated by `1 ⊗ s - s ⊗ 1` as a `S`-module. -/
lemma kaehler_differential.submodule_span_range_eq_ideal :
  submodule.span S (set.range $ λ s : S, (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =
    (kaehler_differential.ideal R S).restrict_scalars S :=
begin
  apply le_antisymm,
  { rw submodule.span_le,
    rintros _ ⟨s, rfl⟩,
    exact kaehler_differential.one_smul_sub_smul_one_mem_ideal _ _ },
  { rintros x (hx : _ = _),
    have : x - (tensor_product.lmul' R x) ⊗ₜ[R] (1 : S)   = x,
    { rw [hx, tensor_product.zero_tmul, sub_zero] },
    rw ← this,
    clear this hx,
    apply tensor_product.induction_on x; clear x,
    { rw [map_zero, tensor_product.zero_tmul, sub_zero], exact zero_mem _ },
    { intros x y,
      convert_to x • (1 ⊗ₜ y - y ⊗ₜ 1) ∈ _,
      { rw [tensor_product.lmul'_apply_tmul, smul_sub, tensor_product.smul_tmul',
          tensor_product.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one] },
      { refine submodule.smul_mem _ x _,
        apply submodule.subset_span,
        exact set.mem_range_self y } },
    { intros x y hx hy,
      rw [map_add, tensor_product.add_tmul, ← sub_add_sub_comm],
      exact add_mem hx hy } }
end

lemma kaehler_differential.span_range_eq_ideal :
  ideal.span (set.range $ λ s : S, (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =
    kaehler_differential.ideal R S :=
begin
  apply le_antisymm,
  { rw ideal.span_le,
    rintros _ ⟨s, rfl⟩,
    exact kaehler_differential.one_smul_sub_smul_one_mem_ideal _ _ },
  { change (kaehler_differential.ideal R S).restrict_scalars S ≤ (ideal.span _).restrict_scalars S,
    rw [← kaehler_differential.submodule_span_range_eq_ideal, ideal.span],
    conv_rhs { rw ← submodule.span_span_of_tower S },
    exact submodule.subset_span }
end

/--
The module of Kähler differentials (Kahler differentials, Kaehler differentials).
This is implemented as `I / I ^ 2` with `I` the kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.
To view elements as a linear combination of the form `s • D s'`, use
`kaehler_differential.tensor_product_to_surjective` and `derivation.tensor_product_to_tmul`.

We also provide the notation `Ω[S⁄R]` for `kaehler_differential R S`.
Note that the slash is `\textfractionsolidus`.
-/
@[derive [add_comm_group, module (S ⊗[R] S)]]
def kaehler_differential : Type* := (kaehler_differential.ideal R S).cotangent

notation `Ω[`:100 S `⁄`:0 R `]`:0 := kaehler_differential R S

instance : nonempty Ω[S⁄R] := ⟨0⟩

instance kaehler_differential.module' {R' : Type*} [comm_ring R'] [algebra R' S] :
  module R' Ω[S⁄R] :=
(module.comp_hom (kaehler_differential.ideal R S).cotangent (algebra_map R' S) : _)

instance : is_scalar_tower S (S ⊗[R] S) Ω[S⁄R] :=
ideal.cotangent.is_scalar_tower _

instance kaehler_differential.is_scalar_tower_of_tower {R₁ R₂ : Type*} [comm_ring R₁] [comm_ring R₂]
  [algebra R₁ S] [algebra R₂ S] [algebra R₁ R₂] [is_scalar_tower R₁ R₂ S] :
  is_scalar_tower R₁ R₂ Ω[S⁄R] :=
begin
  convert restrict_scalars.is_scalar_tower R₁ R₂ Ω[S⁄R] using 1,
  ext x m,
  show algebra_map R₁ S x • m = algebra_map R₂ S (algebra_map R₁ R₂ x) • m,
  rw ← is_scalar_tower.algebra_map_apply,
end

instance kaehler_differential.is_scalar_tower' :
  is_scalar_tower R (S ⊗[R] S) Ω[S⁄R] :=
begin
  convert restrict_scalars.is_scalar_tower R (S ⊗[R] S) Ω[S⁄R] using 1,
  ext x m,
  show algebra_map R S x • m = algebra_map R (S ⊗[R] S) x • m,
  simp_rw [is_scalar_tower.algebra_map_apply R S (S ⊗[R] S), is_scalar_tower.algebra_map_smul]
end

/-- The quotient map `I → Ω[S⁄R]` with `I` being the kernel of `S ⊗[R] S → S`. -/
def kaehler_differential.from_ideal : kaehler_differential.ideal R S →ₗ[S ⊗[R] S] Ω[S⁄R] :=
(kaehler_differential.ideal R S).to_cotangent

/-- (Implementation) The underlying linear map of the derivation into `Ω[S⁄R]`. -/
def kaehler_differential.D_linear_map : S →ₗ[R] Ω[S⁄R] :=
((kaehler_differential.from_ideal R S).restrict_scalars R).comp
  ((tensor_product.include_right.to_linear_map - tensor_product.include_left.to_linear_map :
    S →ₗ[R] S ⊗[R] S).cod_restrict ((kaehler_differential.ideal R S).restrict_scalars R)
      (kaehler_differential.one_smul_sub_smul_one_mem_ideal R) : _ →ₗ[R] _)

lemma kaehler_differential.D_linear_map_apply (s : S) :
  kaehler_differential.D_linear_map R S s = (kaehler_differential.ideal R S).to_cotangent
    ⟨1 ⊗ₜ s - s ⊗ₜ 1, kaehler_differential.one_smul_sub_smul_one_mem_ideal R s⟩ :=
rfl

/-- The universal derivation into `Ω[S⁄R]`. -/
def kaehler_differential.D : derivation R S Ω[S⁄R] :=
{ map_one_eq_zero' := begin
    dsimp [kaehler_differential.D_linear_map_apply],
    rw [ideal.to_cotangent_eq_zero, subtype.coe_mk, sub_self],
    exact zero_mem _
  end,
  leibniz' := λ a b, begin
    dsimp [kaehler_differential.D_linear_map_apply],
    rw [← linear_map.map_smul_of_tower, ← linear_map.map_smul_of_tower, ← map_add,
      ideal.to_cotangent_eq, pow_two],
    convert submodule.mul_mem_mul (kaehler_differential.one_smul_sub_smul_one_mem_ideal R a : _)
      (kaehler_differential.one_smul_sub_smul_one_mem_ideal R b : _) using 1,
    simp only [add_subgroup_class.coe_sub, submodule.coe_add, submodule.coe_mk,
      tensor_product.tmul_mul_tmul, mul_sub, sub_mul, mul_comm b,
      submodule.coe_smul_of_tower, smul_sub, tensor_product.smul_tmul', smul_eq_mul, mul_one],
    ring_nf,
  end,
  ..(kaehler_differential.D_linear_map R S) }

lemma kaehler_differential.D_apply (s : S) :
  kaehler_differential.D R S s = (kaehler_differential.ideal R S).to_cotangent
    ⟨1 ⊗ₜ s - s ⊗ₜ 1, kaehler_differential.one_smul_sub_smul_one_mem_ideal R s⟩ :=
rfl

lemma kaehler_differential.span_range_derivation :
  submodule.span S (set.range $ kaehler_differential.D R S) = ⊤ :=
begin
  rw _root_.eq_top_iff,
  rintros x -,
  obtain ⟨⟨x, hx⟩, rfl⟩ := ideal.to_cotangent_surjective _ x,
  have : x ∈ (kaehler_differential.ideal R S).restrict_scalars S := hx,
  rw ← kaehler_differential.submodule_span_range_eq_ideal at this,
  suffices : ∃ hx, (kaehler_differential.ideal R S).to_cotangent ⟨x, hx⟩ ∈
    submodule.span S (set.range $ kaehler_differential.D R S),
  { exact this.some_spec },
  apply submodule.span_induction this,
  { rintros _ ⟨x, rfl⟩,
    refine ⟨kaehler_differential.one_smul_sub_smul_one_mem_ideal R x, _⟩,
    apply submodule.subset_span,
    exact ⟨x, kaehler_differential.D_linear_map_apply R S x⟩ },
  { exact ⟨zero_mem _, submodule.zero_mem _⟩ },
  { rintros x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩, exact ⟨add_mem hx₁ hy₁, submodule.add_mem _ hx₂ hy₂⟩ },
  { rintros r x ⟨hx₁, hx₂⟩, exact ⟨((kaehler_differential.ideal R S).restrict_scalars S).smul_mem
      r hx₁, submodule.smul_mem _ r hx₂⟩ }
end

variables {R S}

/-- The linear map from `Ω[S⁄R]`, associated with a derivation. -/
def derivation.lift_kaehler_differential (D : derivation R S M) : Ω[S⁄R] →ₗ[S] M :=
begin
  refine ((kaehler_differential.ideal R S • ⊤ :
    submodule (S ⊗[R] S) (kaehler_differential.ideal R S)).restrict_scalars S).liftq _ _,
  { exact D.tensor_product_to.comp ((kaehler_differential.ideal R S).subtype.restrict_scalars S) },
  { intros x hx,
    change _ = _,
    apply submodule.smul_induction_on hx; clear hx x,
    { rintros x (hx : _ = _) ⟨y, hy : _ = _⟩ -,
      dsimp,
      rw [derivation.tensor_product_to_mul, hx, hy, zero_smul, zero_smul, zero_add] },
    { intros x y ex ey, rw [map_add, ex, ey, zero_add] } }
end

lemma derivation.lift_kaehler_differential_apply (D : derivation R S M) (x) :
  D.lift_kaehler_differential
    ((kaehler_differential.ideal R S).to_cotangent x) = D.tensor_product_to x :=
rfl

lemma derivation.lift_kaehler_differential_comp (D : derivation R S M) :
  D.lift_kaehler_differential.comp_der (kaehler_differential.D R S) = D :=
begin
  ext a,
  dsimp [kaehler_differential.D_apply],
  refine (D.lift_kaehler_differential_apply _).trans _,
  rw [subtype.coe_mk, map_sub, derivation.tensor_product_to_tmul,
    derivation.tensor_product_to_tmul, one_smul, D.map_one_eq_zero, smul_zero, sub_zero],
end

@[simp] lemma derivation.lift_kaehler_differential_comp_D (D' : derivation R S M) (x : S) :
  D'.lift_kaehler_differential (kaehler_differential.D R S x) = D' x :=
derivation.congr_fun D'.lift_kaehler_differential_comp x

@[ext]
lemma derivation.lift_kaehler_differential_unique
  (f f' : Ω[S⁄R] →ₗ[S] M)
  (hf : f.comp_der (kaehler_differential.D R S) =
    f'.comp_der (kaehler_differential.D R S)) :
  f = f' :=
begin
  apply linear_map.ext,
  intro x,
  have : x ∈ submodule.span S (set.range $ kaehler_differential.D R S),
  { rw kaehler_differential.span_range_derivation, trivial },
  apply submodule.span_induction this,
  { rintros _ ⟨x, rfl⟩, exact congr_arg (λ D : derivation R S M, D x) hf },
  { rw [map_zero, map_zero] },
  { intros x y hx hy, rw [map_add, map_add, hx, hy] },
  { intros a x e, rw [map_smul, map_smul, e] }
end

variables (R S)

lemma derivation.lift_kaehler_differential_D :
  (kaehler_differential.D R S).lift_kaehler_differential = linear_map.id :=
derivation.lift_kaehler_differential_unique _ _
  (kaehler_differential.D R S).lift_kaehler_differential_comp

variables {R S}

lemma kaehler_differential.D_tensor_product_to (x : kaehler_differential.ideal R S) :
  (kaehler_differential.D R S).tensor_product_to x =
    (kaehler_differential.ideal R S).to_cotangent x :=
begin
  rw [← derivation.lift_kaehler_differential_apply, derivation.lift_kaehler_differential_D],
  refl,
end

variables (R S)

lemma kaehler_differential.tensor_product_to_surjective :
  function.surjective (kaehler_differential.D R S).tensor_product_to :=
begin
  intro x, obtain ⟨x, rfl⟩ := (kaehler_differential.ideal R S).to_cotangent_surjective x,
  exact ⟨x, kaehler_differential.D_tensor_product_to x⟩
end

/-- The `S`-linear maps from `Ω[S⁄R]` to `M` are (`S`-linearly) equivalent to `R`-derivations
from `S` to `M`.  -/
def kaehler_differential.linear_map_equiv_derivation : (Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] derivation R S M :=
{ inv_fun := derivation.lift_kaehler_differential,
  left_inv := λ f, derivation.lift_kaehler_differential_unique _ _
    (derivation.lift_kaehler_differential_comp _),
  right_inv := derivation.lift_kaehler_differential_comp,
  ..(derivation.llcomp.flip $ kaehler_differential.D R S) }

/-- The quotient ring of `S ⊗ S ⧸ J ^ 2` by `Ω[S⁄R]` is isomorphic to `S`. -/
def kaehler_differential.quotient_cotangent_ideal_ring_equiv :
  (S ⊗ S ⧸ kaehler_differential.ideal R S ^ 2) ⧸
    (kaehler_differential.ideal R S).cotangent_ideal ≃+* S :=
begin
  have : function.right_inverse tensor_product.include_left
    (↑(tensor_product.lmul' R : S ⊗[R] S →ₐ[R] S) : S ⊗[R] S →+* S),
  { intro x, rw [alg_hom.coe_to_ring_hom, ← alg_hom.comp_apply,
      tensor_product.lmul'_comp_include_left], refl },
  refine (ideal.quot_cotangent _).trans _,
  refine (ideal.quot_equiv_of_eq _).trans (ring_hom.quotient_ker_equiv_of_right_inverse this),
  ext, refl,
end

/-- The quotient ring of `S ⊗ S ⧸ J ^ 2` by `Ω[S⁄R]` is isomorphic to `S` as an `S`-algebra. -/
def kaehler_differential.quotient_cotangent_ideal :
  ((S ⊗ S ⧸ kaehler_differential.ideal R S ^ 2) ⧸
    (kaehler_differential.ideal R S).cotangent_ideal) ≃ₐ[S] S :=
{ commutes' := (kaehler_differential.quotient_cotangent_ideal_ring_equiv R S).apply_symm_apply,
  ..kaehler_differential.quotient_cotangent_ideal_ring_equiv R S }

lemma kaehler_differential.End_equiv_aux (f : S →ₐ[R] S ⊗ S ⧸ kaehler_differential.ideal R S ^ 2) :
  (ideal.quotient.mkₐ R (kaehler_differential.ideal R S).cotangent_ideal).comp f =
    is_scalar_tower.to_alg_hom R S _ ↔
  (tensor_product.lmul' R : S ⊗[R] S →ₐ[R] S).ker_square_lift.comp f = alg_hom.id R S :=
begin
  rw [alg_hom.ext_iff, alg_hom.ext_iff],
  apply forall_congr,
  intro x,
  have e₁ : (tensor_product.lmul' R : S ⊗[R] S →ₐ[R] S).ker_square_lift (f x) =
    kaehler_differential.quotient_cotangent_ideal_ring_equiv R S
      (ideal.quotient.mk (kaehler_differential.ideal R S).cotangent_ideal $ f x),
  { generalize : f x = y, obtain ⟨y, rfl⟩ := ideal.quotient.mk_surjective y, refl },
  have e₂ : x = kaehler_differential.quotient_cotangent_ideal_ring_equiv
    R S (is_scalar_tower.to_alg_hom R S _ x),
  { exact (mul_one x).symm },
  split,
  { intro e,
    exact (e₁.trans (@ring_equiv.congr_arg _ _ _ _ _ _
      (kaehler_differential.quotient_cotangent_ideal_ring_equiv R S) _ _ e)).trans e₂.symm },
  { intro e, apply (kaehler_differential.quotient_cotangent_ideal_ring_equiv R S).injective,
    exact e₁.symm.trans (e.trans e₂) }
end

/-- Derivations into `Ω[S⁄R]` is equivalent to derivations
into `(kaehler_differential.ideal R S).cotangent_ideal` -/
-- This has type
-- `derivation R S Ω[S⁄R] ≃ₗ[R] derivation R S (kaehler_differential.ideal R S).cotangent_ideal`
-- But lean times-out if this is given explicitly.
noncomputable
def kaehler_differential.End_equiv_derivation' :=
@linear_equiv.comp_der R _ _ _ _ Ω[S⁄R] _ _ _ _ _ _ _ _ _
  ((kaehler_differential.ideal R S).cotangent_equiv_ideal.restrict_scalars S)

/-- (Implementation) An `equiv` version of `kaehler_differential.End_equiv_aux`.
Used in `kaehler_differential.End_equiv`. -/
def kaehler_differential.End_equiv_aux_equiv :
  {f // (ideal.quotient.mkₐ R (kaehler_differential.ideal R S).cotangent_ideal).comp f =
    is_scalar_tower.to_alg_hom R S _ } ≃
  { f // (tensor_product.lmul' R : S ⊗[R] S →ₐ[R] S).ker_square_lift.comp f = alg_hom.id R S } :=
(equiv.refl _).subtype_equiv (kaehler_differential.End_equiv_aux R S)

/--
The endomorphisms of `Ω[S⁄R]` corresponds to sections of the surjection `S ⊗[R] S ⧸ J ^ 2 →ₐ[R] S`,
with `J` being the kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.
-/
noncomputable
def kaehler_differential.End_equiv :
  module.End S Ω[S⁄R] ≃
    { f // (tensor_product.lmul' R : S ⊗[R] S →ₐ[R] S).ker_square_lift.comp f = alg_hom.id R S } :=
(kaehler_differential.linear_map_equiv_derivation R S).to_equiv.trans $
  (kaehler_differential.End_equiv_derivation' R S).to_equiv.trans $
  (derivation_to_square_zero_equiv_lift
  (kaehler_differential.ideal R S).cotangent_ideal
  (kaehler_differential.ideal R S).cotangent_ideal_square).trans $
  kaehler_differential.End_equiv_aux_equiv R S

section presentation

open kaehler_differential (D)
open finsupp (single)

/-- The `S`-submodule of `S →₀ S` (the direct sum of copies of `S` indexed by `S`) generated by
the relations:
1. `dx + dy = d(x + y)`
2. `x dy + y dx = d(x * y)`
3. `dr = 0` for `r ∈ R`
where `db` is the unit in the copy of `S` with index `b`.

This is the kernel of the surjection `finsupp.total S Ω[S⁄R] S (kaehler_differential.D R S)`.
See `kaehler_differential.ker_total_eq` and `kaehler_differential.total_surjective`.
-/
noncomputable
def kaehler_differential.ker_total : submodule S (S →₀ S) :=
submodule.span S
  ((set.range (λ (x : S × S), single x.1 1 + single x.2 1 - single (x.1 + x.2) 1)) ∪
  (set.range (λ (x : S × S), single x.2 x.1 + single x.1 x.2 - single (x.1 * x.2) 1)) ∪
  (set.range (λ x : R, single (algebra_map R S x) 1)))

local notation x `𝖣` y := (kaehler_differential.ker_total R S).mkq (single y x)

lemma kaehler_differential.ker_total_mkq_single_add (x y z) :
  (z 𝖣 (x + y)) = (z 𝖣 x) + (z 𝖣 y) :=
begin
  rw [← map_add, eq_comm, ← sub_eq_zero, ← map_sub, submodule.mkq_apply,
    submodule.quotient.mk_eq_zero],
  simp_rw [← finsupp.smul_single_one _ z, ← smul_add, ← smul_sub],
  exact submodule.smul_mem _ _ (submodule.subset_span (or.inl $ or.inl $ ⟨⟨_, _⟩, rfl⟩)),
end

lemma kaehler_differential.ker_total_mkq_single_mul (x y z) :
  (z 𝖣 (x * y)) = ((z * x) 𝖣 y) + ((z * y) 𝖣 x) :=
begin
  rw [← map_add, eq_comm, ← sub_eq_zero, ← map_sub, submodule.mkq_apply,
    submodule.quotient.mk_eq_zero],
  simp_rw [← finsupp.smul_single_one _ z, ← @smul_eq_mul _ _ z,
    ← finsupp.smul_single, ← smul_add, ← smul_sub],
  exact submodule.smul_mem _ _ (submodule.subset_span (or.inl $ or.inr $ ⟨⟨_, _⟩, rfl⟩)),
end

lemma kaehler_differential.ker_total_mkq_single_algebra_map (x y) :
  (y 𝖣 (algebra_map R S x)) = 0 :=
begin
  rw [submodule.mkq_apply, submodule.quotient.mk_eq_zero, ← finsupp.smul_single_one _ y],
  exact submodule.smul_mem _ _ (submodule.subset_span (or.inr $ ⟨_, rfl⟩)),
end

lemma kaehler_differential.ker_total_mkq_single_algebra_map_one (x) :
  (x 𝖣 1) = 0 :=
begin
  rw [← (algebra_map R S).map_one, kaehler_differential.ker_total_mkq_single_algebra_map],
end

lemma kaehler_differential.ker_total_mkq_single_smul (r : R) (x y) :
  (y 𝖣 (r • x)) = r • (y 𝖣 x) :=
begin
  rw [algebra.smul_def, kaehler_differential.ker_total_mkq_single_mul,
    kaehler_differential.ker_total_mkq_single_algebra_map, add_zero,
    ← linear_map.map_smul_of_tower, finsupp.smul_single, mul_comm, algebra.smul_def],
end

/-- The (universal) derivation into `(S →₀ S) ⧸ kaehler_differential.ker_total R S`. -/
noncomputable
def kaehler_differential.derivation_quot_ker_total :
  derivation R S ((S →₀ S) ⧸ kaehler_differential.ker_total R S) :=
{ to_fun := λ x, 1 𝖣 x,
  map_add' := λ x y, kaehler_differential.ker_total_mkq_single_add _ _ _ _ _,
  map_smul' := λ r s, kaehler_differential.ker_total_mkq_single_smul _ _ _ _ _,
  map_one_eq_zero' := kaehler_differential.ker_total_mkq_single_algebra_map_one _ _ _,
  leibniz' := λ a b, (kaehler_differential.ker_total_mkq_single_mul _ _ _ _ _).trans
    (by { simp_rw [← finsupp.smul_single_one _ (1 * _ : S)], dsimp, simp }) }

lemma kaehler_differential.derivation_quot_ker_total_apply (x) :
  kaehler_differential.derivation_quot_ker_total R S x = (1 𝖣 x) := rfl

lemma kaehler_differential.derivation_quot_ker_total_lift_comp_total :
  (kaehler_differential.derivation_quot_ker_total R S).lift_kaehler_differential.comp
    (finsupp.total S Ω[S⁄R] S (kaehler_differential.D R S)) = submodule.mkq _ :=
begin
  apply finsupp.lhom_ext,
  intros a b,
  conv_rhs { rw [← finsupp.smul_single_one a b, linear_map.map_smul] },
  simp [kaehler_differential.derivation_quot_ker_total_apply],
end

lemma kaehler_differential.ker_total_eq :
  (finsupp.total S Ω[S⁄R] S (kaehler_differential.D R S)).ker =
    kaehler_differential.ker_total R S :=
begin
  apply le_antisymm,
  { conv_rhs { rw ← (kaehler_differential.ker_total R S).ker_mkq },
    rw ← kaehler_differential.derivation_quot_ker_total_lift_comp_total,
    exact linear_map.ker_le_ker_comp _ _ },
  { rw [kaehler_differential.ker_total, submodule.span_le],
    rintros _ ((⟨⟨x, y⟩, rfl⟩|⟨⟨x, y⟩, rfl⟩)|⟨x, rfl⟩); dsimp; simp [linear_map.mem_ker] },
end

lemma kaehler_differential.total_surjective :
  function.surjective (finsupp.total S Ω[S⁄R] S (kaehler_differential.D R S)) :=
begin
  rw [← linear_map.range_eq_top, finsupp.range_total, kaehler_differential.span_range_derivation],
end

/-- `Ω[S⁄R]` is isomorphic to `S` copies of `S` with kernel `kaehler_differential.ker_total`. -/
@[simps] noncomputable
def kaehler_differential.quot_ker_total_equiv :
  ((S →₀ S) ⧸ kaehler_differential.ker_total R S) ≃ₗ[S] Ω[S⁄R] :=
{ inv_fun := (kaehler_differential.derivation_quot_ker_total R S).lift_kaehler_differential,
  left_inv := begin
    intro x,
    obtain ⟨x, rfl⟩ := submodule.mkq_surjective _ x,
    exact linear_map.congr_fun
      (kaehler_differential.derivation_quot_ker_total_lift_comp_total R S : _) x,
  end,
  right_inv := begin
    intro x,
    obtain ⟨x, rfl⟩ := kaehler_differential.total_surjective R S x,
    erw linear_map.congr_fun
      (kaehler_differential.derivation_quot_ker_total_lift_comp_total R S : _) x,
    refl
  end,
  ..(kaehler_differential.ker_total R S).liftq
    (finsupp.total S Ω[S⁄R] S (kaehler_differential.D R S))
    (kaehler_differential.ker_total_eq R S).ge }

lemma kaehler_differential.quot_ker_total_equiv_symm_comp_D :
  (kaehler_differential.quot_ker_total_equiv R S).symm.to_linear_map.comp_der
    (kaehler_differential.D R S) = kaehler_differential.derivation_quot_ker_total R S :=
by convert
  (kaehler_differential.derivation_quot_ker_total R S).lift_kaehler_differential_comp using 0

variables (A B : Type*) [comm_ring A] [comm_ring B] [algebra R A] [algebra S B] [algebra R B]
variables [algebra A B] [is_scalar_tower R S B] [is_scalar_tower R A B]

-- The map `(A →₀ A) →ₗ[A] (B →₀ B)`
local notation `finsupp_map` := ((finsupp.map_range.linear_map (algebra.of_id A B).to_linear_map)
  .comp (finsupp.lmap_domain A A (algebra_map A B)))

lemma kaehler_differential.ker_total_map (h : function.surjective (algebra_map A B)) :
  (kaehler_differential.ker_total R A).map finsupp_map ⊔
    submodule.span A (set.range (λ x : S, single (algebra_map S B x) (1 : B))) =
    (kaehler_differential.ker_total S B).restrict_scalars _  :=
begin
  rw [kaehler_differential.ker_total, submodule.map_span, kaehler_differential.ker_total,
    submodule.restrict_scalars_span _ _ h],
  simp_rw [set.image_union, submodule.span_union, ← set.image_univ, set.image_image,
    set.image_univ, map_sub, map_add],
  simp only [linear_map.comp_apply, finsupp.map_range.linear_map_apply, finsupp.map_range_single,
    finsupp.lmap_domain_apply, finsupp.map_domain_single, alg_hom.to_linear_map_apply,
    algebra.of_id_apply, ← is_scalar_tower.algebra_map_apply, map_one, map_add, map_mul],
  simp_rw [sup_assoc, ← (h.prod_map h).range_comp],
  congr' 3,
  rw [sup_eq_right],
  apply submodule.span_mono,
  simp_rw is_scalar_tower.algebra_map_apply R S B,
  exact set.range_comp_subset_range (algebra_map R S) (λ x, single (algebra_map S B x) (1 : B))
end

end presentation

section exact_sequence

local attribute [irreducible] kaehler_differential

/- We have the commutative diagram
A --→ B
↑     ↑
|     |
R --→ S -/
variables (A B : Type*) [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]
variables [algebra A B] [algebra S B] [is_scalar_tower R A B] [is_scalar_tower R S B]

variables {R B}

/-- For a tower `R → A → B` and an `R`-derivation `B → M`, we may compose with `A → B` to obtain an
`R`-derivation `A → M`. -/
def derivation.comp_algebra_map [module A M] [module B M] [is_scalar_tower A B M]
  (d : derivation R B M) : derivation R A M :=
{ map_one_eq_zero' := by simp,
  leibniz' := λ a b, by simp,
  to_linear_map := d.to_linear_map.comp (is_scalar_tower.to_alg_hom R A B).to_linear_map }

variables (R B)

/-- The map `Ω[A⁄R] →ₗ[A] Ω[B⁄R]` given a square
A --→ B
↑     ↑
|     |
R --→ S -/
def kaehler_differential.map : Ω[A⁄R] →ₗ[A] Ω[B⁄S] :=
derivation.lift_kaehler_differential
  (((kaehler_differential.D S B).restrict_scalars R).comp_algebra_map A)

lemma kaehler_differential.map_comp_der :
  (kaehler_differential.map R S A B).comp_der (kaehler_differential.D R A) =
    (((kaehler_differential.D S B).restrict_scalars R).comp_algebra_map A) :=
derivation.lift_kaehler_differential_comp _

lemma kaehler_differential.map_D (x : A) :
  kaehler_differential.map R S A B (kaehler_differential.D R A x) =
    kaehler_differential.D S B (algebra_map A B x) :=
derivation.congr_fun (kaehler_differential.map_comp_der R S A B) x

open is_scalar_tower (to_alg_hom)

lemma kaehler_differential.map_surjective_of_surjective
  (h : function.surjective (algebra_map A B)) :
  function.surjective (kaehler_differential.map R S A B) :=
begin
  rw [← linear_map.range_eq_top, _root_.eq_top_iff, ← @submodule.restrict_scalars_top B A,
    ← kaehler_differential.span_range_derivation, submodule.restrict_scalars_span _ _ h,
    submodule.span_le],
  rintros _ ⟨x, rfl⟩,
  obtain ⟨y, rfl⟩ := h x,
  rw ← kaehler_differential.map_D R S A B,
  exact ⟨_, rfl⟩,
end

/-- The lift of the map `Ω[A⁄R] →ₗ[A] Ω[B⁄R]` to the base change along `A → B`.
This is the first map in the exact sequence `B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0`. -/
noncomputable
def kaehler_differential.map_base_change : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R] :=
(tensor_product.is_base_change A Ω[A⁄R] B).lift (kaehler_differential.map R R A B)

@[simp]
lemma kaehler_differential.map_base_change_tmul (x : B) (y : Ω[A⁄R]) :
  kaehler_differential.map_base_change R A B (x ⊗ₜ y) =
    x • kaehler_differential.map R R A B y :=
begin
  conv_lhs { rw [← mul_one x, ← smul_eq_mul, ← tensor_product.smul_tmul', linear_map.map_smul] },
  congr' 1,
  exact is_base_change.lift_eq _ _ _
end

end exact_sequence

end kaehler_differential
