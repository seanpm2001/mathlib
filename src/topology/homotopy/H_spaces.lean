/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Junyan Xu
-/
import topology.compact_open
import topology.homotopy.path

/-!
# H-spaces

This file defines H-spaces mainly following the approach proposed by Serre in his paper
*Homologie singulière des espaces fibrés*. The idea beaneath `H-spaces` is that they are topological
spaces with a binary operation `⋀ : X → X → X` that is a homotopic-theoretic weakening of an
operation what would make `X` into a topological monoid. In particular, there exists a "neutral
element" `e : X` such that `λ x, e ⋀ x` and `λ x, x ⋀ e` are homotopic to the identity on `X`, see
[the Wikipedia page of H-spaces](https://en.wikipedia.org/wiki/H-space).

Some notable properties of `H-spaces` are
* Their fundamental group is always abelian (by the same argument for topological groups);
* Their cohomology ring comes equipped with a structure of a Hopf-algebra;
* The loop space based at every `x : X` carries a structure of an `H-spaces`.

## Main Results

* Every topological group `G` is an `H-space` using its operation `* : G → G → G` (this is already
true if `G` has an instance of a `mul_one_class` and `continuous_mul`);
* Given two `H-spaces` `X` and `Y`, their product is again an `H`-space. We show in an example that
starting with two topological groups `G, G'`, the `H`-space structure on `G × G'` is definitionally
equal to the product of `H-space` structures on `G` and `G'`.
* The loop space based at every `x : X` carries a structure of an `H-spaces`.

## To Do
* Prove that for every `normed_add_torsor Z` and every `z : Z`, the operation
`λ x y, midpoint x y` defines a `H-space` structure with `z` as a "neutral element".
* Prove that `S^0`, `S^1`, `S^3` and `S^7` are the unique spheres that are `H-spaces`, where the
first three inherit the structure because they are topological groups (they are Lie groups,
actually), isomorphic to the invertible elements in `ℤ`, in `ℂ` and in the quaternion; and the
fourth from the fact that `S^7` coincides with the octonions of norm 1 (it is not a group, in
particular, only has an instance of `mul_one_class`).

## References

* [J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*,
  Ann. of Math (2) 1951, 54, 425–505][serre1951]
-/

universes u v

noncomputable theory

open_locale unit_interval

open path continuous_map set.Icc topological_space

/--
A topological space `X` is an H-space if it behaves like a (potentially non-associative)
topological group, but where the axioms for a group only hold up to homotopy.
-/
class H_space (X : Type u) [topological_space X] :=
(Hmul : C(X × X, X))
(e : X)
(Hmul_e_e : Hmul (e, e) = e)
(e_Hmul : (Hmul.comp $ (const X e).prod_mk $ continuous_map.id X).homotopy_rel
  (continuous_map.id X) {e})
(Hmul_e : (Hmul.comp $ (continuous_map.id X).prod_mk $ const X e).homotopy_rel
  (continuous_map.id X) {e})

/- We use the notation `⋀`, typeset as \And, to denote the binary operation `Hmul` on a H-space -/
localized "notation (name := H_space.Hmul) x `⋀` y := H_space.Hmul (x, y) " in H_spaces

instance H_space.prod (X : Type u) (Y : Type v) [topological_space X] [topological_space Y]
[H_space X] [H_space Y] : H_space (X × Y) :=
{ Hmul := ⟨λ p, ((p.1.1 ⋀ p.2.1),  p.1.2 ⋀ p.2.2), by continuity⟩,
  e := (H_space.e, H_space.e),
  Hmul_e_e := by {simp only [continuous_map.coe_mk, prod.mk.inj_iff],
    exact ⟨H_space.Hmul_e_e, H_space.Hmul_e_e⟩},
  e_Hmul :=
  begin
    let G : I × (X × Y) → X × Y :=
      (λ p, (H_space.e_Hmul (p.1, p.2.1), H_space.e_Hmul (p.1, p.2.2))),
    have hG : continuous G := (continuous.comp H_space.e_Hmul.1.1.2 (continuous_fst.prod_mk
      (continuous_fst.comp continuous_snd))).prod_mk (continuous.comp H_space.e_Hmul.1.1.2
      (continuous_fst.prod_mk (continuous_snd.comp continuous_snd))),
    use ⟨G, hG⟩,
    { rintros ⟨x, y⟩,
      exacts prod.mk.inj_iff.mpr ⟨(H_space.e_Hmul).1.2 x, (H_space.e_Hmul).1.2 y⟩ },
    { rintros ⟨x, y⟩,
      exact prod.mk.inj_iff.mpr ⟨(H_space.e_Hmul).1.3 x, (H_space.e_Hmul).1.3 y⟩ },
    { rintros t ⟨x, y⟩ h,
      replace h := prod.mk.inj_iff.mp (set.mem_singleton_iff.mp h),
      exact ⟨prod.mk.inj_iff.mpr ⟨homotopy_rel.eq_fst (H_space.e_Hmul) t
        (set.mem_singleton_iff.mpr h.1),
        homotopy_rel.eq_fst (H_space.e_Hmul) t (set.mem_singleton_iff.mpr h.2)⟩,
        prod.mk.inj_iff.mpr ⟨((H_space.e_Hmul).2 t x h.1).2, ((H_space.e_Hmul).2 t y h.2).2⟩⟩ },
  end,
  Hmul_e :=
  begin
    let G : I × (X × Y) → X × Y :=
      (λ p, (H_space.Hmul_e (p.1, p.2.1), H_space.Hmul_e (p.1, p.2.2))),
    have hG : continuous G := (continuous.comp H_space.Hmul_e.1.1.2 (continuous_fst.prod_mk
      (continuous_fst.comp continuous_snd))).prod_mk (continuous.comp H_space.Hmul_e.1.1.2
      (continuous_fst.prod_mk (continuous_snd.comp continuous_snd))),
    use ⟨G, hG⟩,
    { rintros ⟨x, y⟩,
      exacts prod.mk.inj_iff.mpr ⟨(H_space.Hmul_e).1.2 x, (H_space.Hmul_e).1.2 y⟩ },
    { rintros ⟨x, y⟩,
      exact prod.mk.inj_iff.mpr ⟨(H_space.Hmul_e).1.3 x, (H_space.Hmul_e).1.3 y⟩ },
    { rintros t ⟨x, y⟩ h,
      replace h := prod.mk.inj_iff.mp (set.mem_singleton_iff.mp h),
      exact ⟨prod.mk.inj_iff.mpr ⟨homotopy_rel.eq_fst (H_space.Hmul_e) t
        (set.mem_singleton_iff.mpr h.1), homotopy_rel.eq_fst (H_space.Hmul_e) t
        (set.mem_singleton_iff.mpr h.2)⟩, prod.mk.inj_iff.mpr ⟨((H_space.Hmul_e).2 t x h.1).2,
        ((H_space.Hmul_e).2 t y h.2).2⟩⟩ },
  end, }

namespace topological_group

/-- The definition `to_H_space` is not an instance because its `@additive` version would
lead to a diamond since a topological field would inherit two `H_space` structures, one from the
`mul_one_class` and one from the `add_zero_class`. In the case of a group, we make
`topological_group.H_space` an instance."-/
@[to_additive "The definition `to_H_space` is not an instance because it comes together with a
multiplicative version which would lead to a diamond since a topological field would inherit two
`H_space` structures, one from the `mul_one_class` and one from the `add_zero_class`. In the case
of an additive group, we make `topological_group.H_space` an instance."]
definition to_H_space (M : Type u) [mul_one_class M] [topological_space M]
  [has_continuous_mul M] : H_space M :=
{ Hmul := ⟨function.uncurry has_mul.mul, continuous_mul⟩,
  e := 1,
  Hmul_e_e := one_mul 1,
  e_Hmul := (homotopy_rel.refl _ _).cast rfl (by {ext1, apply one_mul}),
  Hmul_e := (homotopy_rel.refl _ _).cast rfl (by {ext1, apply mul_one}) }

@[priority 600, to_additive] instance H_space (G : Type u)
  [topological_space G] [group G] [topological_group G] : H_space G := to_H_space G

lemma one_eq_H_space_e {G : Type u} [topological_space G] [group G] [topological_group G] :
  (1 : G) = H_space.e := rfl

/- In the following example we see that the `H-space` structure on the product of two topological
groups is definitionally equally to the product `H-space`-structure of the two groups.-/

example {G G' : Type u} [topological_space G] [group G] [topological_group G]
  [topological_space G'] [group G'] [topological_group G'] :
  to_H_space (G × G') = H_space.prod G G' := rfl

end topological_group

namespace unit_interval

/-- `Q_right` is analogous to the function `Q` defined on p. 475 of [serre1951] that helps proving
continuity of `delay_refl_right`.-/
def Q_right (p : I × I) : I := set.proj_Icc 0 1 zero_le_one (2 * p.1 / (1 + p.2))

lemma continuous_Q_right : continuous Q_right :=
continuous_proj_Icc.comp $ continuous.div (by continuity) (by continuity)
  (λ x, (add_pos zero_lt_one).ne')

lemma Q_right_zero_left (θ : I) : Q_right (0, θ) = 0 :=
set.proj_Icc_of_le_left _ $ by simp only [coe_zero, mul_zero, zero_div]

lemma Q_right_one_left (θ : I) : Q_right (1, θ) = 1 :=
set.proj_Icc_of_right_le _ $ (le_div_iff $ add_pos zero_lt_one).2 $
  by { dsimp only, rw [coe_one, one_mul, mul_one], apply add_le_add_left (le_one _) }

lemma Q_right_zero_right (t : I) : (Q_right (t, 0) : ℝ) = if (t : ℝ) ≤ 1 / 2 then 2 * t else 1 :=
begin
  simp only [Q_right, coe_zero, add_zero, div_one],
  split_ifs,
  { rw set.proj_Icc_of_mem _ ((mul_pos_mem_iff zero_lt_two).2 _), exacts [rfl, ⟨t.2.1, h⟩] },
  { rw (set.proj_Icc_eq_right _).2, { refl }, { linarith }, { exact zero_lt_one } },
end

lemma Q_right_one_right (t : I) : Q_right (t, 1) = t :=
eq.trans (by {rw Q_right, congr, apply mul_div_cancel_left, exact two_ne_zero}) $
  set.proj_Icc_coe zero_le_one _

end unit_interval

namespace path

open unit_interval

variables {X : Type u} [topological_space X] {x y : X}

/-- This is the function analogous to the one on p. 475 of [serre1951], defining a homotopy from
the product path `γ ∧ e` to `γ`.-/
def delay_refl_right (θ : I) (γ : path x y) : path x y :=
{ to_fun := λ t, γ (Q_right (t, θ)),
  continuous_to_fun := γ.continuous.comp (continuous_Q_right.comp $ continuous.prod.mk_left θ),
  source' := by { dsimp only, rw [Q_right_zero_left, γ.source] },
  target' := by { dsimp only, rw [Q_right_one_left, γ.target] } }

lemma continuous_delay_refl_right : continuous (λ p : I × path x y, delay_refl_right p.1 p.2) :=
  continuous_uncurry_iff.mp $ (continuous_snd.comp continuous_fst).path_eval $
  continuous_Q_right.comp $ continuous_snd.prod_mk $ continuous_fst.comp continuous_fst

lemma delay_refl_right_zero (γ : path x y) : delay_refl_right 0 γ = γ.trans (path.refl y) :=
begin
  ext t,
  simp only [delay_refl_right,
    trans_apply, refl_extend, path.coe_mk, function.comp_app, refl_apply],
  split_ifs, swap, conv_rhs { rw ← γ.target },
  all_goals { apply congr_arg γ, ext1, rw Q_right_zero_right },
  exacts [if_neg h, if_pos h],
end

lemma delay_refl_right_one (γ : path x y) : delay_refl_right 1 γ = γ :=
by { ext t, exact congr_arg γ (Q_right_one_right t) }

/-- This is the function on p. 475 of [serre1951], defining a homotopy from a path `γ` to the
product path `e ∧ γ`.-/
def delay_refl_left (θ : I) (γ : path x y) : path x y := (delay_refl_right θ γ.symm).symm

lemma continuous_delay_refl_left : continuous (λ p : I × path x y, delay_refl_left p.1 p.2) :=
path.continuous_symm.comp $ continuous_delay_refl_right.comp $ continuous_fst.prod_mk $
  path.continuous_symm.comp continuous_snd

lemma delay_refl_left_zero (γ : path x y) : delay_refl_left 0 γ = (path.refl x).trans γ :=
by simp only [delay_refl_left, delay_refl_right_zero, trans_symm, refl_symm, path.symm_symm]

lemma delay_refl_left_one (γ : path x y) : delay_refl_left 1 γ = γ :=
by simp only [delay_refl_left, delay_refl_right_one, path.symm_symm]

/--
The loop space at x carries a structure of a `H-space`. Note that the field `e_Hmul`
(resp. `Hmul_e`) neither implies nor is implied by `path.homotopy.refl_trans`
(resp. `path.homotopy.trans_refl`).
-/

instance (x : X) : H_space (path x x) :=
{ Hmul := ⟨λ ρ, ρ.1.trans ρ.2, continuous_trans⟩,
  e := refl x,
  Hmul_e_e := refl_trans_refl,
  e_Hmul :=
  { to_homotopy := ⟨⟨λ p : I × (path x x), delay_refl_left p.1 p.2,
      continuous_delay_refl_left⟩, delay_refl_left_zero, delay_refl_left_one⟩,
    prop' := by { rintro t _ (rfl : _ = _), exact ⟨refl_trans_refl.symm, rfl⟩ } },
  Hmul_e :=
  { to_homotopy := ⟨⟨λ p : I × (path x x), delay_refl_right p.1 p.2,
      continuous_delay_refl_right⟩, delay_refl_right_zero, delay_refl_right_one⟩,
    prop' := by { rintro t _ (rfl : _ = _), exact ⟨refl_trans_refl.symm, rfl⟩ } } }

end path
