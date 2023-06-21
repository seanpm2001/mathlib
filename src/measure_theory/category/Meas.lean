/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import measure_theory.measure.giry_monad
import category_theory.concrete_category.unbundled_hom
import category_theory.monad.algebra
import topology.category.Top.basic

/-!
# The category of measurable spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Measurable spaces and measurable functions form a (concrete) category `Meas`.

## Main definitions

* `Measure : Meas ⥤ Meas`: the functor which sends a measurable space `X`
to the space of measures on `X`; it is a monad (the "Giry monad").

* `Borel : Top ⥤ Meas`: sends a topological space `X` to `X` equipped with the
`σ`-algebra of Borel sets (the `σ`-algebra generated by the open subsets of `X`).

## Tags

measurable space, giry monad, borel
-/

noncomputable theory

open category_theory measure_theory
open_locale ennreal
universes u v

/-- The category of measurable spaces and measurable functions. -/
def Meas : Type (u+1) := bundled measurable_space

namespace Meas

instance : has_coe_to_sort Meas Type* := bundled.has_coe_to_sort
instance (X : Meas) : measurable_space X := X.str

/-- Construct a bundled `Meas` from the underlying type and the typeclass. -/
def of (α : Type u) [measurable_space α] : Meas := ⟨α⟩

@[simp] lemma coe_of (X : Type u) [measurable_space X] : (of X : Type u) = X := rfl

instance unbundled_hom : unbundled_hom @measurable := ⟨@measurable_id, @measurable.comp⟩

attribute [derive [large_category, concrete_category]] Meas

instance : inhabited Meas := ⟨Meas.of empty⟩

/-- `Measure X` is the measurable space of measures over the measurable space `X`. It is the
weakest measurable space, s.t. λμ, μ s is measurable for all measurable sets `s` in `X`. An
important purpose is to assign a monadic structure on it, the Giry monad. In the Giry monad,
the pure values are the Dirac measure, and the bind operation maps to the integral:
`(μ >>= ν) s = ∫ x. (ν x) s dμ`.

In probability theory, the `Meas`-morphisms `X → Prob X` are (sub-)Markov kernels (here `Prob` is
the restriction of `Measure` to (sub-)probability space.)
-/
def Measure : Meas ⥤ Meas :=
{ obj      := λX, ⟨@measure_theory.measure X.1 X.2⟩,
  map      := λX Y f, ⟨measure.map (f : X → Y), measure.measurable_map f f.2⟩,
  map_id'  := assume ⟨α, I⟩, subtype.eq $ funext $ assume μ, @measure.map_id α I μ,
  map_comp':=
    assume X Y Z ⟨f, hf⟩ ⟨g, hg⟩, subtype.eq $ funext $ assume μ, (measure.map_map hg hf).symm }

/-- The Giry monad, i.e. the monadic structure associated with `Measure`. -/
def Giry : category_theory.monad Meas :=
{ to_functor := Measure,
  η' :=
  { app         := λX, ⟨@measure.dirac X.1 X.2, measure.measurable_dirac⟩,
    naturality' :=
      assume X Y ⟨f, hf⟩, subtype.eq $ funext $ assume a, (measure.map_dirac hf a).symm },
  μ' :=
  { app         := λX, ⟨@measure.join X.1 X.2, measure.measurable_join⟩,
    naturality' :=
      assume X Y ⟨f, hf⟩, subtype.eq $ funext $ assume μ, measure.join_map_map hf μ },
  assoc' := assume α, subtype.eq $ funext $ assume μ, @measure.join_map_join _ _ _,
  left_unit' := assume α, subtype.eq $ funext $ assume μ, @measure.join_dirac _ _ _,
  right_unit' := assume α, subtype.eq $ funext $ assume μ, @measure.join_map_dirac _ _ _ }

/-- An example for an algebra on `Measure`: the nonnegative Lebesgue integral is a hom, behaving
nicely under the monad operations. -/
def Integral : Giry.algebra :=
{ A      := Meas.of ℝ≥0∞ ,
  a      := ⟨λm:measure ℝ≥0∞, ∫⁻ x, x ∂m, measure.measurable_lintegral measurable_id ⟩,
  unit'  := subtype.eq $ funext $ assume r:ℝ≥0∞, lintegral_dirac' _ measurable_id,
  assoc' := subtype.eq $ funext $ assume μ : measure (measure ℝ≥0∞),
    show ∫⁻ x, x ∂ μ.join = ∫⁻ x, x ∂ (measure.map (λm:measure ℝ≥0∞, ∫⁻ x, x ∂m) μ),
    by rw [measure.lintegral_join, lintegral_map];
      apply_rules [measurable_id, measure.measurable_lintegral] }

end Meas

instance Top.has_forget_to_Meas : has_forget₂ Top.{u} Meas.{u} :=
bundled_hom.mk_has_forget₂
  borel
  (λ X Y f, ⟨f.1, f.2.borel_measurable⟩)
  (by intros; refl)

/-- The Borel functor, the canonical embedding of topological spaces into measurable spaces. -/
@[reducible] def Borel : Top.{u} ⥤ Meas.{u} := forget₂ Top.{u} Meas.{u}
