/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.disintegration
import probability.notation

/-!
# Regular conditional probability distribution

We define the regular conditional probability distribution of `Y : α → Ω` given `X : α → β`, where
`Ω` is a standard Borel space. This is a `kernel β Ω` such that for almost all `a`, `cond_distrib`
evaluated at `X a` and a measurable set `s` is equal to the conditional expectation
`μ⟦Y ⁻¹' s | mβ.comap X⟧` evaluated at `a`.

`μ⟦Y ⁻¹' s | mβ.comap X⟧` maps a measurable set `s` to a function `α → ℝ≥0∞`, and for all `s` that
map is unique up to a `μ`-null set. For all `a`, the map from sets to `ℝ≥0∞` that we obtain that way
verifies some of the properties of a measure, but in general the fact that the `μ`-null set depends
on `s` can prevent us from finding versions of the conditional expectation that combine into a true
measure. The standard Borel space assumption on `Ω` allows us to do so.

The case `Y = X = id` is developed in more detail in `probability/kernel/condexp.lean`: here `X` is
understood as a map from `Ω` with a sub-σ-algebra to `Ω` with its default σ-algebra and the
conditional distribution defines a kernel associated with the conditional expectation with respect
to `m`.

## Main definitions

* `cond_distrib Y X μ`: regular conditional probability distribution of `Y : α → Ω` given
  `X : α → β`, where `Ω` is a standard Borel space.

## Main statements

* `cond_distrib_ae_eq_condexp`: for almost all `a`, `cond_distrib` evaluated at `X a` and a
  measurable set `s` is equal to the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`.
* `condexp_prod_ae_eq_integral_cond_distrib`: the conditional expectation
  `μ[(λ a, f (X a, Y a)) | X ; mβ]` is almost everywhere equal to the integral
  `∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a))`.

-/

open measure_theory set filter topological_space

open_locale ennreal measure_theory probability_theory

namespace probability_theory

variables {α β Ω F : Type*}
  [topological_space Ω] [measurable_space Ω] [polish_space Ω] [borel_space Ω] [nonempty Ω]
  [normed_add_comm_group F]
  {mα : measurable_space α} {μ : measure α} [is_finite_measure μ] {X : α → β} {Y : α → Ω}

/-- **Regular conditional probability distribution**: kernel associated with the conditional
expectation of `Y` given `X`.
For almost all `a`, `cond_distrib Y X μ` evaluated at `X a` and a measurable set `s` is equal to
the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`. It also satisfies the equality
`μ[(λ a, f (X a, Y a)) | mβ.comap X] =ᵐ[μ] λ a, ∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a))` for
all integrable functions `f`. -/
@[irreducible] noncomputable
def cond_distrib {mα : measurable_space α} [measurable_space β]
  (Y : α → Ω) (X : α → β) (μ : measure α) [is_finite_measure μ] :
  kernel β Ω :=
(μ.map (λ a, (X a, Y a))).cond_kernel

instance [measurable_space β] : is_markov_kernel (cond_distrib Y X μ) :=
by { rw cond_distrib, apply_instance, }

variables {mβ : measurable_space β} {s : set Ω} {t : set β} {f : β × Ω → F}
include mβ

section measurability

lemma measurable_cond_distrib (hs : measurable_set s) :
  measurable[mβ.comap X] (λ a, cond_distrib Y X μ (X a) s) :=
(kernel.measurable_coe _ hs).comp (measurable.of_comap_le le_rfl)

lemma _root_.measure_theory.ae_strongly_measurable.ae_integrable_cond_distrib_map_iff
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf : ae_strongly_measurable f (μ.map (λ a, (X a, Y a)))) :
  (∀ᵐ a ∂(μ.map X), integrable (λ ω, f (a, ω)) (cond_distrib Y X μ a))
    ∧ integrable (λ a, ∫ ω, ‖f (a, ω)‖ ∂(cond_distrib Y X μ a)) (μ.map X)
  ↔ integrable f (μ.map (λ a, (X a, Y a))) :=
by rw [cond_distrib, ← hf.ae_integrable_cond_kernel_iff, measure.fst_map_prod_mk₀ hX hY]

variables [normed_space ℝ F] [complete_space F]

lemma _root_.measure_theory.ae_strongly_measurable.integral_cond_distrib_map
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf : ae_strongly_measurable f (μ.map (λ a, (X a, Y a)))) :
  ae_strongly_measurable (λ x, ∫ y, f (x, y) ∂(cond_distrib Y X μ x)) (μ.map X) :=
by { rw [← measure.fst_map_prod_mk₀ hX hY, cond_distrib], exact hf.integral_cond_kernel, }

lemma _root_.measure_theory.ae_strongly_measurable.integral_cond_distrib
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf : ae_strongly_measurable f (μ.map (λ a, (X a, Y a)))) :
  ae_strongly_measurable (λ a, ∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a))) μ :=
(hf.integral_cond_distrib_map hX hY).comp_ae_measurable hX

lemma ae_strongly_measurable'_integral_cond_distrib
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf : ae_strongly_measurable f (μ.map (λ a, (X a, Y a)))) :
  ae_strongly_measurable' (mβ.comap X) (λ a, ∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a))) μ :=
(hf.integral_cond_distrib_map hX hY).comp_ae_measurable' hX

end measurability

section integrability

lemma integrable_to_real_cond_distrib (hX : ae_measurable X μ) (hs : measurable_set s) :
  integrable (λ a, (cond_distrib Y X μ (X a) s).to_real) μ :=
begin
  refine integrable_to_real_of_lintegral_ne_top _ _,
  { exact measurable.comp_ae_measurable (kernel.measurable_coe _ hs) hX, },
  { refine ne_of_lt _,
    calc ∫⁻ a, cond_distrib Y X μ (X a) s ∂μ
        ≤ ∫⁻ a, 1 ∂μ : lintegral_mono (λ a, prob_le_one)
    ... = μ univ : lintegral_one
    ... < ∞ : measure_lt_top _ _, },
end

lemma _root_.measure_theory.integrable.cond_distrib_ae_map
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  ∀ᵐ b ∂(μ.map X), integrable (λ ω, f (b, ω)) (cond_distrib Y X μ b) :=
by { rw [cond_distrib, ← measure.fst_map_prod_mk₀ hX hY], exact hf_int.cond_kernel_ae, }

lemma _root_.measure_theory.integrable.cond_distrib_ae
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  ∀ᵐ a ∂μ, integrable (λ ω, f (X a, ω)) (cond_distrib Y X μ (X a)) :=
ae_of_ae_map hX (hf_int.cond_distrib_ae_map hX hY)

lemma _root_.measure_theory.integrable.integral_norm_cond_distrib_map
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  integrable (λ x, ∫ y, ‖f (x, y)‖ ∂(cond_distrib Y X μ x)) (μ.map X) :=
by { rw [cond_distrib, ← measure.fst_map_prod_mk₀ hX hY], exact hf_int.integral_norm_cond_kernel, }

lemma _root_.measure_theory.integrable.integral_norm_cond_distrib
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  integrable (λ a, ∫ y, ‖f (X a, y)‖ ∂(cond_distrib Y X μ (X a))) μ :=
(hf_int.integral_norm_cond_distrib_map hX hY).comp_ae_measurable hX

variables [normed_space ℝ F] [complete_space F]

lemma _root_.measure_theory.integrable.norm_integral_cond_distrib_map
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  integrable (λ x, ‖∫ y, f (x, y) ∂(cond_distrib Y X μ x)‖) (μ.map X) :=
by { rw [cond_distrib, ← measure.fst_map_prod_mk₀ hX hY], exact hf_int.norm_integral_cond_kernel, }

lemma _root_.measure_theory.integrable.norm_integral_cond_distrib
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  integrable (λ a, ‖∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a))‖) μ :=
(hf_int.norm_integral_cond_distrib_map hX hY).comp_ae_measurable hX

lemma _root_.measure_theory.integrable.integral_cond_distrib_map
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  integrable (λ x, ∫ y, f (x, y) ∂(cond_distrib Y X μ x)) (μ.map X) :=
(integrable_norm_iff (hf_int.1.integral_cond_distrib_map hX hY)).mp
  (hf_int.norm_integral_cond_distrib_map hX hY)

lemma _root_.measure_theory.integrable.integral_cond_distrib
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  integrable (λ a, ∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a))) μ :=
(hf_int.integral_cond_distrib_map hX hY).comp_ae_measurable hX

end integrability

lemma set_lintegral_preimage_cond_distrib (hX : measurable X) (hY : ae_measurable Y μ)
  (hs : measurable_set s) (ht : measurable_set t) :
  ∫⁻ a in X ⁻¹' t, cond_distrib Y X μ (X a) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) :=
by rw [lintegral_comp (kernel.measurable_coe _ hs) hX, cond_distrib,
  ← measure.restrict_map hX ht, ← measure.fst_map_prod_mk₀ hX.ae_measurable hY,
  set_lintegral_cond_kernel_eq_measure_prod _ ht hs,
  measure.map_apply_of_ae_measurable (hX.ae_measurable.prod_mk hY) (ht.prod hs),
  mk_preimage_prod]

lemma set_lintegral_cond_distrib_of_measurable_set (hX : measurable X) (hY : ae_measurable Y μ)
  (hs : measurable_set s) {t : set α} (ht : measurable_set[mβ.comap X] t) :
  ∫⁻ a in t, cond_distrib Y X μ (X a) s ∂μ = μ (t ∩ Y ⁻¹' s) :=
by { obtain ⟨t', ht', rfl⟩ := ht, rw set_lintegral_preimage_cond_distrib hX hY hs ht', }

/-- For almost every `a : α`, the `cond_distrib Y X μ` kernel applied to `X a` and a measurable set
`s` is equal to the conditional expectation of the indicator of `Y ⁻¹' s`. -/
lemma cond_distrib_ae_eq_condexp (hX : measurable X) (hY : measurable Y) (hs : measurable_set s) :
  (λ a, (cond_distrib Y X μ (X a) s).to_real) =ᵐ[μ] μ⟦Y ⁻¹' s | mβ.comap X⟧ :=
begin
  refine ae_eq_condexp_of_forall_set_integral_eq hX.comap_le _ _ _ _,
  { exact (integrable_const _).indicator (hY hs),  },
  { exact λ t ht _, (integrable_to_real_cond_distrib hX.ae_measurable hs).integrable_on, },
  { intros t ht _,
    rw [integral_to_real ((measurable_cond_distrib hs).mono hX.comap_le le_rfl).ae_measurable
        (eventually_of_forall (λ ω, measure_lt_top (cond_distrib Y X μ (X ω)) _)),
      integral_indicator_const _ (hY hs), measure.restrict_apply (hY hs), smul_eq_mul, mul_one,
      inter_comm, set_lintegral_cond_distrib_of_measurable_set hX hY.ae_measurable hs ht], },
  { refine (measurable.strongly_measurable _).ae_strongly_measurable',
    exact @measurable.ennreal_to_real _ (mβ.comap X) _ (measurable_cond_distrib hs), },
end

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `cond_distrib` kernel. -/
lemma condexp_prod_ae_eq_integral_cond_distrib' [normed_space ℝ F] [complete_space F]
  (hX : measurable X) (hY : ae_measurable Y μ)
  (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  μ[(λ a, f (X a, Y a)) | mβ.comap X] =ᵐ[μ] λ a, ∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a)) :=
begin
  have hf_int' : integrable (λ a, f (X a, Y a)) μ,
  { exact (integrable_map_measure hf_int.1 (hX.ae_measurable.prod_mk hY)).mp hf_int, },
  refine (ae_eq_condexp_of_forall_set_integral_eq hX.comap_le hf_int' (λ s hs hμs, _) _ _).symm,
  { exact (hf_int.integral_cond_distrib hX.ae_measurable hY).integrable_on, },
  { rintros s ⟨t, ht, rfl⟩ _,
    change ∫ a in X ⁻¹' t, ((λ x', ∫ y, f (x', y) ∂(cond_distrib Y X μ) x') ∘ X) a ∂μ
      = ∫ a in X ⁻¹' t, f (X a, Y a) ∂μ,
    rw ← integral_map hX.ae_measurable,
    swap,
    { rw ← measure.restrict_map hX ht,
      exact (hf_int.1.integral_cond_distrib_map hX.ae_measurable hY).restrict, },
    rw [← measure.restrict_map hX ht, ← measure.fst_map_prod_mk₀ hX.ae_measurable hY, cond_distrib,
      set_integral_cond_kernel_univ_right ht hf_int.integrable_on,
      set_integral_map (ht.prod measurable_set.univ) hf_int.1 (hX.ae_measurable.prod_mk hY),
      mk_preimage_prod, preimage_univ, inter_univ], },
  { exact ae_strongly_measurable'_integral_cond_distrib hX.ae_measurable hY hf_int.1, },
end

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `cond_distrib` kernel. -/
lemma condexp_prod_ae_eq_integral_cond_distrib₀ [normed_space ℝ F] [complete_space F]
  (hX : measurable X) (hY : ae_measurable Y μ)
  (hf : ae_strongly_measurable f (μ.map (λ a, (X a, Y a))))
  (hf_int : integrable (λ a, f (X a, Y a)) μ) :
  μ[(λ a, f (X a, Y a)) | mβ.comap X] =ᵐ[μ] λ a, ∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a)) :=
begin
  have hf_int' : integrable f (μ.map (λ a, (X a, Y a))),
  { rwa integrable_map_measure hf (hX.ae_measurable.prod_mk hY), },
  exact condexp_prod_ae_eq_integral_cond_distrib' hX hY hf_int',
end

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `cond_distrib` kernel. -/
lemma condexp_prod_ae_eq_integral_cond_distrib [normed_space ℝ F] [complete_space F]
  (hX : measurable X) (hY : ae_measurable Y μ)
  (hf : strongly_measurable f) (hf_int : integrable (λ a, f (X a, Y a)) μ) :
  μ[(λ a, f (X a, Y a)) | mβ.comap X] =ᵐ[μ] λ a, ∫ y, f (X a, y) ∂(cond_distrib Y X μ (X a)) :=
begin
  have hf_int' : integrable f (μ.map (λ a, (X a, Y a))),
  { rwa integrable_map_measure hf.ae_strongly_measurable (hX.ae_measurable.prod_mk hY), },
  exact condexp_prod_ae_eq_integral_cond_distrib' hX hY hf_int',
end

lemma condexp_ae_eq_integral_cond_distrib [normed_space ℝ F] [complete_space F]
  (hX : measurable X) (hY : ae_measurable Y μ)
  {f : Ω → F} (hf : strongly_measurable f) (hf_int : integrable (λ a, f (Y a)) μ) :
  μ[(λ a, f (Y a)) | mβ.comap X] =ᵐ[μ] λ a, ∫ y, f y ∂(cond_distrib Y X μ (X a)) :=
condexp_prod_ae_eq_integral_cond_distrib hX hY (hf.comp_measurable measurable_snd) hf_int

/-- The conditional expectation of `Y` given `X` is almost everywhere equal to the integral
`∫ y, y ∂(cond_distrib Y X μ (X a))`. -/
lemma condexp_ae_eq_integral_cond_distrib' {Ω} [normed_add_comm_group Ω] [normed_space ℝ Ω]
  [complete_space Ω] [measurable_space Ω] [borel_space Ω] [second_countable_topology Ω] {Y : α → Ω}
  (hX : measurable X) (hY_int : integrable Y μ) :
  μ[Y | mβ.comap X] =ᵐ[μ] λ a, ∫ y, y ∂(cond_distrib Y X μ (X a)) :=
condexp_ae_eq_integral_cond_distrib hX hY_int.1.ae_measurable strongly_measurable_id hY_int

lemma _root_.measure_theory.ae_strongly_measurable.comp_snd_map_prod_mk
  {Ω F} {mΩ : measurable_space Ω} {X : Ω → β} {μ : measure Ω}
  [topological_space F] (hX : measurable X) {f : Ω → F} (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x : β × Ω, f x.2) (μ.map (λ ω, (X ω, ω))) :=
begin
  refine ⟨λ x, hf.mk f x.2, hf.strongly_measurable_mk.comp_measurable measurable_snd, _⟩,
  suffices h : measure.quasi_measure_preserving prod.snd (μ.map (λ ω, (X ω, ω))) μ,
  { exact measure.quasi_measure_preserving.ae_eq h hf.ae_eq_mk, },
  refine ⟨measurable_snd, measure.absolutely_continuous.mk (λ s hs hμs, _)⟩,
  rw measure.map_apply _ hs,
  swap, { exact measurable_snd, },
  rw measure.map_apply,
  { rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id'],
    exact hμs, },
  { exact hX.prod_mk measurable_id, },
  { exact measurable_snd hs, },
end

lemma _root_.measure_theory.integrable.comp_snd_map_prod_mk {Ω} {mΩ : measurable_space Ω}
  {X : Ω → β} {μ : measure Ω} (hX : measurable X) {f : Ω → F} (hf_int : integrable f μ) :
  integrable (λ x : β × Ω, f x.2) (μ.map (λ ω, (X ω, ω))) :=
begin
  have hf := hf_int.1.comp_snd_map_prod_mk hX,
  refine ⟨hf, _⟩,
  rw [has_finite_integral, lintegral_map' hf.ennnorm (hX.prod_mk measurable_id).ae_measurable],
  exact hf_int.2,
end

lemma ae_strongly_measurable_comp_snd_map_prod_mk_iff {Ω F} {mΩ : measurable_space Ω}
  [topological_space F] {X : Ω → β} {μ : measure Ω} (hX : measurable X) {f : Ω → F} :
  ae_strongly_measurable (λ x : β × Ω, f x.2) (μ.map (λ ω, (X ω, ω)))
    ↔ ae_strongly_measurable f μ :=
⟨λ h, h.comp_measurable (hX.prod_mk measurable_id), λ h, h.comp_snd_map_prod_mk hX⟩

lemma integrable_comp_snd_map_prod_mk_iff {Ω} {mΩ : measurable_space Ω} {X : Ω → β} {μ : measure Ω}
  (hX : measurable X) {f : Ω → F} :
  integrable (λ x : β × Ω, f x.2) (μ.map (λ ω, (X ω, ω))) ↔ integrable f μ :=
⟨λ h, h.comp_measurable (hX.prod_mk measurable_id), λ h, h.comp_snd_map_prod_mk hX⟩

lemma condexp_ae_eq_integral_cond_distrib_id [normed_space ℝ F] [complete_space F]
  {X : Ω → β} {μ : measure Ω} [is_finite_measure μ]
  (hX : measurable X) {f : Ω → F} (hf_int : integrable f μ) :
  μ[f | mβ.comap X] =ᵐ[μ] λ a, ∫ y, f y ∂(cond_distrib id X μ (X a)) :=
condexp_prod_ae_eq_integral_cond_distrib' hX ae_measurable_id (hf_int.comp_snd_map_prod_mk hX)

end probability_theory
