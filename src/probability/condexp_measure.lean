/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.notation

/-!
# Condexp Measure

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



-/

open measure_theory filter
open_locale measure_theory probability_theory ennreal

namespace probability_theory

variables {Ω ι : Type*}

localized "notation (name := expected_value.probability)
  P `⟦` E `|` m `⟧` := P[ E.indicator (λ x, (1 : ℝ)) | m]" in probability_theory

@[simp] lemma condexp_zero' {α F'} {m m0 : measurable_space α} {μ : measure α}
  [normed_add_comm_group F'] [normed_space ℝ F'] [complete_space F'] :
  μ[λ x : α, (0 : F') | m] = 0 :=
condexp_zero

section conditional_probability

variables {m m0 : measurable_space Ω} {μ : measure Ω} {s t : set Ω}

lemma cond_measure_nonneg : 0 ≤ᵐ[μ] μ⟦s | m⟧ :=
condexp_nonneg (eventually_of_forall (λ x, set.indicator_nonneg (λ _ _, zero_le_one) x))

lemma cond_measure_of_measurable (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  μ⟦s | m⟧ = s.indicator (λ _, (1 : ℝ)) :=
begin
  rw condexp_of_strongly_measurable,
  { exact strongly_measurable.indicator strongly_measurable_const hs, },
  { rw [integrable_indicator_iff (hm s hs), integrable_on_const],
    exact or.inr hμs.lt_top, },
end

lemma cond_measure_empty (hm : m ≤ m0) [sigma_finite (μ.trim hm)] :
  μ⟦(∅ : set Ω) | m⟧ = λ ω, (0 : ℝ) :=
begin
  rw [cond_measure_of_measurable hm (@measurable_set.empty _ m), set.indicator_empty],
  { rw measure_empty,
    exact ennreal.zero_ne_top, },
  { apply_instance, },
end

lemma cond_measure_univ (hm : m ≤ m0) [is_finite_measure μ] : μ⟦set.univ | m⟧ = λ ω, (1 : ℝ) :=
by rw [cond_measure_of_measurable hm measurable_set.univ (measure_ne_top μ _), set.indicator_univ]

lemma cond_measure_mono (hst : s ⊆ t)
  (hs : measurable_set s) (ht : measurable_set t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) :
  μ⟦s | m⟧ ≤ᵐ[μ] μ⟦t | m⟧ :=
begin
  refine condexp_mono _ _ (eventually_of_forall (λ x, _)),
  { rw [integrable_indicator_iff hs, integrable_on_const],
    exact or.inr hμs.lt_top, },
  { rw [integrable_indicator_iff ht, integrable_on_const],
    exact or.inr hμt.lt_top, },
  by_cases hxs : x ∈ s,
  { simp [hxs, hst hxs], },
  { simp only [hxs, set.indicator_of_not_mem, not_false_iff],
    exact set.indicator_nonneg (λ _ _, zero_le_one) x, },
end

lemma cond_measure_le_measure_univ [is_finite_measure μ] (hs : measurable_set s) :
  μ⟦s | m⟧ ≤ᵐ[μ] λ ω, (1 : ℝ) :=
begin
  by_cases hμ : μ = 0,
  { simp only [hμ, ae_zero], },
  haveI : μ.ae.ne_bot := ae_ne_bot.mpr hμ,
  by_cases hm : m ≤ m0,
  swap, { rw [condexp_of_not_le hm], exact eventually_of_forall (λ _, zero_le_one), },
  refine (cond_measure_mono (set.subset_univ _) hs measurable_set.univ (measure_ne_top _ _)
    (measure_ne_top _ _)).trans _,
  rw cond_measure_univ hm,
  apply_instance,
end

lemma cond_measure_union_of_disjoint [is_finite_measure μ]
  (h : disjoint s t) (hs : measurable_set s) (ht : measurable_set t) :
  μ⟦s ∪ t | m⟧ =ᵐ[μ] μ⟦s | m⟧ + μ⟦t | m⟧ :=
begin
  rw set.indicator_union_of_disjoint h,
  exact condexp_add ((integrable_const _).indicator hs) ((integrable_const _).indicator ht),
end

-- this is a `Ω → measure Ω`. Under suitable conditions (standard Borel space) this could be a
-- `kernel Ω Ω`
noncomputable
def condexp_to_measure {m m0 : measurable_space Ω} (μ : measure Ω)
  (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (ω : Ω) :
  measure Ω :=
measure.of_measurable (λ s hs, ennreal.of_real (μ⟦s | m⟧ ω))
  (by simp only [set.indicator_empty, condexp_zero', pi.zero_apply, ennreal.of_real_zero])
  begin
    intros f hf_meas hf_disj,
    sorry
  end

end conditional_probability

end probability_theory
