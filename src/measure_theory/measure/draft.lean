/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.measure.measure_space_def

/-!
# Draft

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open filter

open_locale ennreal topology big_operators

namespace measure_theory

namespace measure

variables {α : Type*} [measurable_space α]

lemma measurable_set.accumulate {s : ℕ → set α} (hs : ∀ n, measurable_set (s n)) (n : ℕ) :
  measurable_set (set.accumulate s n) :=
measurable_set.bUnion (set.to_countable _) (λ n _, hs n)

lemma ennreal.tendsto_at_top_zero_const_sub_iff (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞) (ha : a ≠ ∞)
  (hfa : ∀ n, f n ≤ a) :
  tendsto (λ n, a - f n) at_top (𝓝 0) ↔ tendsto (λ n, f n) at_top (𝓝 a) :=
begin
  rw [ennreal.tendsto_at_top_zero, ennreal.tendsto_at_top ha],
  swap, { apply_instance, },
  refine ⟨λ h ε hε, _, λ h ε hε, _⟩; obtain ⟨N, hN⟩ := h ε hε,
  { refine ⟨N, λ n hn, ⟨_, (hfa n).trans (le_add_right le_rfl)⟩⟩,
    specialize hN n hn,
    rw tsub_le_iff_right at hN ⊢,
    rwa add_comm, },
  { refine ⟨N, λ n hn, _⟩,
    have hN_left := (hN n hn).1,
    rw tsub_le_iff_right at hN_left ⊢,
    rwa add_comm, },
end

lemma set.accumulate_subset_Union (s : ℕ → set α) (n : ℕ) :
  set.accumulate s n ⊆ ⋃ i, s i :=
by { simp_rw [set.accumulate_def, set.Union_subset_iff], exact λ i _, set.subset_Union s i, }

/-- todo: this has to be somewhere -/
lemma set.bUnion_le_succ (s : ℕ → set α) (n : ℕ) :
  (⋃ i ≤ n.succ, s i) = (⋃ i ≤ n, s i) ∪ s n.succ :=
begin
  ext1 x,
  simp only [set.mem_Union, exists_prop, set.mem_union],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨i, hi_le, hxi⟩ := h,
    cases hi_le with hi_eq hi_le,
    { exact or.inr hxi, },
    { exact or.inl ⟨i, hi_le, hxi⟩, }, },
  { cases h with h h,
    { obtain ⟨i, hi_le, hxi⟩ := h,
      exact ⟨i, hi_le.trans (nat.lt_succ_self _).le, hxi⟩, },
    { exact ⟨n.succ, le_rfl, h⟩, }, },
end

lemma set.disjoint_accumulate {s : ℕ → set α} (hs : pairwise (disjoint on s)) {i j : ℕ}
  (hij : i < j) :
  disjoint (set.accumulate s i) (s j) :=
begin
  rw set.accumulate_def,
  induction i with i hi,
  { simp only [le_zero_iff, set.Union_Union_eq_left],
    exact hs hij.ne, },
  { rw set.bUnion_le_succ s i,
    refine disjoint.union_left _ _,
    { exact hi ((nat.lt_succ_self i).trans hij), },
    { exact hs hij.ne, }, },
end

lemma countably_additive_of_todo (m : Π (s : set α), measurable_set s → ℝ≥0∞)
  (hm_ne_top : ∀ s (hs : measurable_set s), m s hs ≠ ∞)
  (hm_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t),
    disjoint s t → m (s ∪ t) (hs.union ht) = m s hs + m t ht)
  (hm : ∀ (s : ℕ → set α) (hs : ∀ n, measurable_set (s n)),
    antitone s → (⋂ n, s n) = ∅ → tendsto (λ n, m (s n) (hs n)) at_top (𝓝 0))
  ⦃f : ℕ → set α⦄ (h : ∀ i, measurable_set (f i)) (h_disj : pairwise (disjoint on f)) :
    m (⋃ i, f i) (measurable_set.Union h) = ∑' i, m (f i) (h i) :=
begin
  have h_meas_Union : measurable_set (⋃ i, f i) := measurable_set.Union h,
  have hm_diff : ∀ s t (hs : measurable_set s) (ht : measurable_set t),
    t ⊆ s → m (s \ t) (hs.diff ht) = m s hs - m t ht,
  { intros s t hs ht hst,
    have h_union := hm_add t (s \ t) ht (hs.diff ht) disjoint_sdiff_self_right,
    simp_rw [set.union_diff_self, set.union_eq_right_iff_subset.mpr hst] at h_union,
    rw [h_union, ennreal.add_sub_cancel_left (hm_ne_top t ht)], },
  have hm_mono : ∀ s t (hs : measurable_set s) (ht : measurable_set t),
    t ⊆ s → m t ht ≤ m s hs,
  { intros s t hs ht hst,
    have h_union := hm_add t (s \ t) ht (hs.diff ht) disjoint_sdiff_self_right,
    simp_rw [set.union_diff_self, set.union_eq_right_iff_subset.mpr hst] at h_union,
    rw h_union,
    exact le_add_right le_rfl, },
  have hm_acc : ∀ (s : ℕ → set α) (h_disj : pairwise (disjoint on s))
    (h_meas : ∀ i, measurable_set (s i)) (n : ℕ),
    m (set.accumulate s n) (measurable_set.accumulate h_meas n)
      = ∑ i in finset.range (n + 1), m (s i) (h_meas i),
  { intros s hs_disj hs_meas n,
    simp_rw set.accumulate_def,
    induction n with n hn,
    { simp only [le_zero_iff, set.Union_Union_eq_left, finset.range_one, finset.sum_singleton], },
    rw [finset.sum_range_succ, ← hn],
    simp_rw [set.bUnion_le_succ],
    rw hm_add,
    exact set.disjoint_accumulate hs_disj (nat.lt_succ_self n), },
  let s : ℕ → set α := λ n, (⋃ i, f i) \ (set.accumulate f n),
  have hf_meas_acc : ∀ n, measurable_set (set.accumulate f n) := measurable_set.accumulate h,
  have hs_meas : ∀ n, measurable_set (s n) := λ n, h_meas_Union.diff (hf_meas_acc n),
  have hs_anti : antitone s,
  { intros i j hij x hxj,
    rw set.mem_diff at hxj ⊢,
    exact ⟨hxj.1, λ hxi, hxj.2 (set.monotone_accumulate hij hxi)⟩, },
  have hs_Inter : (⋂ n, s n) = ∅,
  { simp_rw [s, set.diff_eq],
    rw [set.Inter_inter_distrib, set.Inter_const, ← set.compl_Union, set.Union_accumulate],
    exact set.inter_compl_self _, },
  have h_tendsto : tendsto (λ n, m (s n) (hs_meas n)) at_top (𝓝 0) :=
    hm s hs_meas hs_anti hs_Inter,
  have hmsn : ∀ n, m (s n) (hs_meas n)
    = m (⋃ i, f i) h_meas_Union - ∑ i in finset.range (n + 1), m (f i) (h i),
  { intro n,
    simp_rw s,
    rw hm_diff _ _ h_meas_Union (hf_meas_acc n),
    { congr,
      exact hm_acc _ h_disj _ n, },
    { exact set.accumulate_subset_Union _ _, }, },
  simp_rw hmsn at h_tendsto,
  have h_tendsto' : tendsto (λ n, ∑ i in finset.range n, m (f i) (h i)) at_top
    (𝓝 (m (⋃ i, f i) h_meas_Union)),
  { refine (filter.tendsto_add_at_top_iff_nat 1).mp _,
    rwa ennreal.tendsto_at_top_zero_const_sub_iff _ _ (hm_ne_top _ _) at h_tendsto,
    intros n,
    rw ← hm_acc _ h_disj,
    exact hm_mono _ _ _ _ (set.accumulate_subset_Union _ _), },
  exact tendsto_nhds_unique h_tendsto' (ennreal.tendsto_nat_tsum (λ i, m (f i) (h i))),
end

/-- todo name. Or don't define this, use of_measurable directly -/
noncomputable def of_measurable' (m : Π (s : set α), measurable_set s → ℝ≥0∞)
  (m0 : m ∅ measurable_set.empty = 0)
  (hm_ne_top : ∀ s (hs : measurable_set s), m s hs ≠ ∞)
  (hm_add : ∀ (s t : set α) (hs : measurable_set s) (ht : measurable_set t),
    disjoint s t → m (s ∪ t) (hs.union ht) = m s hs + m t ht)
  (hm : ∀ (s : ℕ → set α) (hs : ∀ n, measurable_set (s n)),
    antitone s → (⋂ n, s n) = ∅ → tendsto (λ n, m (s n) (hs n)) at_top (𝓝 0)) :
  measure α :=
of_measurable m m0 (countably_additive_of_todo m hm_ne_top hm_add hm)

end measure

end measure_theory
