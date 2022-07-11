/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import combinatorics.set_family.compression.down
import data.nat.interval

/-!
# Shattering families

This file defines the shattering property and VC-dimension of set families.

## Main declarations

* `finset.shatter`: The shattering property.
* `finset.vc_dimension`: The Vapnik-Chervonenkis dimension.
-/

namespace finset
variables {α : Type*}

@[simp, norm_cast] lemma coe_powerset (s : finset α) :
  (s.powerset : set (finset α)) = coe ⁻¹' (s : set α).powerset :=
by { ext, simp }

variables [fintype α]

@[simp] lemma powerset_univ : (univ : finset α).powerset = univ :=
coe_injective $ by simp [-coe_eq_univ]

end finset

open_locale big_operators finset_family

namespace finset
variables {α : Type*} [decidable_eq α] {𝒜 ℬ : finset (finset α)} {s t : finset α} {a : α} {n : ℕ}

/-- A set family shatters a set `s` if all subsets of `s` can be obtained as the intersection of `s`
and some element of the set family. -/
def shatter (𝒜 : finset (finset α)) (s : finset α) : Prop := ∀ ⦃t⦄, t ⊆ s → ∃ u ∈ 𝒜, s ∩ u = t

instance : decidable_pred 𝒜.shatter := λ s, finset.decidable_forall_of_decidable_subsets

lemma shatter.exists_superset (h : 𝒜.shatter s) : ∃ t ∈ 𝒜, s ⊆ t :=
Exists₂.imp (λ t _, (inter_eq_left_iff_subset _ _).1) (h subset.rfl)

lemma shatter_of_forall_subset (h : ∀ t ⊆ s, t ∈ 𝒜) : 𝒜.shatter s :=
λ t ht, ⟨t, h _ ht, (inter_eq_right_iff_subset _ _).2 ht⟩

protected lemma shatter.nonempty (h : 𝒜.shatter s) : 𝒜.nonempty :=
let ⟨t, ht, _⟩ := h subset.rfl in ⟨t, ht⟩

@[simp] lemma shatter_empty : 𝒜.shatter ∅ ↔ 𝒜.nonempty :=
⟨shatter.nonempty, λ ⟨s, hs⟩ t ht, ⟨s, hs, by rwa [empty_inter, eq_comm, ←subset_empty]⟩⟩

protected lemma shatter.iff (h : 𝒜.shatter s) : t ⊆ s ↔ ∃ u ∈ 𝒜, s ∩ u = t :=
⟨λ ht, h ht, by { rintro ⟨u, hu, rfl⟩, exact inter_subset_left _ _ }⟩

lemma shatter_iff : 𝒜.shatter s ↔ 𝒜.image (λ t, s ∩ t) = s.powerset :=
⟨λ h, by { ext t, rw [mem_image, mem_powerset, h.iff] },
  λ h t ht, by rwa [←mem_powerset, ←h, mem_image] at ht⟩

lemma univ_shatter [fintype α] : univ.shatter s := shatter_of_forall_subset $ λ _ _, mem_univ _

@[simp] lemma shatter_univ [fintype α] : 𝒜.shatter univ ↔ 𝒜 = univ :=
by { rw [shatter_iff, powerset_univ], simp_rw [univ_inter, image_id'] }

/-- Pajor's variant of the **Sauer-Shelah lemma**. -/
lemma exists_forall_shatter (𝒜 : finset (finset α)) :
  ∃ ℬ : finset (finset α), 𝒜.card ≤ ℬ.card ∧ ∀ s ∈ ℬ, 𝒜.shatter s :=
begin
  induction 𝒜 using finset.strong_induction with 𝒜 ih,
  sorry
end

variables [fintype α]

/-- The Vapnik-Chervonenkis dimension of a set family is the maximal size of the sets it shatters.-/
def vc_dimension (𝒜 : finset (finset α)) : ℕ := (univ.filter 𝒜.shatter).sup card

lemma shatter.card_le_vc_dimension (h : 𝒜.shatter s) : s.card ≤ 𝒜.vc_dimension :=
finset.le_sup $ mem_filter.2 ⟨mem_univ _, h⟩

/-- Down-compressing decreases the VC-dimension. -/
lemma vc_dimension_compress_le (a : α) (𝒜 : finset (finset α)) :
  (𝓓 a 𝒜).vc_dimension ≤ 𝒜.vc_dimension :=
sorry

/-- The **Sauer-Shelah** lemma. -/
lemma card_le_sum_vc_dimension : 𝒜.card ≤ ∑ k in Iic 𝒜.vc_dimension, (fintype.card α).choose k :=
begin
  simp_rw [←card_univ, ←card_powerset_len],
  obtain ⟨ℬ, hℬ𝒜, h⟩ := 𝒜.exists_forall_shatter,
  refine hℬ𝒜.trans ((card_le_of_subset $ λ s hs, mem_bUnion.2 _).trans $ card_bUnion_le),
  exact ⟨s.card, mem_Iic.2 (h _ hs).card_le_vc_dimension, mem_powerset_len_univ_iff.2 rfl⟩,
end

end finset
