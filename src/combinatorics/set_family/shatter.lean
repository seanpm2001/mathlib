/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import combinatorics.set_family.compression.down
import data.nat.interval
import order.upper_lower

/-!
# Shattering families

This file defines the shattering property and VC-dimension of set families.

## Main declarations

* `finset.shatter`: The shattering property.
* `finset.shatterer`: The set family of sets shattered by a set family.
* `finset.vc_dimension`: The Vapnik-Chervonenkis dimension.
-/

section
variables {α : Type*} [semilattice_sup α] {a b c : α}

lemma sup_congr_left (hb : b ≤ a ⊔ c) (hc : c ≤ a ⊔ b) : a ⊔ b = a ⊔ c :=
(sup_le le_sup_left hb).antisymm $ sup_le le_sup_left hc

lemma sup_congr_right (hb : b ≤ c ⊔ a) (hc : c ≤ b ⊔ a) : b ⊔ a = c ⊔ a :=
(sup_le hb le_sup_right).antisymm $ sup_le hc le_sup_right

end

section
variables {α : Type*} [semilattice_inf α] {a b c : α}

lemma inf_congr_left (hb : a ⊓ c ≤ b) (hc : a ⊓ b ≤ c) : a ⊓ b = a ⊓ c :=
(le_inf inf_le_left hc).antisymm $ le_inf inf_le_left hb

lemma inf_congr_right (hb : c ⊓ a ≤ b) (hc : b ⊓ a ≤ c) : b ⊓ a = c ⊓ a :=
(le_inf hc inf_le_right).antisymm $ le_inf hb inf_le_right

end

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
and some element of the set family. We also say that `s` is traced by `𝒜`. -/
def shatter (𝒜 : finset (finset α)) (s : finset α) : Prop := ∀ ⦃t⦄, t ⊆ s → ∃ u ∈ 𝒜, s ∩ u = t

instance : decidable_pred 𝒜.shatter := λ s, finset.decidable_forall_of_decidable_subsets

lemma shatter.mono_left (h : 𝒜 ⊆ ℬ) (h𝒜 : 𝒜.shatter s) : ℬ.shatter s :=
λ t ht, let ⟨u, hu, hut⟩ := h𝒜 ht in ⟨u, h hu, hut⟩

lemma shatter.mono_right (h : t ⊆ s) (hs : 𝒜.shatter s) : 𝒜.shatter t :=
λ u hu, by { obtain ⟨v, hv, rfl⟩ := hs (hu.trans h),
  exact ⟨v, hv, inf_congr_right hu $ inf_le_of_left_le h⟩ }

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

/-- The set family of sets that are shattered by `𝒜`. -/
def shatterer (𝒜 : finset (finset α)) : finset (finset α) := (𝒜.bUnion powerset).filter 𝒜.shatter

@[simp] lemma mem_shatterer : s ∈ 𝒜.shatterer ↔ 𝒜.shatter s :=
begin
  refine mem_filter.trans (and_iff_right_of_imp $ λ h, _),
  simp_rw [mem_bUnion, mem_powerset],
  exact h.exists_superset,
end

lemma shatterer_mono (h : 𝒜 ⊆ ℬ) : 𝒜.shatterer ⊆ ℬ.shatterer :=
λ _, by simpa using shatter.mono_left h

lemma subset_shatterer (h : is_lower_set (𝒜 : set (finset α))) : 𝒜 ⊆ 𝒜.shatterer :=
λ s hs, mem_shatterer.2 $ λ t ht, ⟨t, h ht hs, (inter_eq_right_iff_subset _ _).2 ht⟩

@[simp] lemma is_lower_set_shatterer (𝒜 : finset (finset α)) :
  is_lower_set (𝒜.shatterer : set (finset α)) :=
λ s t, by simpa using shatter.mono_right

@[simp] lemma shatterer_eq : 𝒜.shatterer = 𝒜 ↔ is_lower_set (𝒜 : set (finset α)) :=
begin
  refine ⟨λ h, _, λ h, subset.antisymm (λ s hs, _) $ subset_shatterer h⟩,
  { rw ←h,
    exact is_lower_set_shatterer _ },
  { obtain ⟨t, ht, hst⟩ := (mem_shatterer.1 hs).exists_superset,
    exact h hst ht }
end

@[simp] lemma shatterer_idem : 𝒜.shatterer.shatterer = 𝒜.shatterer := by simp

@[simp] lemma shatter_shatterer : 𝒜.shatterer.shatter s ↔ 𝒜.shatter s :=
by simp_rw [←mem_shatterer, shatterer_idem]

alias shatter_shatterer ↔ _ shatter.shatterer

attribute [protected] shatter.shatterer

section order
variables [linear_order α]


def order_shatter : finset (finset α) → list α → Prop
| 𝒜 [] := 𝒜.nonempty
| 𝒜 (a :: l) := (𝒜.non_member_section a).order_shatter l ∧ (𝒜.member_section a).order_shatter l ∧
  ∀ ⦃s : finset α⦄, s ∈ 𝒜.non_member_section a → ∀ ⦃t⦄, t ∈ 𝒜.member_section a →
    s.filter (λ b, a < b) = t.filter (λ b, a < b)

instance : decidable_pred 𝒜.order_shatter := sorry

def order_shatterer (𝒜 : finset (finset α)) : finset (finset α) :=
(𝒜.bUnion powerset).filter $ λ s, 𝒜.order_shatter $ s.sort (≤)

end order

def strongly_shatter (𝒜 : finset (finset α)) (s : finset α) : Prop :=
∃ t, ∀ ⦃u⦄, u ⊆ s → ∃ v ∈ 𝒜, s ∩ v = u ∧ v \ s = t

/-- Pajor's variant of the **Sauer-Shelah lemma**. -/
lemma le_card_shatterer (𝒜 : finset (finset α)) : 𝒜.card ≤ 𝒜.shatterer.card :=
begin
  induction 𝒜 using finset.strong_induction with 𝒜 ih,
  obtain rfl | h𝒜 := 𝒜.eq_empty_or_nonempty,
  { exact bot_le },

  sorry
end

variables [fintype α]

/-- The Vapnik-Chervonenkis dimension of a set family is the maximal size of a set it shatters. -/
def vc_dimension (𝒜 : finset (finset α)) : ℕ := (univ.filter 𝒜.shatter).sup card

lemma shatter.card_le_vc_dimension (h : 𝒜.shatter s) : s.card ≤ 𝒜.vc_dimension :=
finset.le_sup $ mem_filter.2 ⟨mem_univ _, h⟩

/-- Down-compressing decreases the VC-dimension. -/
lemma vc_dimension_compress_le (a : α) (𝒜 : finset (finset α)) :
  (𝓓 a 𝒜).vc_dimension ≤ 𝒜.vc_dimension :=
sorry

/-- The **Sauer-Shelah lemma**. -/
lemma card_shatterer_le_sum_vc_dimension :
  𝒜.shatterer.card ≤ ∑ k in Iic 𝒜.vc_dimension, (fintype.card α).choose k :=
begin
  simp_rw [←card_univ, ←card_powerset_len],
  refine ((card_le_of_subset $ λ s hs, mem_bUnion.2 ⟨card s, _⟩).trans $ card_bUnion_le),
  exact ⟨mem_Iic.2 (mem_shatterer.1 hs).card_le_vc_dimension, mem_powerset_len_univ_iff.2 rfl⟩,
end

end finset
