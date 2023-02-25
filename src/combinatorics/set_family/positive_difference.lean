/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.pointwise
import data.set.intervals.ord_connected
import order.upper_lower

/-!
# Positive difference

This file defines the positive difference of set families and sets in an ordered additive group.

## Main declarations

* `finset.positive_sdiff`: Positive difference of set families.
* `finset.positive_sub`: Positive difference of sets in an ordered additive group.

## Notations

We declare the following notation in the `finset_family` locale:
* `s \₊ t` for `finset.positive_sdiff s t`
* `s -₊ t` for `finset.positive_sub s t`

## References

* [Bollobás, Leader, Radcliffe, *Reverse Kleitman Inequalities][bollobasleaderradcliffe1989]
-/

open_locale pointwise

variables {α : Type*}

namespace finset

@[elab_as_eliminator]
protected lemma family_induction_on {p : finset (finset α) → Prop} [decidable_eq α]
  (𝒜 : finset (finset α)) (h₀ : p ∅)
  (h₁ : ∀ ⦃a : α⦄ ⦃𝒜 : finset (finset α)⦄, (∀ s ∈ 𝒜, a ∉ s) → p 𝒜 → p (𝒜.image $ insert a))
  (h₂ : ∀ ⦃a : α⦄ ⦃𝒜 : finset (finset α)⦄, p (𝒜.filter ((∉) a)) → p (𝒜.filter ((∈) a)) → p 𝒜) :
  p 𝒜 :=
sorry

end finset

namespace finset

/-! ### Positive set difference -/

section positive_sdiff
section boolean_algebra
variables [generalized_boolean_algebra α] [@decidable_rel α (≤)] [decidable_eq α] {s t : finset α}
  {a : α}

/-- The positive set difference of finsets `s` and `t` is the set of `a \ b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def positive_sdiff (s t : finset α) : finset α :=
((s.product t).filter $ λ x : α × α, x.2 ≤ x.1).image (λ x, x.1 \ x.2)

localized "infix ` \\₊ `:70   := finset.positive_sdiff" in finset_family

@[simp] lemma mem_positive_sdiff : a ∈ s \₊ t ↔ ∃ (b ∈ s) (c ∈ t), c ≤ b ∧ b \ c = a :=
by simp_rw [positive_sdiff, mem_image, mem_filter, mem_product, exists_prop, prod.exists, and_assoc,
  exists_and_distrib_left]

@[simp] lemma positive_sdiff_empty (s : finset α) : s \₊ ∅ = ∅ := by simp [positive_sdiff]
@[simp] lemma empty_positive_sdiff (s : finset α) : ∅ \₊ s = ∅ := by simp [positive_sdiff]

end boolean_algebra

open_locale finset_family

section finset
variables [decidable_eq α] {𝒜 ℬ : finset (finset α)}

lemma card_positive_sdiff_self_le (h𝒜 : (𝒜 : set (finset α)).ord_connected) :
  (𝒜 \₊ 𝒜).card ≤ 𝒜.card :=
begin
  unfreezingI { revert h𝒜 },
  refine finset.family_induction_on 𝒜 _ _ _, clear 𝒜,
  { simp },
  {
    rintro a 𝒜 h𝒜,
  }
end

/-- A **reverse Kleitman inequality**. -/
lemma le_card_upper_inter_lower (h𝒜 : is_lower_set (𝒜 : set (finset α)))
  (hℬ : is_upper_set (ℬ : set (finset α))) :
  (𝒜 \₊ ℬ).card ≤ (𝒜 ∩ ℬ).card :=
begin
  refine (card_le_of_subset _).trans (card_positive_sdiff_self_le _),
  { simp_rw [subset_iff, mem_positive_sdiff, mem_inter],
    rintro _ ⟨s, hs, t, ht, hts, rfl⟩,
    exact ⟨s, ⟨hs, hℬ hts ht⟩, t, ⟨h𝒜 hts hs, ht⟩, hts, rfl⟩ },
  { rw coe_inter,
    exact h𝒜.ord_connected.inter hℬ.ord_connected }
end

end finset
end positive_sdiff

/-! ### Positive subtraction -/

section positive_sub
variables [has_sub α] [preorder α] [@decidable_rel α (≤)] [decidable_eq α] {s t : finset α} {a : α}

/-- The positive subtraction of finsets `s` and `t` is the set of `a - b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def positive_sub (s t : finset α) : finset α :=
((s.product t).filter $ λ x : α × α, x.2 ≤ x.1).image (λ x, x.1 - x.2)

localized "infix ` -₊ `:70   := finset.positive_sub" in finset_family

lemma mem_positive_sub : a ∈ s -₊ t ↔ ∃ (b ∈ s) (c ∈ t), c ≤ b ∧ b - c = a :=
by simp_rw [positive_sub, mem_image, mem_filter, mem_product, exists_prop, prod.exists, and_assoc,
  exists_and_distrib_left]

lemma positive_sub_subset_sub : s -₊ t ⊆ s - t :=
λ x, by { rw [mem_positive_sub, mem_sub], exact λ ⟨b, hb, c, hc, _, h⟩, ⟨b, c, hb, hc, h⟩ }

lemma card_positive_sub_self_le (hs : (s : set α).ord_connected) : (s -₊ s).card ≤ s.card := sorry

end positive_sub
end finset
