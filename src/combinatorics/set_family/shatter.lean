/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.basic

/-!
# Shattering families

This file defines the shattering property and VC-dimension of set families.
-/

variables {α : Type*} [decidable_eq α] {𝒜 ℬ : finset (finset α)} {s : finset α} {a : α}

namespace finset


def shatters (𝒜 : finset (finset α)) (s : finset α) : Prop := ∀ ⦃t⦄, t ⊆ s → ∃ u ∈ 𝒜, s ∩ u = t

instance : decidable_pred 𝒜.shatters := λ s, finset.decidable_forall_of_decidable_subsets


variables [fintype α]

/-- The Vapnik-Chervonenkis dimension of a set family -/
def vc_dimension (𝒜 : finset (finset α)) : ℕ := (univ.filter 𝒜.shatters).sup card

example (s : finset α) : shatters.decidable_pred s = (sorry : decidable (𝒜.shatters s)) :=
begin
  unfold shatters.decidable_pred,
end


lemma vc_dimension_ : 𝒜.vc_dimension = 1 :=
begin
  unfold vc_dimension,
end

end finset
