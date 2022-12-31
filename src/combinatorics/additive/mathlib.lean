/-
Copyright (c) 2022 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import data.finset.pointwise
import data.set.pointwise.finite
import group_theory.quotient_group

namespace function
variables {α β γ : Type*}

@[simp] lemma on_fun_apply (f : β → β → γ) (g : α → β) (a b : α) :
  on_fun f g a b = f (g a) (g b) := rfl

end function

--TODO: Fix implicitness `finset.not_subset`

section generalized_boolean_algebra
variables {α : Type*} [generalized_boolean_algebra α] {a b c : α}

lemma le_sdiff : a ≤ b \ c ↔ a ≤ b ∧ disjoint a c :=
⟨λ h, ⟨h.trans sdiff_le, disjoint_sdiff_self_left.mono_left h⟩, λ h,
  by { rw ←h.2.sdiff_eq_left, exact sdiff_le_sdiff_right h.1 }⟩

@[simp] lemma sdiff_eq_left : a \ b = a ↔ disjoint a b :=
⟨λ h, disjoint_sdiff_self_left.mono_left h.ge, disjoint.sdiff_eq_left⟩

end generalized_boolean_algebra

section canonically_ordered_monoid
variables {α : Type*} [canonically_ordered_monoid α] {a b c : α}

@[to_additive] lemma le_mul_of_le_left : a ≤ b → a ≤ b * c := le_self_mul.trans'
@[to_additive] lemma le_mul_of_le_right : a ≤ c → a ≤ b * c := le_mul_self.trans'

end canonically_ordered_monoid

attribute [to_additive] finset.bUnion_smul_finset

section subset
variables {α : Type*} [has_subset α] {a b c : α}

lemma subset_of_eq_of_subset (hab : a = b) (hbc : b ⊆ c) : a ⊆ c := by rwa hab
lemma subset_of_subset_of_eq (hab : a ⊆ b) (hbc : b = c) : a ⊆ c := by rwa ←hbc

alias subset_of_eq_of_subset ← eq.trans_subset
alias subset_of_subset_of_eq ← has_subset.subset.trans_eq

end subset

section ssubset
variables {α : Type*} [has_ssubset α] {a b c : α}

lemma ssubset_of_eq_of_ssubset (hab : a = b) (hbc : b ⊂ c) : a ⊂ c := by rwa hab
lemma ssubset_of_ssubset_of_eq (hab : a ⊂ b) (hbc : b = c) : a ⊂ c := by rwa ←hbc

alias ssubset_of_eq_of_ssubset ← eq.trans_ssubset
alias ssubset_of_ssubset_of_eq ← has_ssubset.ssubset.trans_eq

end ssubset

namespace set
variables {α : Type*} {s : set α}

lemma nonempty.exists_eq_singleton_or_nontrivial : s.nonempty → (∃ a, s = {a}) ∨ s.nontrivial :=
λ ⟨a, ha⟩, (eq_singleton_or_nontrivial ha).imp_left $ exists.intro a

end set

namespace finset
variables {α : Type*} {s : finset α}

lemma nonempty.exists_eq_singleton_or_nontrivial :
  s.nonempty → (∃ a, s = {a}) ∨ (s : set α).nontrivial :=
λ ⟨a, ha⟩, (eq_singleton_or_nontrivial ha).imp_left $ exists.intro a

end finset

namespace finset
variables {α : Type*} [decidable_eq α] {s t u : finset α}

lemma card_inter_add_card_union (s t : finset α) : (s ∩ t).card + (s ∪ t).card = s.card + t.card :=
by rw [add_comm, card_union_add_card_inter]

lemma not_disjoint_iff_nonempty_inter : ¬disjoint s t ↔ (s ∩ t).nonempty :=
not_disjoint_iff.trans $ by simp [finset.nonempty]

alias not_disjoint_iff_nonempty_inter ↔ _ nonempty.not_disjoint

lemma disjoint_or_nonempty_inter (s t : finset α) : disjoint s t ∨ (s ∩ t).nonempty :=
by { rw ←not_disjoint_iff_nonempty_inter, exact em _ }

lemma inter_subset_union : s ∩ t ⊆ s ∪ t := le_iff_subset.1 inf_le_sup

lemma subset_sdiff : s ⊆ t \ u ↔ s ⊆ t ∧ disjoint s u :=
le_iff_subset.symm.trans le_sdiff

end finset

namespace finset
variables {α : Type*} {s t : finset α}

lemma subset_iff_eq_of_card_le (h : t.card ≤ s.card) : s ⊆ t ↔ s = t :=
⟨λ hst, eq_of_subset_of_card_le hst h, eq.subset'⟩

end finset

namespace set
variables {β : Type*} {ι : Sort*} [nonempty ι] {f : ι → set β} {s : set β}

lemma Union_eq_const (hf : ∀ i, f i = s) : (⋃ i, f i) = s := (Union_congr hf).trans $ Union_const _
lemma Inter_eq_const (hf : ∀ i, f i = s) : (⋂ i, f i) = s := (Inter_congr hf).trans $ Inter_const _

end set

namespace set
variables {α : Type*} {s : set α} {a : α}

lemma nontrivial_iff_ne_singleton (ha : a ∈ s) : s.nontrivial ↔ s ≠ {a} :=
⟨nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

end set

namespace finset
variables {α : Type*} {s : finset α} {a : α}

/-- A finset is nontrivial if it has at least two elements. -/
@[reducible] protected def nontrivial' (s : finset α) : Prop := (s : set α).nontrivial

@[simp] lemma not_nontrivial_empty : ¬ (∅ : finset α).nontrivial' := by simp [finset.nontrivial']

@[simp] lemma not_nontrivial_singleton : ¬ ({a} : finset α).nontrivial' :=
by simp [finset.nontrivial']

lemma nontrivial'.ne_singleton (hs : s.nontrivial') : s ≠ {a} :=
by { rintro rfl, exact not_nontrivial_singleton hs }

lemma nontrivial_iff_ne_singleton (ha : a ∈ s) : s.nontrivial' ↔ s ≠ {a} :=
⟨nontrivial'.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

lemma nontrivial'.one_lt_card : s.nontrivial' → 1 < s.card := finset.one_lt_card.2

end finset

namespace set
variables {α β γ : Type*} {f : α → β → γ} {s : set α} {t : set β} {u : set γ}

@[simp]
lemma to_finset_image [decidable_eq β] (f : α → β) (s : set α) [fintype s] [fintype (f '' s)] :
  (f '' s).to_finset = s.to_finset.image f :=
finset.coe_injective $ by simp

@[simp]
lemma to_finset_image2 [decidable_eq γ] (f : α → β → γ) (s : set α) (t : set β) [fintype s]
  [fintype t] [fintype (image2 f s t)] :
  (image2 f s t).to_finset = finset.image₂ f s.to_finset t.to_finset :=
finset.coe_injective $ by simp

lemma finite.to_finset_image [decidable_eq β] (f : α → β) (hs : s.finite) (hf := hs.image f) :
  hf.to_finset = hs.to_finset.image f :=
finset.coe_injective $ by simp

lemma finite.to_finset_image2 [decidable_eq γ] (f : α → β → γ) (hs : s.finite) (ht : t.finite)
  (hf := hs.image2 f ht) :
  hf.to_finset = finset.image₂ f hs.to_finset ht.to_finset :=
finset.coe_injective $ by simp

lemma image2_subset_iff_left : image2 f s t ⊆ u ↔ ∀ a ∈ s, f a '' t ⊆ u :=
by simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage]

lemma image2_subset_iff_right : image2 f s t ⊆ u ↔ ∀ b ∈ t, (λ a, f a b) '' s ⊆ u :=
by rw [image2_swap, image2_subset_iff_left]

end set

namespace finset
variables {α β γ : Type*} [decidable_eq γ] {f : α → β → γ} {s : finset α} {t : finset β}
  {u : finset γ}

lemma image₂_subset_iff_left : image₂ f s t ⊆ u ↔ ∀ a ∈ s, t.image (f a) ⊆ u :=
by simp_rw [image₂_subset_iff, image_subset_iff]

lemma image₂_subset_iff_right : image₂ f s t ⊆ u ↔ ∀ b ∈ t, s.image (λ a, f a b) ⊆ u :=
by rw [image₂_swap, image₂_subset_iff_left]

end finset

namespace set
variables {α β : Type*} {f : α → α → β} {s t : set α}

lemma image2_inter_union_subset (hf : ∀ a b, f a b = f b a) :
  image2 f (s ∩ t) (s ∪ t) ⊆ image2 f s t :=
begin
  rintro _ ⟨a, b, ha, hb | hb, rfl⟩,
  { rw hf,
    exact mem_image2_of_mem hb ha.2 },
  { exact mem_image2_of_mem ha.1 hb }
end

lemma image2_union_inter_subset (hf : ∀ a b, f a b = f b a) :
  image2 f (s ∪ t) (s ∩ t) ⊆ image2 f s t :=
by { rw image2_comm hf, exact image2_inter_union_subset hf }

end set

attribute [simp] finset.singleton_inj

open_locale pointwise

namespace set
variables {α : Type*} [has_mul α] {s t u : set α}

open mul_opposite

@[to_additive] lemma mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u := image2_subset_iff_left
@[to_additive] lemma mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
image2_subset_iff_right

end set

namespace finset
variables {α : Type*} [decidable_eq α] [has_mul α] {s t u : finset α}

open mul_opposite

@[to_additive] lemma mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u := image₂_subset_iff_left
@[to_additive] lemma mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
image₂_subset_iff_right

end finset

namespace finset
variables {α : Type*} [has_one α]

@[simp, to_additive] lemma card_one : (1 : finset α).card = 1 := card_singleton _

end finset

namespace finset
variables {α β : Type*} [group α] [mul_action α β] [decidable_eq β]

@[simp, to_additive] lemma card_smul_finset (a : α) (s : finset β) : (a • s).card = s.card :=
card_image_of_injective _ $ mul_action.injective _

end finset

namespace set
variables {α : Type*} [comm_semigroup α] {s t : set α}

@[to_additive] lemma inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t :=
image2_inter_union_subset mul_comm

@[to_additive] lemma union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t :=
image2_union_inter_subset mul_comm

end set

namespace finset
variables {α : Type*} [decidable_eq α] [comm_semigroup α] {s t : finset α}

@[to_additive] lemma inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t :=
coe_subset.1 $ by { push_cast, exact set.inter_mul_union_subset }

@[to_additive] lemma union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t :=
coe_subset.1 $ by { push_cast, exact set.union_mul_inter_subset }

end finset

namespace set
variables {α β : Type*}

section has_one
variables [has_one α]

@[simp, to_additive] lemma finite_one : (1 : set α).finite := finite_singleton _

@[simp, to_additive] lemma to_finset_one : (1 : set α).to_finset = 1 := rfl

@[simp, to_additive]
lemma finite.to_finset_one (h : (1 : set α).finite := finite_one) : h.to_finset = 1 :=
finite.to_finset_singleton _

end has_one

section has_mul
variables [has_mul α] [decidable_eq α] {s t : set α}

@[simp, to_additive] lemma to_finset_mul (s t : set α) [fintype s] [fintype t] [fintype ↥(s * t)] :
  (s * t).to_finset = s.to_finset * t.to_finset :=
to_finset_image2 _ _ _

@[simp, to_additive] lemma finite.to_finset_mul (hs : s.finite) (ht : t.finite) (hf := hs.mul ht) :
  hf.to_finset = hs.to_finset * ht.to_finset :=
finite.to_finset_image2 _ _ _

end has_mul

section has_smul
variables [has_smul α β] [decidable_eq β] {a : α} {s : set α} {t : set β}

@[simp, to_additive]
lemma to_finset_smul (s : set α) (t : set β) [fintype s] [fintype t] [fintype ↥(s • t)] :
  (s • t).to_finset = s.to_finset • t.to_finset :=
to_finset_image2 _ _ _

@[simp, to_additive]
lemma finite.to_finset_smul (hs : s.finite) (ht : t.finite) (hf := hs.smul ht) :
  hf.to_finset = hs.to_finset • ht.to_finset :=
finite.to_finset_image2 _ _ _

end has_smul

section has_smul
variables [has_smul α β] [decidable_eq β] {a : α} {s : set β}

@[simp, to_additive]
lemma to_finset_smul_set (a : α) (s : set β) [fintype s] [fintype ↥(a • s)] :
  (a • s).to_finset = a • s.to_finset :=
to_finset_image _ _

@[simp, to_additive]
lemma finite.to_finset_smul_set (hs : s.finite) (hf : (a • s).finite := hs.smul_set) :
  hf.to_finset = a • hs.to_finset :=
finite.to_finset_image _ _

end has_smul
end set

namespace set
variables {α β : Type*} [has_smul α β] {s : set α} {t : set β} {a : α}

@[to_additive] lemma smul_set_subset_smul (ha : a ∈ s) : a • t ⊆ s • t :=
by { rw ←singleton_smul, exact smul_subset_smul_right (singleton_subset_iff.2 ha) }

end set

namespace finset
variables {α β : Type*} [has_smul α β] [decidable_eq β] {s : finset α} {t : finset β} {a : α}

@[to_additive] lemma smul_finset_subset_smul (ha : a ∈ s) : a • t ⊆ s • t :=
by { rw ←singleton_smul, exact smul_subset_smul_right (singleton_subset_iff.2 ha) }

end finset

namespace set
variables {α β γ : Type*}

section
variables [has_smul α β] [has_smul α γ]

@[to_additive] lemma smul_image (f : β → γ) (s : set β) (a : α) :
  (∀ b, a • f b = f (a • b)) → a • f '' s = f '' (a • s) :=
image_comm

end

variables [monoid α] [monoid β]

@[to_additive] lemma image_smul' (f : α →* β) (s : set α) (a : α) : f '' (a • s) = f a • f '' s :=
image_comm $ map_mul _ _

end set

namespace subgroup
variables {α : Type*} [group α] {H : subgroup α} [subgroup.normal H] {s t : set α}

open set

@[to_additive]
lemma image_coe_quotient (H : subgroup α) [H.normal] : (coe : α → α ⧸ H) '' H = 1 :=
begin
  ext a,
  dsimp,
  split,
  { rintro ⟨a, ha, rfl⟩,
    rwa [quotient_group.eq_one_iff] },
  { rintro rfl,
    exact ⟨1, H.one_mem, rfl⟩ }
end

@[to_additive] lemma preimage_image_coe (s : set α) : (coe : α → α ⧸ H) ⁻¹' (coe '' s) = H * s :=
begin
  ext a,
  split,
  { rintro ⟨b, hb, h⟩,
    refine ⟨a / b, b, (quotient_group.eq_one_iff _).1 _, hb, div_mul_cancel' _ _⟩,
    simp only [h, quotient_group.coe_div, div_self'] },
  { rintro ⟨a, b, ha, hb, rfl⟩,
    refine ⟨b, hb, _⟩,
    simpa only [quotient_group.coe_mul, self_eq_mul_left, quotient_group.eq_one_iff] }
end

@[to_additive]
lemma image_coe_inj : (coe : α → α ⧸ H) '' s = (coe : α → α ⧸ H) '' t ↔ ↑H * s = H * t :=
by { simp_rw ←preimage_image_coe,
  exact quotient_group.mk_surjective.preimage_injective.eq_iff.symm }

end subgroup

namespace submonoid
variables {G α β : Type*} [monoid G] [has_smul G α] {S : submonoid G}

@[simp, to_additive] lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end submonoid

namespace subgroup
variables {G α β : Type*} [group G] [mul_action G α] {S : subgroup G}

@[simp, to_additive] lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end subgroup

namespace subgroup
variables {α : Type*} [group α] {s : subgroup α} {a : α}

@[simp, to_additive] lemma coe_sort_coe (s : subgroup α) : ↥(s : set α) = ↥s := rfl

@[to_additive] lemma smul_coe (ha : a ∈ s) : a • (s : set α) = s :=
by { ext, rw set.mem_smul_set_iff_inv_smul_mem, exact subgroup.mul_mem_cancel_left _ (inv_mem ha) }

end subgroup

namespace subgroup
variables {α : Type*} [comm_group α] {s : subgroup α} {a : α}

@[to_additive]
lemma mul_alt_version (N : subgroup α) (s : set α) :
  coe ⁻¹' ((coe : α → α ⧸ N) '' s) = ⋃ x : N, x • s :=
by { simp_rw [quotient_group.preimage_image_coe N s, mul_comm _ (coe _), ← set.Union_inv_smul,
    ←set.preimage_smul _ s], congr }

end subgroup

namespace subgroup
variables {α β : Type*} [group α] [group β] [mul_action α β] [is_scalar_tower α β β]

open set

@[to_additive] lemma pairwise_disjoint_smul (s : subgroup β) :
  (set.range $ λ a : α, a • (s : set β)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab,
  dsimp at ⊢ hab,
  rw disjoint_left,
  rintro _ ⟨c, hc, rfl⟩ ⟨d, hd, hcd⟩,
  refine hab _,
  rw [←smul_coe hc, ←smul_assoc, ←hcd, smul_assoc, smul_coe hc, smul_coe hd],
end

end subgroup

namespace mul_action
variables {α β γ : Type*} [group α] [mul_action α β] [mul_action α γ] {a : α}

open function set

section set

@[simp, to_additive] lemma stabilizer_empty : stabilizer α (∅ : set β) = ⊤ :=
subgroup.coe_eq_univ.1 $ eq_univ_of_forall $ λ a, smul_set_empty

@[simp, to_additive] lemma stabilizer_singleton (b : β) :
  stabilizer α ({b} : set β) = stabilizer α b :=
by { ext, simp }

@[to_additive] lemma mem_stabilizer_set {s : set β} :
  a ∈ stabilizer α s ↔ ∀ b, a • b ∈ s ↔ b ∈ s :=
begin
  refine ⟨λ h b, _, λ h, _⟩,
  { rw [←(smul_mem_smul_set_iff : a • b ∈ a • s ↔ _), mem_stabilizer_iff.1 h] },
  simp_rw [mem_stabilizer_iff, set.ext_iff, mem_smul_set_iff_inv_smul_mem],
  exact ((mul_action.to_perm a).forall_congr' $ by simp [iff.comm]).1 h,
end

@[simp, to_additive] lemma stabilizer_subgroup (s : subgroup α) : stabilizer α (s : set α) = s :=
begin
  simp_rw [set_like.ext_iff, mem_stabilizer_set],
  refine λ a, ⟨λ h, _, λ ha b, s.mul_mem_cancel_left ha⟩,
  convert (h 1).2 s.one_mem,
  exact (mul_one _).symm,
end

@[to_additive] lemma map_stabilizer_le (f : α →* α) (s : set α) :
  (stabilizer α s).map f ≤ stabilizer α (f '' s) :=
begin
  rintro a,
  simp only [subgroup.mem_map, mem_stabilizer_iff, exists_prop, forall_exists_index, and_imp],
  rintro a ha rfl,
  rw [←image_smul', ha],
end

@[simp, to_additive] lemma stabilizer_mul (s : set α) : (stabilizer α s : set α) * s = s :=
begin
  ext,
  refine ⟨_, λ h, ⟨_, _, (stabilizer α s).one_mem, h, one_mul _⟩⟩,
  rintro ⟨a, b, ha, hb, rfl⟩,
  rw ←mem_stabilizer_iff.1 ha,
  exact smul_mem_smul_set hb,
end

@[to_additive]
lemma le_stabilizer_smul_left [has_smul β γ] [is_scalar_tower α β γ] (b : β) (c : γ) :
  stabilizer α b ≤ stabilizer α (b • c) :=
by { simp_rw [set_like.le_def, mem_stabilizer_iff, ←smul_assoc], rintro a h, rw h }

@[simp, to_additive]
lemma stabilizer_mul_eq_left [group β] [is_scalar_tower α β β] (b c : β) :
  stabilizer α (b * c) = stabilizer α b :=
begin
  rw ←smul_eq_mul,
  refine (le_stabilizer_smul_left _ _).antisymm' (λ a ha, _),
  dsimp at ha,
  rwa [←smul_mul_assoc, mul_left_inj] at ha,
end

end set

@[to_additive]
lemma le_stabilizer_smul_right {α} [group α] [mul_action α γ] [has_smul β γ] [smul_comm_class α β γ]
  (b : β) (c : γ) :
  stabilizer α c ≤ stabilizer α (b • c) :=
by { simp_rw [set_like.le_def, mem_stabilizer_iff, smul_comm], rintro a h, rw h }

@[simp, to_additive]
lemma stabilizer_smul_eq_right {α} [group α] [group β] [mul_action α γ] [mul_action β γ]
  [smul_comm_class α β γ] (b : β) (c : γ) :
  stabilizer α (b • c) = stabilizer α c :=
(le_stabilizer_smul_right _ _).antisymm' $ (le_stabilizer_smul_right b⁻¹ _).trans_eq $
  by rw inv_smul_smul

section decidable_eq
variables [decidable_eq β]

@[simp, to_additive] lemma stabilizer_coe_finset (s : finset β) :
  stabilizer α (s : set β) = stabilizer α s :=
by { ext, simp [←finset.coe_smul_finset] }

@[simp, to_additive] lemma stabilizer_finset_empty : stabilizer α (∅ : finset β) = ⊤ :=
subgroup.coe_eq_univ.1 $ eq_univ_of_forall finset.smul_finset_empty

@[simp, to_additive] lemma stabilizer_finset_singleton (b : β) :
  stabilizer α ({b} : finset β) = stabilizer α b :=
by { ext, simp }

@[to_additive] lemma mem_stabilizer_finset {s : finset β} :
  a ∈ stabilizer α s ↔ ∀ b, a • b ∈ s ↔ b ∈ s :=
by simp_rw [←stabilizer_coe_finset, mem_stabilizer_set, finset.mem_coe]

@[to_additive] lemma mem_stabilizer_finset_iff_subset_smul_finset {s : finset β} :
  a ∈ stabilizer α s ↔ s ⊆ a • s :=
by rw [mem_stabilizer_iff, finset.subset_iff_eq_of_card_le (finset.card_smul_finset _ _).le,
  eq_comm]

@[to_additive] lemma mem_stabilizer_finset_iff_smul_finset_subset {s : finset β} :
  a ∈ stabilizer α s ↔ a • s ⊆ s :=
by rw [mem_stabilizer_iff, finset.subset_iff_eq_of_card_le (finset.card_smul_finset _ _).ge]

@[to_additive] lemma mem_stabilizer_finset' {s : finset β} :
  a ∈ stabilizer α s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s :=
by { rw [←subgroup.inv_mem_iff, mem_stabilizer_finset_iff_subset_smul_finset],
  simp_rw [←finset.mem_inv_smul_finset_iff, finset.subset_iff] }

end decidable_eq

@[to_additive] lemma mem_stabilizer_set_iff_subset_smul_set {s : set β} (hs : s.finite) :
  a ∈ stabilizer α s ↔ s ⊆ a • s :=
by { lift s to finset β using hs, classical, norm_cast,
  simp [mem_stabilizer_finset_iff_subset_smul_finset] }

@[to_additive] lemma mem_stabilizer_set_iff_smul_set_subset {s : set β} (hs : s.finite) :
  a ∈ stabilizer α s ↔ a • s ⊆ s :=
by { lift s to finset β using hs, classical, norm_cast,
  simp [mem_stabilizer_finset_iff_smul_finset_subset] }

@[to_additive] lemma mem_stabilizer_set' {s : set β} (hs : s.finite) :
  a ∈ stabilizer α s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s :=
by { lift s to finset β using hs, classical, simp [mem_stabilizer_finset'] }

end mul_action

namespace mul_action
variables {α : Type*} [comm_group α] {s : set α}

open function set
open_locale pointwise

@[simp, to_additive] lemma mul_stabilizer (s : set α) : s * (stabilizer α s : set α) = s :=
by rw [mul_comm, stabilizer_mul]

@[to_additive] lemma stabilizer_image_coe_quotient (s : set α) :
  stabilizer (α ⧸ stabilizer α s) ((coe : α → α ⧸ stabilizer α s) '' s) = ⊥ :=
begin
  ext a,
  induction a using quotient_group.induction_on',
  simp only [mem_stabilizer_iff, subgroup.mem_bot, quotient_group.eq_one_iff],
  have : ↑a • (coe : α → α ⧸ stabilizer α s) '' s = coe '' (a • s) :=
    (image_smul' (quotient_group.mk' _) _ _).symm,
  rw this,
  refine ⟨λ h, _, λ h, by rw h⟩,
  rwa [subgroup.image_coe_inj, mul_smul_comm, stabilizer_mul] at h,
end

end mul_action

open mul_action

namespace finset
variables {ι α : Type*}

/-! ### Stabilizer of a finset -/

section group
variables [group α] [decidable_eq α] {s t : finset α} {a : α}

/-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`.-/
@[to_additive "The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`."]
def mul_stab (s : finset α) : finset α := (s / s).filter $ λ a, a • s = s

@[simp, to_additive]
lemma mem_mul_stab (hs : s.nonempty) : a ∈ s.mul_stab ↔ a • s = s :=
begin
  rw [mul_stab, mem_filter, mem_div, and_iff_right_of_imp],
  obtain ⟨b, hb⟩ := hs,
  exact λ h, ⟨_, _, by { rw ←h, exact smul_mem_smul_finset hb }, hb, mul_div_cancel'' _ _⟩,
end

@[to_additive] lemma mul_stab_subset_div (s : finset α) : s.mul_stab ⊆ s / s := filter_subset _ _

@[to_additive] lemma mul_stab_subset_div_right (ha : a ∈ s) : s.mul_stab ⊆ s / {a} :=
begin
  refine λ b hb, mem_div.2 ⟨_, _, _, mem_singleton_self _, mul_div_cancel'' _ _⟩,
  rw mem_mul_stab ⟨a, ha⟩ at hb,
  rw ←hb,
  exact smul_mem_smul_finset ha,
end

@[simp, to_additive] lemma coe_mul_stab (hs : s.nonempty) :
  (s.mul_stab : set α) = mul_action.stabilizer α s :=
by { ext, simp [mem_mul_stab hs] }

@[to_additive] lemma mem_mul_stab_iff_subset_smul_finset (hs : s.nonempty) :
  a ∈ s.mul_stab ↔ s ⊆ a • s :=
by rw [←mem_coe, coe_mul_stab hs, set_like.mem_coe, mem_stabilizer_finset_iff_subset_smul_finset]

@[to_additive] lemma mem_mul_stab_iff_smul_finset_subset (hs : s.nonempty) :
  a ∈ s.mul_stab ↔ a • s ⊆ s :=
by rw [←mem_coe, coe_mul_stab hs, set_like.mem_coe, mem_stabilizer_finset_iff_smul_finset_subset]

@[to_additive] lemma mem_mul_stab' (hs : s.nonempty) : a ∈ s.mul_stab ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s :=
by rw [←mem_coe, coe_mul_stab hs, set_like.mem_coe, mem_stabilizer_finset']

@[simp, to_additive] lemma mul_stab_empty : mul_stab (∅ : finset α) = ∅ := by simp [mul_stab]
@[simp, to_additive] lemma mul_stab_singleton (a : α) : mul_stab ({a} : finset α) = 1 :=
by simp [mul_stab, singleton_one]

@[to_additive] lemma nonempty.of_mul_stab : s.mul_stab.nonempty → s.nonempty :=
by { simp_rw [nonempty_iff_ne_empty, not_imp_not], rintro rfl, exact mul_stab_empty }

@[simp, to_additive] lemma one_mem_mul_stab : (1 : α) ∈ s.mul_stab ↔ s.nonempty :=
⟨λ h, nonempty.of_mul_stab ⟨_, h⟩, λ h, (mem_mul_stab h).2 $ one_smul _ _⟩

alias one_mem_mul_stab ↔ _ nonempty.one_mem_mul_stab

attribute [protected, to_additive] nonempty.one_mem_mul_stab

@[to_additive] lemma nonempty.mul_stab (h : s.nonempty) : s.mul_stab.nonempty :=
⟨_, h.one_mem_mul_stab⟩

@[simp, to_additive] lemma mul_stab_nonempty : s.mul_stab.nonempty ↔ s.nonempty :=
⟨nonempty.of_mul_stab, nonempty.mul_stab⟩

@[simp, to_additive] lemma card_mul_stab_eq_one : s.mul_stab.card = 1 ↔ s.mul_stab = 1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨a, ha⟩ := card_eq_one.1 h,
    rw ha,
    rw [eq_singleton_iff_nonempty_unique_mem, mul_stab_nonempty, ←one_mem_mul_stab] at ha,
    rw [←ha.2 _ ha.1, singleton_one] },
  { rw [h, card_one] }
end

@[to_additive] lemma nonempty.mul_stab_nontrivial (h : s.nonempty) :
  s.mul_stab.nontrivial' ↔ s.mul_stab ≠ 1 :=
nontrivial_iff_ne_singleton h.one_mem_mul_stab

@[to_additive] lemma subset_mul_stab_mul_left (ht : t.nonempty) : s.mul_stab ⊆ (s * t).mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  simp_rw [subset_iff, mem_mul_stab hs, mem_mul_stab (hs.mul ht)],
  rintro a h,
  rw [←smul_mul_assoc, h],
end

@[simp, to_additive] lemma mul_stab_mul (s : finset α) : s.mul_stab * s = s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact mul_empty _ },
  refine coe_injective _,
  simp only [hs, coe_mul, coe_mul_stab, ←stabilizer_coe_finset, stabilizer_mul],
end

@[to_additive] lemma mul_subset_right_iff (ht : t.nonempty) : s * t ⊆ t ↔ s ⊆ t.mul_stab :=
by simp_rw [←smul_eq_mul, ←bUnion_smul_finset, bUnion_subset,
  ←mem_mul_stab_iff_smul_finset_subset ht, subset_iff]

@[to_additive]
lemma smul_mul_stab (ha : a ∈ s.mul_stab) : a • s.mul_stab = s.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  rw [←mem_coe, coe_mul_stab hs, set_like.mem_coe] at ha,
  rw [←coe_inj, coe_smul_finset, coe_mul_stab hs, subgroup.smul_coe ha],
end

@[simp, to_additive]
lemma mul_stab_mul_mul_stab (s : finset α) : s.mul_stab * s.mul_stab = s.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  { simp_rw [←smul_eq_mul, ← bUnion_smul_finset, bUnion_congr rfl (λ a, smul_mul_stab),
    ←sup_eq_bUnion, sup_const hs.mul_stab] }
end

@[to_additive]
lemma inter_mul_stab_subset_mul_stab_union : s.mul_stab ∩ t.mul_stab ⊆ (s ∪ t).mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  intros x hx,
  rw [mem_mul_stab (finset.nonempty.mono (subset_union_left s t) hs), smul_finset_union,
    (mem_mul_stab hs).mp (mem_of_mem_inter_left hx),
    (mem_mul_stab ht).mp (mem_of_mem_inter_right hx)],
end

end group

variables [comm_group α] [decidable_eq α] {s t : finset α} {a : α}

@[to_additive] lemma mul_stab_subset_div_left (ha : a ∈ s) : s.mul_stab ⊆ {a} / s :=
begin
  refine λ b hb, mem_div.2 ⟨_, _, mem_singleton_self _, _, div_div_cancel _ _⟩,
  rw mem_mul_stab ⟨a, ha⟩ at hb,
  rwa [←hb, ←inv_smul_mem_iff, smul_eq_mul, inv_mul_eq_div] at ha,
end

@[to_additive] lemma subset_mul_stab_mul_right (hs : s.nonempty) : t.mul_stab ⊆ (s * t).mul_stab :=
by { rw mul_comm, exact subset_mul_stab_mul_left hs }

@[simp, to_additive] lemma mul_mul_stab (s : finset α) : s * s.mul_stab = s :=
by { rw mul_comm, exact mul_stab_mul _ }

@[to_additive] lemma smul_finset_mul_stab_subset (ha : a ∈ s) : a • s.mul_stab ⊆ s :=
(smul_finset_subset_smul ha).trans s.mul_mul_stab.subset'

@[to_additive] lemma mul_subset_left_iff (hs : s.nonempty) : s * t ⊆ s ↔ t ⊆ s.mul_stab :=
by rw [mul_comm, mul_subset_right_iff hs]

@[simp, to_additive] lemma mul_stab_idem (s : finset α) : s.mul_stab.mul_stab = s.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  refine coe_injective _,
  rw [coe_mul_stab hs, coe_mul_stab hs.mul_stab, ←stabilizer_coe_finset, coe_mul_stab hs],
  simp,
end

@[simp, to_additive] lemma mul_stab_smul (a : α) (s : finset α) : (a • s).mul_stab = s.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  refine coe_injective _,
  rw [coe_mul_stab hs, coe_mul_stab hs.smul_finset, stabilizer_smul_eq_right],
end

section classical
open_locale classical

@[to_additive] lemma mul_stab_image_coe_quotient (hs : s.nonempty) :
  (s.image coe : finset (α ⧸ stabilizer α s)).mul_stab = 1 :=
begin
  refine coe_injective _,
  rw [coe_mul_stab (hs.image _), ←stabilizer_coe_finset, ←stabilizer_coe_finset, coe_image, coe_one,
    stabilizer_image_coe_quotient, subgroup.coe_bot, set.singleton_one],
end

@[to_additive to_name_add]
lemma to_name (s t : finset α) (ht : t.nonempty):
  quotient_group.mk ⁻¹' (coe '' (s : set α) : set (α ⧸ stabilizer α t)) = s * t.mul_stab :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  convert (stabilizer α t).mul_alt_version s,
  refine eq.trans _ (set.Union_subtype _ _).symm,
  simp_rw [subgroup.mk_smul,← set_like.mem_coe, ← coe_mul_stab ht, ← coe_smul_finset,
    ← coe_bUnion, bUnion_smul_finset, smul_eq_mul, coe_mul, mul_comm]
end

@[to_additive to_name_add_also]
lemma to_name_also (s t : finset α) :
  quotient_group.mk ⁻¹' (coe '' ((s : set α) * ↑t) : set (α ⧸ stabilizer α (s * t))) = ↑s * ↑t :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  convert to_name (s * t) (s * t) (hs.mul ht) using 1,
  { simp },
  { norm_cast,
    rw mul_mul_stab (s * t) }
end

@[to_additive] lemma pairwise_disjoint_smul_finset_mul_stab (s : finset α) :
  (set.range $ λ a : α, a • s.mul_stab).pairwise_disjoint id :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩,
  dsimp,
  simp_rw [←disjoint_coe, ←coe_injective.eq_iff, coe_smul_finset, coe_mul_stab hs],
  exact subgroup.pairwise_disjoint_smul _ (set.mem_range_self _) (set.mem_range_self _),
end

@[to_additive] lemma disjoint_smul_finset_mul_stab_mul_mul_stab :
  ¬ a • s.mul_stab ⊆ t * s.mul_stab → disjoint (a • s.mul_stab) (t * s.mul_stab) :=
begin
  simp_rw [@not_imp_comm (_ ⊆ _), ←smul_eq_mul, ←bUnion_smul_finset, disjoint_bUnion_right,
    not_forall],
  rintro ⟨b, hb, h⟩,
  rw s.pairwise_disjoint_smul_finset_mul_stab.eq (set.mem_range_self _) (set.mem_range_self _) h,
  exact subset_bUnion_of_mem _ hb,
end

end classical
end finset

namespace finset
variables {α : Type*} [comm_group α] [decidable_eq α]

open function
open_locale classical

/-- A version of Lagrange's theorem. -/
@[to_additive "A version of Lagrange's theorem."]
lemma card_mul_card_image_coe' (s t : finset α) :
  t.mul_stab.card * (s.image coe : finset (α ⧸ stabilizer α t)).card = (s * t.mul_stab).card :=
begin
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  have := quotient_group.preimage_mk_equiv_subgroup_times_set (stabilizer α t)
    (coe '' (s : set α) : set (α ⧸ stabilizer α t)),
  have that : ↥(stabilizer α t) = ↥t.mul_stab,
  { rw [←subgroup.coe_sort_coe, ←coe_mul_stab ht, finset.coe_sort_coe] },
  have temp := this.trans (equiv.prod_congr (equiv.cast that) (equiv.refl _ )),
  rw to_name s t ht at temp,
  replace temp := fintype.card_congr temp,
  simp only [←coe_mul, fintype.card_prod, fintype.card_coe, fintype.card_of_finset, to_finset_coe]
    at temp,
  rw ←temp,
  simp only [fintype.card_of_finset, mem_coe, iff_self, forall_const]
end

@[to_additive]
lemma card_mul_card_eq_mul_stab_card_mul_coe (s t : finset α) :
  (s * t).card = (s * t).mul_stab.card *
  ((s * t).image coe : finset (α ⧸ stabilizer α (s * t))).card :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  have := quotient_group.preimage_mk_equiv_subgroup_times_set (stabilizer α (s * t))
    (coe '' ((s : set α) * ↑t) : set (α ⧸ stabilizer α (s * t))),
  have that : ↥(stabilizer α (s * t)) = ↥(s * t).mul_stab,
  { rw [←subgroup.coe_sort_coe, ←coe_mul_stab (hs.mul ht), finset.coe_sort_coe] },
  have temp := this.trans (equiv.prod_congr (equiv.cast that) (equiv.refl _ )),
  rw to_name_also s t at temp,
  replace temp := fintype.card_congr temp,
  have h1 : fintype.card ↥(((s * t) : finset α) : set α) = fintype.card ↥(s * t) := by congr,
  simp_rw [← coe_mul s t, h1, fintype.card_coe, coe_mul, fintype.card_prod,
    fintype.card_of_finset, fintype.card_coe, ← coe_mul s t, to_finset_coe] at temp,
  exact temp
end

/-- A version of Lagrange's theorem. -/
@[to_additive "A version of Lagrange's theorem."]
lemma card_mul_card_image_coe (s t : finset α) :
  (s * t).mul_stab.card *
  (s.image coe * t.image coe : finset (α ⧸ stabilizer α (s * t))).card = (s * t).card :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  have := quotient_group.preimage_mk_equiv_subgroup_times_set (stabilizer α (s * t))
    (((s : set α).image coe : set (α ⧸ stabilizer α (s * t))) *
    ((t : set α).image coe : set (α ⧸ stabilizer α (s * t)))),
  have image_coe_mul :
    (((s : set α) * t).image coe : set (α ⧸ stabilizer α (s * t))) =
      (s : set α).image coe * (t : set α).image coe,
  { exact set.image_mul (quotient_group.mk' _ : α →* α ⧸ stabilizer α (s * t)) },
  rw [←image_coe_mul, to_name_also, image_coe_mul] at this,
  have that : (stabilizer α (s * t) × ↥(((s : set α).image coe : set (α ⧸ stabilizer α (s * t))) *
    ((t : set α).image coe : set (α ⧸ stabilizer α (s * t))))) =
    ((s * t).mul_stab × ↥(((s : set α).image coe : set (α ⧸ stabilizer α (s * t))) *
    ((t : set α).image coe : set (α ⧸ stabilizer α (s * t))))),
  { rw [←subgroup.coe_sort_coe, ←coe_mul_stab (hs.mul ht), finset.coe_sort_coe] },
  have temp := this.trans (equiv.cast that),
  replace temp := fintype.card_congr temp,
  simp_rw ← finset.coe_mul s t at temp,
  simp only [fintype.card_prod, fintype.card_coe] at temp,
  have h1 : fintype.card ↥(((s * t) : finset α) : set α) = fintype.card ↥(s * t) := by congr,
  have h2 : ((s : set α).image coe : set (α ⧸ stabilizer α (s * t))) * coe '' ↑t =
    ((s.image coe : finset (α ⧸ stabilizer α (s * t))) *
    t.image coe : finset (α ⧸ stabilizer α (s * t))) := by simp,
  have h3 : fintype.card ↥(((s : set α).image coe : set (α ⧸ stabilizer α (s * t)))  *
    coe '' (t : set α)) = fintype.card ↥((s.image coe : finset (α ⧸ stabilizer α (s * t))) *
    image coe t),
  { simp_rw h2,
    congr },
  simp only [h1, h3, fintype.card_coe] at temp,
  rw temp
end

end finset
