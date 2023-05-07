/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice
import data.fintype.card
import order.upper_lower.basic

/-!
# Birkhoff's representation theorem
-/

open finset order_dual

variables {ι α : Type*}

/-! ### Irreducible and prime elements -/

section semilattice_sup
variables [semilattice_sup α] {a : α}

/-- A sup-irreducible element is a non-bottom element which isn't the supremum of anything smaller.
-/
def sup_irred (a : α) : Prop := ¬ is_min a ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

/-- A sup-prime element is a non-bottom element which isn't less than the supremum of anything
smaller. -/
def sup_prime (a : α) : Prop := ¬ is_min a ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c

lemma sup_irred.not_is_min (ha : sup_irred a) : ¬ is_min a := ha.1
lemma sup_prime.not_is_min (ha : sup_prime a) : ¬ is_min a := ha.1
lemma is_min.not_sup_irred (ha : is_min a) : ¬ sup_irred a := λ h, h.1 ha
lemma is_min.not_sup_prime (ha : is_min a) : ¬ sup_prime a := λ h, h.1 ha

@[simp] protected lemma sup_prime.sup_irred : sup_prime a → sup_irred a :=
and.imp_right $ λ h b c ha, by simpa [←ha] using h ha.ge

variables [order_bot α] {s : finset ι} {f : ι → α}

@[simp] lemma not_sup_irred_bot : ¬ sup_irred (⊥ : α) := is_min_bot.not_sup_irred
@[simp] lemma not_sup_prime_bot : ¬ sup_prime (⊥ : α) := is_min_bot.not_sup_prime

lemma sup_irred.ne_bot (ha : sup_irred a) : a ≠ ⊥ := by { rintro rfl, exact not_sup_irred_bot ha }
lemma sup_prime.ne_bot (ha : sup_prime a) : a ≠ ⊥ := by { rintro rfl, exact not_sup_prime_bot ha }

lemma sup_irred.finset_sup (ha : sup_irred a) (h : s.sup f = a) : ∃ i ∈ s, f i = a :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { simpa [ha.ne_bot] using h.symm },
  simp only [exists_prop, exists_mem_insert] at ⊢ ih,
  rw sup_insert at h,
  exact (ha.2 h).imp_right ih,
end

lemma sup_prime.finset_sup (ha : sup_prime a) (h : a ≤ s.sup f) : ∃ i ∈ s, a ≤ f i :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { simpa [ha.ne_bot] using h },
  simp only [exists_prop, exists_mem_insert] at ⊢ ih,
  rw sup_insert at h,
  exact (ha.2 h).imp_right ih,
end

variables [finite α]

lemma exists_finset_sup_sup_irred_eq (a : α) :
  ∃ s : finset α, s.sup id = a ∧ ∀ ⦃b⦄, b ∈ s → sup_irred b :=
begin
  obtain rfl | ha := eq_or_ne a ⊥,
  { exact ⟨∅, by simp⟩ },
  { sorry }
end

end semilattice_sup

section semilattice_inf
variables [semilattice_inf α] {a : α}

/-- An inf-irreducible element is a non-top element which isn't the infimum of anything bigger. -/
def inf_irred (a : α) : Prop := ¬ is_max a ∧ ∀ ⦃b c⦄, b ⊓ c = a → b = a ∨ c = a

/-- An inf-prime element is a non-top element which isn't bigger than the infimum of anything
bigger. -/
def inf_prime (a : α) : Prop := ¬ is_max a ∧ ∀ ⦃b c⦄, b ⊓ c ≤ a → b ≤ a ∨ c ≤ a

@[simp] lemma is_max.not_inf_irred (ha : is_max a) : ¬ inf_irred a := λ h, h.1 ha
@[simp] lemma is_max.not_inf_prime (ha : is_max a) : ¬ inf_prime a := λ h, h.1 ha

@[simp] protected lemma inf_prime.inf_irred : inf_prime a → inf_irred a :=
and.imp_right $ λ h b c ha, by simpa [←ha] using h ha.le

variables [order_top α] {s : finset ι} {f : ι → α}

@[simp] lemma not_inf_irred_top : ¬ inf_irred (⊤ : α) := is_max_top.not_inf_irred
@[simp] lemma not_inf_prime_top : ¬ inf_prime (⊤ : α) := is_max_top.not_inf_prime

lemma inf_irred.ne_top (ha : inf_irred a) : a ≠ ⊤ := by { rintro rfl, exact not_inf_irred_top ha }
lemma inf_prime.ne_top (ha : inf_prime a) : a ≠ ⊤ := by { rintro rfl, exact not_inf_prime_top ha }

lemma inf_irred.finset_inf : inf_irred a → s.inf f = a → ∃ i ∈ s, f i = a :=
@sup_irred.finset_sup _ αᵒᵈ _ _ _ _ _

lemma inf_prime.finset_inf : inf_prime a → s.inf f ≤ a → ∃ i ∈ s, f i ≤ a :=
@sup_prime.finset_sup _ αᵒᵈ _ _ _ _ _

variables [finite α]

lemma exists_finset_inf_inf_irred_eq (a : α) :
  ∃ s : finset α, s.inf id = a ∧ ∀ ⦃b⦄, b ∈ s → inf_irred b :=
@exists_finset_sup_sup_irred_eq αᵒᵈ _ _ _ _

end semilattice_inf

section distrib_lattice
variables [distrib_lattice α] {a b c : α}

@[simp] lemma sup_prime_iff_sup_irred : sup_prime a ↔ sup_irred a :=
⟨sup_prime.sup_irred, and.imp_right $ λ h b c,
  by { simp_rw [←inf_eq_left, inf_sup_left], exact @h _ _ }⟩

@[simp] lemma inf_prime_iff_inf_irred : inf_prime a ↔ inf_irred a :=
⟨inf_prime.inf_irred, and.imp_right $ λ h b c,
  by { simp_rw [←sup_eq_left, sup_inf_left], exact @h _ _ }⟩

alias sup_prime_iff_sup_irred ↔ _ sup_irred.sup_prime
alias inf_prime_iff_inf_irred ↔ _ inf_irred.inf_prime

attribute [protected] sup_irred.sup_prime inf_irred.inf_prime

open_locale classical

variables [fintype α]

section order_bot
variables [order_bot α]

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice is isomorphic to the
lattice of lower sets of its sup-irreducible elements. -/
noncomputable def lower_set_sup_irred_iso : lower_set {a : α // sup_irred a} ≃o α :=
equiv.to_order_iso
 { to_fun := λ s, (s : set {a : α // sup_irred a}).to_finset.sup coe,
  inv_fun := λ a, ⟨{b | ↑b ≤ a}, λ b c, le_trans⟩,
  left_inv := λ s, begin
    dsimp,
    refine le_antisymm (λ a ha, _) (λ a ha, _),
    { obtain ⟨i, hi, ha⟩ := a.2.sup_prime.finset_sup ha,
      exact s.lower ha (set.mem_to_finset.1 hi) },
    { dsimp,
      exact le_sup (set.mem_to_finset.2 ha) }
  end,
  right_inv := λ a, begin
    refine le_antisymm (finset.sup_le $ λ b, set.mem_to_finset.1) _,
    obtain ⟨s, rfl, hs⟩ := exists_finset_sup_sup_irred_eq a,
    refine finset.sup_le (λ i hi, le_sup_of_le (set.mem_to_finset.2 _) _),
    { exact ⟨i, hs hi⟩ },
    { dsimp,
      exact le_sup hi },
    { refl }
  end }
  (λ s t hst, finset.sup_mono $ set.to_finset_mono hst)
  (λ b c hbc d, le_trans' hbc)

/-- Any finite distributive lattice is isomorphic to its lattice of sup-irreducible lower sets. -/
def sup_irred_lower_set_iso : {s : lower_set α // sup_irred s} ≃o α :=
equiv.to_order_iso
 { to_fun := λ s, sorry,
  inv_fun := λ a, ⟨lower_set.Iic a, sorry⟩,
  left_inv := sorry,
  right_inv := sorry }
  sorry
  (λ b c hbc d, le_trans' hbc)

end order_bot

section order_top
variables [order_top α]

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice is dual-isomorphic to the
lattice of upper sets of its inf-irreducible elements. -/
noncomputable def upper_set_inf_irred_iso : upper_set {a : α // inf_irred a} ≃o αᵒᵈ :=
equiv.to_order_iso
 { to_fun := λ s, to_dual $ (s : set {a : α // inf_irred a}).to_finset.inf coe,
  inv_fun := λ a, ⟨{b | of_dual a ≤ b}, λ b c, le_trans'⟩,
  left_inv := λ s, begin
    dsimp,
    refine le_antisymm (λ a ha, _) (λ a ha, _),
    { obtain ⟨i, hi, ha⟩ := a.2.inf_prime.finset_inf ha,
      exact s.upper ha (set.mem_to_finset.1 hi) },
    { dsimp,
      exact inf_le (set.mem_to_finset.2 ha) }
  end,
  right_inv := order_dual.forall.2 $ λ a, of_dual.injective begin
    refine le_antisymm _ (finset.le_inf $ λ b, set.mem_to_finset.1),
    obtain ⟨s, rfl, hs⟩ := exists_finset_inf_inf_irred_eq a,
    refine finset.le_inf (λ i hi, inf_le_of_le (set.mem_to_finset.2 _) _),
    { exact ⟨i, hs hi⟩ },
    { dsimp,
      exact inf_le hi },
    { refl }
  end }
  (λ s t hst, finset.inf_mono $ set.to_finset_mono hst)
  (λ b c hbc d, le_trans' hbc)

end order_top
end distrib_lattice

section linear_order
variables [linear_order α] {a : α}

@[simp] protected lemma sup_prime_iff_not_is_min : sup_prime a ↔ ¬ is_min a :=
and_iff_left $ by simp

@[simp] protected lemma sup_irred_iff_not_is_min : sup_irred a ↔ ¬ is_min a :=
and_iff_left $ λ _ _, by simpa only [sup_eq_max, max_eq_iff] using or.imp and.left and.left

@[simp] protected lemma inf_prime_iff_not_is_max : inf_prime a ↔ ¬ is_max a :=
and_iff_left $ by simp

@[simp] protected lemma inf_irred_iff_not_is_max : inf_irred a ↔ ¬ is_max a :=
and_iff_left $ λ _ _, by simpa only [inf_eq_min, min_eq_iff] using or.imp and.left and.left

end linear_order
