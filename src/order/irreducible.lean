/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.basic
import order.upper_lower.basic

/-!
# Birkhoff's representation theorem
-/

open order

variables {α : Type*}

/-! ### Irreducible and prime elements -/

section semilattice_sup
variables [semilattice_sup α] [order_bot α] {a : α}

/-- A sup-irreducible element is a non-bottom element which isn't the supremum of anything smaller.
-/
def sup_irreducible (a : α) : Prop := a ≠ ⊥ ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

/-- A sup-prime element is a non-bottom element which isn't less than the supremum of anything
smaller. -/
def sup_prime (a : α) : Prop := a ≠ ⊥ ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c

@[simp] lemma not_sup_irreducible_bot : ¬ sup_irreducible (⊥ : α) := λ h, h.1 rfl
@[simp] lemma not_sup_prime_bot : ¬ sup_prime (⊥ : α) := λ h, h.1 rfl

@[simp] protected lemma sup_prime.sup_irreducible : sup_prime a → sup_irreducible a :=
and.imp_right $ λ h b c ha, by simpa [←ha] using h ha.ge

end semilattice_sup

section semilattice_inf
variables [semilattice_inf α] [order_top α] {a : α}

/-- A inf-irreducible element is a non-top element which isn't the infiemum of anything bigger. -/
def inf_irreducible (a : α) : Prop := a ≠ ⊤ ∧ ∀ ⦃b c⦄, b ⊓ c = a → b = a ∨ c = a

/-- A inf-prime element is a non-toptom element which isn't less than the infremum of anything
smaller. -/
def inf_prime (a : α) : Prop := a ≠ ⊤ ∧ ∀ ⦃b c⦄, b ⊓ c ≤ a → b ≤ a ∨ c ≤ a

@[simp] lemma not_inf_irreducible_top : ¬ inf_irreducible (⊤ : α) := λ h, h.1 rfl
@[simp] lemma not_inf_prime_top : ¬ inf_prime (⊤ : α) := λ h, h.1 rfl

@[simp] protected lemma inf_prime.inf_irreducible : inf_prime a → inf_irreducible a :=
and.imp_right $ λ h b c ha, by simpa [←ha] using h ha.le

end semilattice_inf

section distrib_lattice
variables [distrib_lattice α] [order_bot α] {a b c : α}

/-- **Birkhoff's Representation Theorem**. -/
def birkhoff [fintype α] : lower_set {a : α // sup_irreducible a} ≃o α := sorry

end distrib_lattice
