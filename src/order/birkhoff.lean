/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.irreducible
import order.locally_finite
import order.upper_lower.basic

/-!
# Birkhoff's representation theorem
-/

namespace set
variables {α : Type*} [preorder α]

section locally_finite_order
variables [locally_finite_order α]

@[simp] lemma to_finset_Icc (a b : α) [fintype (Icc a b)] : (Icc a b).to_finset = finset.Icc a b :=
by ext; simp

@[simp] lemma to_finset_Ico (a b : α) [fintype (Ico a b)] : (Ico a b).to_finset = finset.Ico a b :=
by ext; simp

@[simp] lemma to_finset_Ioc (a b : α) [fintype (Ioc a b)] : (Ioc a b).to_finset = finset.Ioc a b :=
by ext; simp

@[simp] lemma to_finset_Ioo (a b : α) [fintype (Ioo a b)] : (Ioo a b).to_finset = finset.Ioo a b :=
by ext; simp

end locally_finite_order

section locally_finite_order_top
variables [locally_finite_order_top α]

@[simp] lemma to_finset_Ici (a : α) [fintype (Ici a)] : (Ici a).to_finset = finset.Ici a :=
by ext; simp

@[simp] lemma to_finset_Ioi (a : α) [fintype (Ioi a)] : (Ioi a).to_finset = finset.Ioi a :=
by ext; simp

end locally_finite_order_top

section locally_finite_order_bot
variables [locally_finite_order_bot α]

@[simp] lemma to_finset_Iic (a : α) [fintype (Iic a)] : (Iic a).to_finset = finset.Iic a :=
by ext; simp

@[simp] lemma to_finset_Iio (a : α) [fintype (Iio a)] : (Iio a).to_finset = finset.Iio a :=
by ext; simp

end locally_finite_order_bot
end set

namespace finset
variables {α : Type*} [semilattice_sup α] [order_bot α] [locally_finite_order_bot α]

@[simp] lemma sup_Iic (a : α) : (Iic a).sup id = a :=
le_antisymm (finset.sup_le $ λ _, mem_Iic.1) $ le_sup $ mem_Iic.2 $ le_refl a

end finset

open finset order_dual

variables {α : Type*}

namespace upper_set
variables [semilattice_inf α] {s : upper_set α} {a : α}

local attribute [-instance] set_like.partial_order

@[simp] lemma inf_irred_Ici (a : α) : inf_irred (Ici a) :=
begin
  refine ⟨λ h, Ici_ne_top _ h.eq_top, λ s t hst, _⟩,
  have := mem_Ici_iff.2 (le_refl a),
  rw ←hst at this,
  exact this.imp (λ ha, le_antisymm (le_Ici.2 ha) $ hst.ge.trans inf_le_left)
    (λ ha, le_antisymm (le_Ici.2 ha) $ hst.ge.trans inf_le_right),
end

variables [finite α] [order_top α]

-- TODO: Do we really need `order_top α` here?
@[simp] protected lemma inf_irred : inf_irred s ↔ ∃ a, Ici a = s :=
begin
  classical,
  casesI nonempty_fintype α,
  refine ⟨λ h, ⟨(s : set α).to_finset.inf id, _⟩, _⟩,
  { refine le_antisymm (λ a ha, inf_le $ set.mem_to_finset.2 $ set_like.mem_coe.2 ha) (le_Ici.2 _),
    sorry, },
  { rintro ⟨a, rfl⟩,
    exact inf_irred_Ici _ }
end

end upper_set

namespace lower_set
variables [semilattice_sup α] {s : lower_set α} {a : α}

@[simp] lemma sup_irred_Iic (a : α) : sup_irred (Iic a) :=
begin
  refine ⟨λ h, Iic_ne_bot _ h.eq_bot, λ s t hst, _⟩,
  have := mem_Iic_iff.2 (le_refl a),
  rw ←hst at this,
  exact this.imp (λ ha, (le_sup_left.trans_eq hst).antisymm $ Iic_le.2 ha)
    (λ ha, (le_sup_right.trans_eq hst).antisymm $ Iic_le.2 ha),
end

variables [finite α] [order_bot α]

-- TODO: Do we really need `order_bot α` here?
@[simp] protected lemma sup_irred : sup_irred s ↔ ∃ a, Iic a = s :=
begin
  classical,
  casesI nonempty_fintype α,
  refine ⟨λ h, ⟨(s : set α).to_finset.sup id, _⟩, _⟩,
  { refine le_antisymm (Iic_le.2 _) (λ a ha, le_sup $ set.mem_to_finset.2 $ set_like.mem_coe.2 ha),
    sorry, },
  { rintro ⟨a, rfl⟩,
    exact sup_irred_Iic _ }
end

end lower_set

section distrib_lattice
variables [distrib_lattice α] [fintype α] {a b c : α}

open_locale classical

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
      obtain ⟨s, rfl, hs⟩ := exists_sup_irred_decomposition a,
      refine finset.sup_le (λ i hi, le_sup_of_le (set.mem_to_finset.2 _) _),
      { exact ⟨i, hs hi⟩ },
      { dsimp,
        exact le_sup hi },
      { refl }
    end }
  (λ s t hst, finset.sup_mono $ set.to_finset_mono hst)
  (λ b c hbc d, le_trans' hbc)

/-- Any finite distributive lattice is isomorphic to its lattice of sup-irreducible lower sets. -/
noncomputable def sup_irred_lower_set_iso : {s : lower_set α // sup_irred s} ≃o α :=
equiv.to_order_iso
  { to_fun := λ s, ((s : lower_set α) : set α).to_finset.sup id,
    inv_fun := λ a, ⟨lower_set.Iic a, lower_set.sup_irred_Iic _⟩,
    left_inv := begin
      classical,
      haveI : locally_finite_order α := fintype.to_locally_finite_order,
      rintro ⟨s, hs⟩,
      obtain ⟨a, rfl⟩ := lower_set.sup_irred.1 hs,
      simp,
    end,
    right_inv := λ a, begin
      classical,
      haveI : locally_finite_order α := fintype.to_locally_finite_order,
      simp,
    end }
  (λ s t hst, finset.sup_mono $ set.to_finset_mono hst)
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
    obtain ⟨s, rfl, hs⟩ := exists_inf_irred_decomposition a,
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
