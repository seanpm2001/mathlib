/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.monoid.basic

/-!
# Ordered monoids with zero
-/

universes u
variables {α : Type u}

namespace with_zero

local attribute [semireducible] with_zero

instance [preorder α] : preorder (with_zero α) := with_bot.preorder

instance [partial_order α] : partial_order (with_zero α) := with_bot.partial_order

instance [preorder α] : order_bot (with_zero α) := with_bot.order_bot

lemma zero_le [preorder α] (a : with_zero α) : 0 ≤ a := bot_le

lemma zero_lt_coe [preorder α] (a : α) : (0 : with_zero α) < a := with_bot.bot_lt_coe a

lemma zero_eq_bot [preorder α] : (0 : with_zero α) = ⊥ := rfl

@[simp, norm_cast] lemma coe_lt_coe [preorder α] {a b : α} : (a : with_zero α) < b ↔ a < b :=
with_bot.coe_lt_coe

@[simp, norm_cast] lemma coe_le_coe [preorder α] {a b : α} : (a : with_zero α) ≤ b ↔ a ≤ b :=
with_bot.coe_le_coe

instance [lattice α] : lattice (with_zero α) := with_bot.lattice

instance [linear_order α] : linear_order (with_zero α) := with_bot.linear_order

instance covariant_class_mul_le {α : Type u} [has_mul α] [preorder α]
  [covariant_class α α (*) (≤)] :
  covariant_class (with_zero α) (with_zero α) (*) (≤) :=
begin
  refine ⟨λ a b c hbc, _⟩,
  induction a using with_zero.rec_zero_coe, { exact zero_le _ },
  induction b using with_zero.rec_zero_coe, { exact zero_le _ },
  rcases with_bot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩,
  rw [← coe_mul, ← coe_mul, coe_le_coe],
  exact mul_le_mul_left' hbc' a
end

instance contravariant_class_mul_lt {α : Type u} [has_mul α] [partial_order α]
  [contravariant_class α α (*) (<)] :
  contravariant_class (with_zero α) (with_zero α) (*) (<) :=
begin
  refine ⟨λ a b c h, _⟩,
  have := ((zero_le _).trans_lt h).ne',
  lift a to α using left_ne_zero_of_mul this,
  lift c to α using right_ne_zero_of_mul this,
  induction b using with_zero.rec_zero_coe,
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' $ coe_lt_coe.mp h)]
end

@[simp] lemma le_max_iff [linear_order α] {a b c : α} :
  (a : with_zero α) ≤ max b c ↔ a ≤ max b c :=
by simp only [with_zero.coe_le_coe, le_max_iff]

@[simp] lemma min_le_iff [linear_order α] {a b c : α} :
   min (a : with_zero α) b ≤ c ↔ min a b ≤ c :=
by simp only [with_zero.coe_le_coe, min_le_iff]

instance [ordered_comm_monoid α] : ordered_comm_monoid (with_zero α) :=
{ mul_le_mul_left := λ _ _, mul_le_mul_left',
  ..with_zero.comm_monoid_with_zero,
  ..with_zero.partial_order }

protected lemma covariant_class_add_le [add_zero_class α] [preorder α]
  [covariant_class α α (+) (≤)] (h : ∀ a : α, 0 ≤ a) :
  covariant_class (with_zero α) (with_zero α) (+) (≤) :=
begin
  refine ⟨λ a b c hbc, _⟩,
  induction a using with_zero.rec_zero_coe,
  { rwa [zero_add, zero_add] },
  induction b using with_zero.rec_zero_coe,
  { rw [add_zero],
    induction c using with_zero.rec_zero_coe,
    { rw [add_zero], exact le_rfl },
    { rw [← coe_add, coe_le_coe],
      exact le_add_of_nonneg_right (h _) } },
  { rcases with_bot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩,
    rw [← coe_add, ← coe_add, coe_le_coe],
    exact add_le_add_left hbc' a }
end

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/

/--
If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
See note [reducible non-instances].
-/
@[reducible] protected def ordered_add_comm_monoid [ordered_add_comm_monoid α]
  (zero_le : ∀ a : α, 0 ≤ a) : ordered_add_comm_monoid (with_zero α) :=
{ add_le_add_left := @add_le_add_left _ _ _ (with_zero.covariant_class_add_le zero_le),
  ..with_zero.partial_order,
  ..with_zero.add_comm_monoid, .. }

end with_zero
