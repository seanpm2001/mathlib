/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import data.list.quot
import data.multiset.basic

/-!
# Quotients indexed by a `multiset`

In this file, we define lifting and recursion principle for quotients indexed by a `multiset`.
-/

namespace multiset
variables {ι : Type*} [decidable_eq ι] {α : ι → Sort*} [S : Π i, setoid (α i)] {β : Sort*}
include S

/-- Given a collection of setoids indexed by a type `ι`, a multiset `m` of indices, and a function
  that for each `i ∈ m` gives a term of the corresponding quotient type, then there is a
  corresponding term in the quotient of the product of the setoids indexed by `m`. -/
def quotient_choice {m : multiset ι} :
  (Π i ∈ m, quotient (S i)) → @quotient (Π i ∈ m, α i) pi_setoid :=
quotient.hrec_on m (λ l, list.quotient_choice)
  (λ l₁ l₂ hl, list.quotient_choice_heq (λ i, list.perm.mem_iff hl))

theorem quotient_choice_mk {m : multiset ι} (a : Π i ∈ m, α i) :
  quotient_choice (λ i h, ⟦a i h⟧) = ⟦a⟧ :=
by { induction m using quotient.ind, exact list.quotient_choice_mk a }

/-- Lift a function on `Π i ∈ m, α i` to `Π i ∈ m, quotient (S i)`. -/
def quotient_lift_on {m : multiset ι} : Π (q : Π i ∈ m, quotient (S i)) (f : (Π i ∈ m, α i) → β)
  (h : ∀ (a b : Π i ∈ m, α i), (∀ i (hi : i ∈ m), a i hi ≈ b i hi) → f a = f b), β :=
quotient.hrec_on m (λ l, list.quotient_lift_on)
  (λ l₁ l₂ hl, list.quotient_lift_on_heq (λ i, list.perm.mem_iff hl))

/-- Lift a function on `Π i ∈ m, α i` to `Π i ∈ m, quotient (S i)`. -/
def quotient_lift {m : multiset ι} (f : (Π i ∈ m, α i) → β)
  (h : ∀ (a b : Π i ∈ m, α i), (∀ i (hi : i ∈ m), a i hi ≈ b i hi) → f a = f b)
  (q : Π i ∈ m, quotient (S i)) : β :=
quotient_lift_on q f h

@[simp] lemma quotient_lift_on_empty (q : Π i ∈ (∅ : multiset ι), quotient (S i)) :
  @quotient_lift_on _ _ _ _ β _ q = λ f h, f (λ i hi, hi.elim) :=
rfl

@[simp] lemma quotient_lift_on_mk {m : multiset ι} (a : Π i ∈ m, α i) :
  @quotient_lift_on _ _ _ _ β _ (λ i hi, ⟦a i hi⟧) = λ f h, f a :=
by { induction m using quotient.ind, exact list.quotient_lift_on_mk a }

@[simp] lemma quotient_lift_empty (f : (Π i ∈ (∅ : multiset ι), α i) → β) (h) :
  quotient_lift f h = (λ q, f (λ i hi, hi.elim)) :=
rfl

@[simp] lemma quotient_lift_mk {m : multiset ι} (f : (Π i ∈ m, α i) → β)
  (h : ∀ (a b : Π i ∈ m, α i), (∀ i (hi : i ∈ m), a i hi ≈ b i hi) → f a = f b)
  (a : Π i ∈ m, α i) : quotient_lift f h (λ i hi, ⟦a i hi⟧) = f a :=
congr_fun (congr_fun (quotient_lift_on_mk a) f) h

/-- Choice-free induction principle for quotients indexed by a `multiset`. -/
@[nolint decidable_classical, elab_as_eliminator]
lemma quotient_ind {m : multiset ι} {C : (Π i ∈ m, quotient (S i)) → Prop}
  (f : ∀ a : Π i ∈ m, α i, C (λ i hi, ⟦a i hi⟧)) (q : Π i ∈ m, quotient (S i)) : C q :=
by { induction m using quotient.ind, exact list.quotient_ind f q }

/-- Choice-free induction principle for quotients indexed by a `multiset`. -/
@[nolint decidable_classical, elab_as_eliminator]
lemma quotient_induction_on {m : multiset ι}
  {C : (Π i ∈ m, quotient (S i)) → Prop}
  (q : Π i ∈ m, quotient (S i)) (f : ∀ a : Π i ∈ m, α i, C (λ i hi, ⟦a i hi⟧)) :
  C q :=
quotient_ind f q

/-- Recursion principle for quotients indexed by a `multiset`. -/
@[elab_as_eliminator] def quotient_rec_on {m : multiset ι} :
  Π {C : (Π i ∈ m, quotient (S i)) → Sort*}
  (q : Π i ∈ m, quotient (S i))
  (f : Π a : Π i ∈ m, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ m, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
    (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
      C (λ i hi, ⟦b i hi⟧)) = f b),
  C q :=
quotient.hrec_on m (@list.quotient_rec_on _ _ _ _)
  (λ l₁ l₂ hl, list.quotient_rec_on_heq (λ i, list.perm.mem_iff hl))

/-- Recursion principle for quotients indexed by a `multiset`. -/
@[elab_as_eliminator] def quotient_rec {m : multiset ι} {C : (Π i ∈ m, quotient (S i)) → Sort*}
  (f : Π a : Π i ∈ m, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ m, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
    (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
      C (λ i hi, ⟦b i hi⟧)) = f b)
  (q : Π i ∈ m, quotient (S i)) :
  C q :=
quotient_rec_on q f h

/-- Recursion principle for quotients indexed by a `multiset`. -/
@[elab_as_eliminator] def quotient_hrec_on {m : multiset ι} {C : (Π i ∈ m, quotient (S i)) → Sort*}
  (q : Π i ∈ m, quotient (S i))
  (f : Π a : Π i ∈ m, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ m, α i) (h : ∀ i hi, a i hi ≈ b i hi), f a == f b) :
  C q :=
quotient_rec_on q f (λ a b p, eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))

@[simp] lemma quotient_rec_mk {m : multiset ι} {C : (Π i ∈ m, quotient (S i)) → Sort*}
  (f : Π a : Π i ∈ m, α i, C (λ i hi, ⟦a i hi⟧))
  (h) (a : Π i ∈ m, α i) :
  @quotient_rec _ _ _ _ _ C f h (λ i hi, ⟦a i hi⟧) = f a :=
by { induction m using quotient.ind, exact list.quotient_rec_mk f h a }

@[simp] lemma quotient_rec_on_mk {m : multiset ι} {C : (Π i ∈ m, quotient (S i)) → Sort*}
  (a : Π i ∈ m, α i) :
  @quotient_rec_on _ _ _ _ _ C (λ i hi, ⟦a i hi⟧) = λ f h, f a :=
by { ext f h, exact quotient_rec_mk _ _ _, }

end multiset
