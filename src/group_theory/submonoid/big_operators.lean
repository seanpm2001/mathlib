/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/

import algebra.big_operators.basic
import data.finset.noncomm_prod
import group_theory.submonoid.membership

/-!
# Submonoids: membership criteria

TODO
-/

open_locale big_operators

variables {M A B : Type*}

section assoc
variables [monoid M] [set_like B M] [submonoid_class B M] {S : B}

namespace submonoid_class

@[simp, norm_cast, to_additive] theorem coe_list_prod (l : list S) :
  (l.prod : M) = (l.map coe).prod :=
(submonoid_class.subtype S : _ →* M).map_list_prod l

@[simp, norm_cast, to_additive] theorem coe_multiset_prod {M} [comm_monoid M] [set_like B M]
  [submonoid_class B M] (m : multiset S) : (m.prod : M) = (m.map coe).prod :=
(submonoid_class.subtype S : _ →* M).map_multiset_prod m

@[simp, norm_cast, to_additive] theorem coe_finset_prod {ι M} [comm_monoid M] [set_like B M]
  [submonoid_class B M] (f : ι → S) (s : finset ι) :
  ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
(submonoid_class.subtype S : _ →* M).map_prod f s

end submonoid_class

open submonoid_class

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
lemma list_prod_mem {l : list M} (hl : ∀ x ∈ l, x ∈ S) : l.prod ∈ S :=
by { lift l to list S using hl, rw ← coe_list_prod, exact l.prod.coe_prop }

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is
in the `add_submonoid`."]
lemma multiset_prod_mem {M} [comm_monoid M] [set_like B M] [submonoid_class B M] (m : multiset M)
  (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S :=
by { lift m to multiset S using hm, rw ← coe_multiset_prod, exact m.prod.coe_prop }

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`
is in the `add_submonoid`."]
lemma prod_mem {M : Type*} [comm_monoid M] [set_like B M] [submonoid_class B M]
  {ι : Type*} {t : finset ι} {f : ι → M} (h : ∀c ∈ t, f c ∈ S) :
  ∏ c in t, f c ∈ S :=
multiset_prod_mem (t.1.map f) $ λ x hx, let ⟨i, hi, hix⟩ := multiset.mem_map.1 hx in hix ▸ h i hi

namespace submonoid

variables (s : submonoid M)

@[simp, norm_cast, to_additive] theorem coe_list_prod (l : list s) :
  (l.prod : M) = (l.map coe).prod :=
s.subtype.map_list_prod l

@[simp, norm_cast, to_additive] theorem coe_multiset_prod {M} [comm_monoid M] (S : submonoid M)
  (m : multiset S) : (m.prod : M) = (m.map coe).prod :=
S.subtype.map_multiset_prod m

@[simp, norm_cast, to_additive] theorem coe_finset_prod {ι M} [comm_monoid M] (S : submonoid M)
  (f : ι → S) (s : finset ι) :
  ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
S.subtype.map_prod f s



/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
lemma list_prod_mem {l : list M} (hl : ∀ x ∈ l, x ∈ s) : l.prod ∈ s :=
by { lift l to list s using hl, rw ← coe_list_prod, exact l.prod.coe_prop }

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is
in the `add_submonoid`."]
lemma multiset_prod_mem {M} [comm_monoid M] (S : submonoid M) (m : multiset M)
  (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S :=
by { lift m to multiset S using hm, rw ← coe_multiset_prod, exact m.prod.coe_prop }

@[to_additive]
lemma multiset_noncomm_prod_mem (S : submonoid M) (m : multiset M) (comm) (h : ∀ (x ∈ m), x ∈ S) :
  m.noncomm_prod comm ∈ S :=
begin
  induction m using quotient.induction_on with l,
  simp only [multiset.quot_mk_to_coe, multiset.noncomm_prod_coe],
  exact submonoid.list_prod_mem _ h,
end

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`
is in the `add_submonoid`."]
lemma prod_mem {M : Type*} [comm_monoid M] (S : submonoid M)
  {ι : Type*} {t : finset ι} {f : ι → M} (h : ∀c ∈ t, f c ∈ S) :
  ∏ c in t, f c ∈ S :=
S.multiset_prod_mem (t.1.map f) $ λ x hx, let ⟨i, hi, hix⟩ := multiset.mem_map.1 hx in hix ▸ h i hi
@[to_additive]
lemma noncomm_prod_mem (S : submonoid M) {ι : Type*} (t : finset ι) (f : ι → M) (comm)
  (h : ∀ c ∈ t, f c ∈ S) :
  t.noncomm_prod f comm ∈ S :=
begin
  apply multiset_noncomm_prod_mem,
  intro y,
  rw multiset.mem_map,
  rintros ⟨x, ⟨hx, rfl⟩⟩,
  exact h x hx,
end

end submonoid

end assoc

namespace submonoid

variables [monoid M]

open monoid_hom

@[to_additive] lemma closure_eq_image_prod (s : set M) :
  (closure s : set M) = list.prod '' {l : list M | ∀ x ∈ l, x ∈ s} :=
begin
  rw [closure_eq_mrange, coe_mrange, ← list.range_map_coe, ← set.range_comp],
  refl
end

@[to_additive]
lemma exists_list_of_mem_closure {s : set M} {x : M} (hx : x ∈ closure s) :
  ∃ (l : list M) (hl : ∀ y ∈ l, y ∈ s), l.prod = x :=
by rwa [← set_like.mem_coe, closure_eq_image_prod, set.mem_image_iff_bex] at hx

@[to_additive]
lemma exists_multiset_of_mem_closure {M : Type*} [comm_monoid M] {s : set M}
  {x : M} (hx : x ∈ closure s) : ∃ (l : multiset M) (hl : ∀ y ∈ l, y ∈ s), l.prod = x :=
begin
  obtain ⟨l, h1, h2⟩ := exists_list_of_mem_closure hx,
  exact ⟨l, h1, (multiset.coe_prod l).trans h2⟩,
end

end submonoid
