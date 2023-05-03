/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/

import group_theory.subgroup.basic
import ring_theory.non_unital_subsemiring.basic

/-!
# non_unital_subrings

Let `R` be a non-unital ring. This file defines the "bundled" non-unital subring type
`non_unital_subring R`, a type whose terms correspond to non-unital subrings of `R`.
This is the preferred way to talk about non-unital non-unital subrings in mathlib.

We prove that non-unital subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `set R` to `non_unital_subring R`, sending a subset of
`R` to the non-unital subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [non_unital_ring R] (S : Type u) [non_unital_ring S] (f g : R →ₙ+* S)`
`(A : non_unital_subring R) (B : non_unital_subring S) (s : set R)`

* `non_unital_subring R` : the type of non-unital subrings of a ring `R`.

* `instance : complete_lattice (non_unital_subring R)` : the complete lattice structure on the
  non-unital subrings.

* `non_unital_subring.center` : the center of a non-unital ring `R`.

* `non_unital_subring.closure` : non-unital subring closure of a set, i.e., the smallest
  non-unital subring that includes the set.

* `non_unital_subring.gi` : `closure : set M → non_unital_subring M` and coercion
  `coe : non_unital_subring M → set M`
  form a `galois_insertion`.

* `comap f B : non_unital_subring A` : the preimage of a non-unital subring `B` along the
  non-unital ring homomorphism `f`

* `map f A : non_unital_subring B` : the image of a non-unital subring `A` along the
  non-unital ring homomorphism `f`.

* `prod A B : non_unital_subring (R × S)` : the product of non-unital subrings

* `f.range : non_unital_subring B` : the range of the non-unital ring homomorphism `f`.

* `eq_locus f g : non_unital_subring R` : given non-unital ring homomorphisms `f g : R →ₙ+* S`,
     the non-unital subring of `R` where `f x = g x`

## Implementation notes

A non-unital subring is implemented as a non-unital non_unital_subsemiring which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non_unital_subring's underlying set.

## Tags
non-unital subring
-/

open_locale big_operators
universes u v w

section basic

variables {R : Type u} {S : Type v} {T : Type w} [non_unital_ring R]

section non_unital_subring_class

/-- `non_unital_subring_class S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
class non_unital_subring_class (S : Type*) (R : Type u) [non_unital_ring R] [set_like S R]
  extends non_unital_subsemiring_class S R, neg_mem_class S R : Prop

@[priority 100] -- See note [lower instance priority]
instance non_unital_subring_class.add_subgroup_class (S : Type*) (R : Type u) [set_like S R]
  [non_unital_ring R] [h : non_unital_subring_class S R] : add_subgroup_class S R :=
{ .. h }

variables [set_like S R] [hSR : non_unital_subring_class S R] (s : S)
include hSR

namespace non_unital_subring_class

/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
@[priority 75]
-- Prefer subclasses of `non_unital_ring` over subclasses of `non_unital_subring_class`.
instance to_non_unital_ring : non_unital_ring s :=
subtype.coe_injective.non_unital_ring coe rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl)

omit hSR
/-- A non-unital subring of a `non_unital_comm_ring` is a `non_unital_comm_ring`. -/
@[priority 75]
-- Prefer subclasses of `non_unital_ring` over subclasses of `non_unital_subring_class`.
instance to_non_unital_comm_ring {R} [non_unital_comm_ring R] [set_like S R]
  [non_unital_subring_class S R] : non_unital_comm_ring s :=
subtype.coe_injective.non_unital_comm_ring coe rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl)

-- TODO: `is_domain` should be generalized to `non_unital_non_assoc_semiring`
/- A non_unital_subring of a domain is a domain.
@[priority 75] -- Prefer subclasses of `ring` over subclasses of `non_unital_subring_class`.
instance {R} [ring R] [is_domain R] [set_like S R] [non_unital_subring_class S R] : is_domain s :=
no_zero_divisors.to_is_domain _ -/

include hSR

/-- The natural ring hom from a non-unital subring of non-unital ring `R` to `R`. -/
def subtype (s : S) : s →ₙ+* R :=
{ to_fun := coe,
 .. non_unital_subsemiring_class.subtype s,
 .. add_subgroup_class.subtype s }

@[simp] theorem coe_subtype : (subtype s : s → R) = coe := rfl

end non_unital_subring_class

end non_unital_subring_class

variables [non_unital_ring S] [non_unital_ring T]

set_option old_structure_cmd true

/-- `non_unital_subring R` is the type of non-unital subrings of `R`. A non-unital subring of `R`
is a subset `s` that is a multiplicative subsemigroup and an additive subgroup. Note in particular
that it shares the same 0 as R. -/
structure non_unital_subring (R : Type u) [non_unital_ring R]
  extends non_unital_subsemiring R, add_subgroup R

/-- Reinterpret a `non_unital_subring` as a `non_unital_subsemiring`. -/
add_decl_doc non_unital_subring.to_non_unital_subsemiring

/-- Reinterpret a `non_unital_subring` as an `add_subgroup`. -/
add_decl_doc non_unital_subring.to_add_subgroup

namespace non_unital_subring

/-- The underlying submonoid of a non_unital_subring. -/
def to_subsemigroup (s : non_unital_subring R) : subsemigroup R :=
{ carrier := s.carrier,
  ..s.to_non_unital_subsemiring.to_subsemigroup }

instance : set_like (non_unital_subring R) R :=
{ coe := non_unital_subring.carrier,
  coe_injective' := λ p q h, by cases p; cases q; congr' }

instance : non_unital_subring_class (non_unital_subring R) R :=
{ zero_mem := zero_mem',
  add_mem := add_mem',
  mul_mem := mul_mem',
  neg_mem := neg_mem' }

@[simp]
lemma mem_carrier {s : non_unital_subring R} {x : R} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[simp]
lemma mem_mk {S : set R} {x : R} (h₁ h₂ h₃ h₄) :
  x ∈ (⟨S, h₁, h₂, h₃, h₄⟩ : non_unital_subring R) ↔ x ∈ S := iff.rfl

@[simp] lemma coe_set_mk (S : set R) (h₁ h₂ h₃ h₄) :
  ((⟨S, h₁, h₂, h₃, h₄⟩ : non_unital_subring R) : set R) = S := rfl

@[simp]
lemma mk_le_mk {S S' : set R} (h₁ h₂ h₃  h₄ h₁' h₂' h₃'  h₄') :
  (⟨S, h₁, h₂, h₃, h₄⟩ : non_unital_subring R) ≤ (⟨S', h₁', h₂', h₃', h₄'⟩ : non_unital_subring R) ↔ S ⊆ S' :=
iff.rfl

/-- Two non-unital subrings are equal if they have the same elements. -/
@[ext] theorem ext {S T : non_unital_subring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

/-- Copy of a non-unital subring with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (S : non_unital_subring R) (s : set R) (hs : s = ↑S) : non_unital_subring R :=
{ carrier := s,
  neg_mem' := λ _, hs.symm ▸ S.neg_mem',
  ..S.to_non_unital_subsemiring.copy s hs }

@[simp] lemma coe_copy (S : non_unital_subring R) (s : set R) (hs : s = ↑S) :
  (S.copy s hs : set R) = s := rfl

lemma copy_eq (S : non_unital_subring R) (s : set R) (hs : s = ↑S) : S.copy s hs = S :=
set_like.coe_injective hs

lemma to_non_unital_subsemiring_injective :
  function.injective (to_non_unital_subsemiring : non_unital_subring R → non_unital_subsemiring R)
| r s h := ext (set_like.ext_iff.mp h : _)

@[mono]
lemma to_non_unital_subsemiring_strict_mono :
  strict_mono (to_non_unital_subsemiring : non_unital_subring R → non_unital_subsemiring R) :=
λ _ _, id

@[mono]
lemma to_non_unital_subsemiring_mono :
  monotone (to_non_unital_subsemiring : non_unital_subring R → non_unital_subsemiring R) :=
to_non_unital_subsemiring_strict_mono.monotone

lemma to_add_subgroup_injective :
  function.injective (to_add_subgroup : non_unital_subring R → add_subgroup R)
| r s h := ext (set_like.ext_iff.mp h : _)

@[mono]
lemma to_add_subgroup_strict_mono :
  strict_mono (to_add_subgroup : non_unital_subring R → add_subgroup R) :=
λ _ _, id

@[mono]
lemma to_add_subgroup_mono :
  monotone (to_add_subgroup : non_unital_subring R → add_subgroup R) :=
to_add_subgroup_strict_mono.monotone

lemma to_subsemigroup_injective :
  function.injective (to_subsemigroup : non_unital_subring R → subsemigroup R)
| r s h := ext (set_like.ext_iff.mp h : _)

@[mono]
lemma to_subsemigroup_strict_mono :
  strict_mono (to_subsemigroup : non_unital_subring R → subsemigroup R) :=
λ _ _, id

@[mono]
lemma to_subsemigroup_mono :
  monotone (to_subsemigroup : non_unital_subring R → subsemigroup R) :=
to_subsemigroup_strict_mono.monotone

/-- Construct a `non_unital_subring R` from a set `s`, a subsemigroup `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : set R) (sm : subsemigroup R) (sa : add_subgroup R)
  (hm : ↑sm = s) (ha : ↑sa = s) :
  non_unital_subring R :=
{ carrier := s,
  zero_mem' := ha ▸ sa.zero_mem,
  add_mem' := λ x y, by simpa only [← ha] using sa.add_mem,
  mul_mem' := λ x y, by simpa only [← hm] using sm.mul_mem,
  neg_mem' := λ x, by simpa only [← ha] using sa.neg_mem, }

@[simp] lemma coe_mk' {s : set R} {sm : subsemigroup R} (hm : ↑sm = s)
  {sa : add_subgroup R} (ha : ↑sa = s) :
  (non_unital_subring.mk' s sm sa hm ha : set R) = s := rfl

@[simp] lemma mem_mk' {s : set R} {sm : subsemigroup R} (hm : ↑sm = s)
  {sa : add_subgroup R} (ha : ↑sa = s) {x : R} :
  x ∈ non_unital_subring.mk' s sm sa hm ha ↔ x ∈ s :=
iff.rfl

@[simp] lemma mk'_to_subsemigroup {s : set R} {sm : subsemigroup R} (hm : ↑sm = s)
  {sa : add_subgroup R} (ha : ↑sa = s) :
  (non_unital_subring.mk' s sm sa hm ha).to_subsemigroup = sm :=
set_like.coe_injective hm.symm

@[simp] lemma mk'_to_add_subgroup {s : set R} {sm : subsemigroup R} (hm : ↑sm = s)
  {sa : add_subgroup R} (ha : ↑sa  =s) :
  (non_unital_subring.mk' s sm sa hm ha).to_add_subgroup = sa :=
set_like.coe_injective ha.symm

end non_unital_subring

namespace non_unital_subring

variables (s : non_unital_subring R)

/-- A non-unital subring contains the ring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s := zero_mem _

/-- A non-unital subring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s := mul_mem

/-- A non-unital subring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s := add_mem

/-- A non-unital subring is closed under negation. -/
protected theorem neg_mem {x : R} : x ∈ s → -x ∈ s := neg_mem

/-- A non-unital subring is closed under subtraction -/
protected theorem sub_mem {x y : R} (hx : x ∈ s) (hy : y ∈ s) : x - y ∈ s := sub_mem hx hy

/-- Sum of a list of elements in a non-unital subring is in the non-unital subring. -/
protected lemma list_sum_mem {l : list R} : (∀x ∈ l, x ∈ s) → l.sum ∈ s := list_sum_mem

/-- Sum of a multiset of elements in an `non_unital_subring` of a `non_unital_ring` is
in the `non_unital_subring`. -/
protected lemma multiset_sum_mem {R} [non_unital_ring R](s : non_unital_subring R)
  (m : multiset R) : (∀a ∈ m, a ∈ s) → m.sum ∈ s :=
multiset_sum_mem _

/-- Sum of elements in a `non_unital_subring` of a `non_unital_ring` indexed by a `finset`
is in the `non_unital_subring`. -/
protected lemma sum_mem {R : Type*} [non_unital_ring R] (s : non_unital_subring R)
  {ι : Type*} {t : finset ι} {f : ι → R} (h : ∀c ∈ t, f c ∈ s) :
  ∑ i in t, f i ∈ s :=
sum_mem h

/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
instance to_non_unital_ring : non_unital_ring s :=
subtype.coe_injective.non_unital_ring coe rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl)

protected lemma zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s := zsmul_mem hx n

@[simp, norm_cast] lemma coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_neg (x : s) : (↑(-x) : R) = -↑x := rfl
@[simp, norm_cast] lemma coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : s) : R) = 0 := rfl

-- TODO: can be generalized to `add_submonoid_class`
@[simp] lemma coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 :=
⟨λ h, subtype.ext (trans h s.coe_zero.symm),
 λ h, h.symm ▸ s.coe_zero⟩

/-- A non-unital subring of a `non_unital_comm_ring` is a `non_unital_comm_ring`. -/
instance to_non_unital_comm_ring {R} [non_unital_comm_ring R] (s : non_unital_subring R) :
  non_unital_comm_ring s :=
subtype.coe_injective.non_unital_comm_ring coe rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl)

/-! ## Partial order -/

@[simp] lemma mem_to_subsemigroup {s : non_unital_subring R} {x : R} : x ∈ s.to_subsemigroup ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_subsemigroup (s : non_unital_subring R) : (s.to_subsemigroup : set R) = s := rfl
@[simp] lemma mem_to_add_subgroup {s : non_unital_subring R} {x : R} :
  x ∈ s.to_add_subgroup ↔ x ∈ s := iff.rfl
@[simp] lemma coe_to_add_subgroup (s : non_unital_subring R) : (s.to_add_subgroup : set R) = s := rfl

/-! ## top -/

/-- The non-unital subring `R` of the ring `R`. -/
instance : has_top (non_unital_subring R) :=
⟨{ .. (⊤ : subsemigroup R), .. (⊤ : add_subgroup R) }⟩

@[simp] lemma mem_top (x : R) : x ∈ (⊤ : non_unital_subring R) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : non_unital_subring R) : set R) = set.univ := rfl

/- TODO: FIX ME
/-- The ring equiv between the top element of `non_unital_subring R` and `R`. -/
@[simps]
def top_equiv : (⊤ : non_unital_subring R) ≃+* R := non_unital_subsemiring.top_equiv
-/

end non_unital_subring

end basic

section hom

namespace non_unital_subring

variables {F : Type w} {R : Type u} {S : Type v} {T : Type*} {SR : Type*}
variables [non_unital_ring R] [non_unital_ring S] [non_unital_ring T]
variables [non_unital_ring_hom_class F R S] (s : non_unital_subring R)

/-! ## comap -/

/-- The preimage of a non_unital_subring along a ring homomorphism is a non_unital_subring. -/
def comap {F : Type w} {R : Type u} {S : Type v} [non_unital_ring R] [non_unital_ring S]
  [non_unital_ring_hom_class F R S] (f : F) (s : non_unital_subring S) : non_unital_subring R :=
{ carrier := f ⁻¹' s.carrier,
 .. s.to_subsemigroup.comap (f : R →ₙ* S),
  .. s.to_add_subgroup.comap (f : R →+ S) }

@[simp] lemma coe_comap (s : non_unital_subring S) (f : F) :
  (s.comap f : set R) = f ⁻¹' s := rfl

@[simp]
lemma mem_comap {s : non_unital_subring S} {f : F} {x : R} :
  x ∈ s.comap f ↔ f x ∈ s := iff.rfl

lemma comap_comap (s : non_unital_subring T) (g : S →ₙ+* T) (f : R →ₙ+* S) :
  (s.comap g).comap f = s.comap (g.comp f) :=
rfl

/-! ## map -/

/-- The image of a non_unital_subring along a ring homomorphism is a non_unital_subring. -/
def map {F : Type w} {R : Type u} {S : Type v} [non_unital_ring R] [non_unital_ring S]
  [non_unital_ring_hom_class F R S] (f : F) (s : non_unital_subring R) : non_unital_subring S :=
  { carrier := f '' s.carrier,
.. s.to_subsemigroup.map (f : R →ₙ* S),
.. s.to_add_subgroup.map (f : R →+ S) }

@[simp] lemma coe_map (f : F) (s : non_unital_subring R) : (s.map f : set S) = f '' s := rfl

@[simp] lemma mem_map {f : F} {s : non_unital_subring R} {y : S} :
  y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
set.mem_image_iff_bex

@[simp] lemma map_id : s.map (non_unital_ring_hom.id R) = s :=
set_like.coe_injective $ set.image_id _

lemma map_map (g : S →ₙ+* T) (f : R →ₙ+* S) : (s.map f).map g = s.map (g.comp f) :=
set_like.coe_injective $ set.image_image _ _ _

lemma map_le_iff_le_comap {f : F} {s : non_unital_subring R} {t : non_unital_subring S} :
  s.map f ≤ t ↔ s ≤ t.comap f :=
set.image_subset_iff

lemma gc_map_comap (f : F) :
  galois_connection (map f : non_unital_subring R → non_unital_subring S) (comap f) :=
λ S T, map_le_iff_le_comap

/-- A non_unital_subring is isomorphic to its image under an injective function -/
noncomputable def equiv_map_of_injective
  (f : F) (hf : function.injective (f : R → S)) : s ≃+* s.map f :=
{ map_mul' := λ _ _, subtype.ext (map_mul f _ _),
  map_add' := λ _ _, subtype.ext (map_add f _ _),
  ..equiv.set.image f s hf }

@[simp] lemma coe_equiv_map_of_injective_apply
  (f : F) (hf : function.injective f) (x : s) :
  (equiv_map_of_injective s f hf x : S) = f x := rfl

end non_unital_subring

namespace non_unital_ring_hom

variables {R : Type u} {S : Type v} {T : Type*}
variables [non_unital_ring R] [non_unital_ring S] [non_unital_ring T]
variables (g : S →ₙ+* T) (f : R →ₙ+* S)

/-! ## range -/

/-- The range of a ring homomorphism, as a non_unital_subring of the target. See Note [range copy pattern]. -/
def range {R : Type u} {S : Type v} [non_unital_ring R] [non_unital_ring S]
  (f : R →ₙ+* S) : non_unital_subring S :=
((⊤ : non_unital_subring R).map f).copy (set.range f) set.image_univ.symm

@[simp] lemma coe_range : (f.range : set S) = set.range f := rfl

@[simp] lemma mem_range {f : R →ₙ+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y := iff.rfl

lemma range_eq_map (f : R →ₙ+* S) : f.range = non_unital_subring.map f ⊤ :=
by { ext, simp }

lemma mem_range_self (f : R →ₙ+* S) (x : R) : f x ∈ f.range :=
mem_range.mpr ⟨x, rfl⟩

lemma map_range : f.range.map g = (g.comp f).range :=
by simpa only [range_eq_map] using (⊤ : non_unital_subring R).map_map g f

/-- The range of a ring homomorphism is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype S`. -/
instance fintype_range [fintype R] [decidable_eq S] (f : R →ₙ+* S) : fintype (range f) :=
set.fintype_range f

end non_unital_ring_hom

namespace non_unital_subring

variables {F : Type w} {R : Type u} {S : Type v} {T : Type*}
variables [non_unital_ring R] [non_unital_ring S] [non_unital_ring T]
variables [non_unital_ring_hom_class F R S]
variables (g : S →ₙ+* T) (f : R →ₙ+* S)

/-! ## bot -/

instance : has_bot (non_unital_subring R) := ⟨(0 : R →ₙ+* R).range⟩

instance : inhabited (non_unital_subring R) := ⟨⊥⟩

lemma coe_bot : ((⊥ : non_unital_subring R) : set R) = {0} :=
(non_unital_ring_hom.coe_range (0 : R →ₙ+* R)).trans (@set.range_const R R _ 0)

lemma mem_bot {x : R} : x ∈ (⊥ : non_unital_subring R) ↔ x = 0 :=
show x ∈ ((⊥ : non_unital_subring R) : set R) ↔ x = 0, by rw [coe_bot, set.mem_singleton_iff]

/-! ## inf -/

/-- The inf of two non_unital_subrings is their intersection. -/
instance : has_inf (non_unital_subring R) :=
⟨λ s t,
  { carrier := s ∩ t,
    .. s.to_subsemigroup ⊓ t.to_subsemigroup,
    .. s.to_add_subgroup ⊓ t.to_add_subgroup }⟩

@[simp] lemma coe_inf (p p' : non_unital_subring R) :
  ((p ⊓ p' : non_unital_subring R) : set R) = p ∩ p' := rfl

@[simp] lemma mem_inf {p p' : non_unital_subring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

instance : has_Inf (non_unital_subring R) :=
⟨λ s, non_unital_subring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, non_unital_subring.to_subsemigroup t )
  (⨅ t ∈ s, non_unital_subring.to_add_subgroup t) (by simp) (by simp)⟩

@[simp, norm_cast] lemma coe_Inf (S : set (non_unital_subring R)) :
  ((Inf S : non_unital_subring R) : set R) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (non_unital_subring R)} {x : R} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
set.mem_Inter₂

@[simp, norm_cast] lemma coe_infi {ι : Sort*} {S : ι → non_unital_subring R} :
  (↑(⨅ i, S i) : set R) = ⋂ i, S i :=
by simp only [infi, coe_Inf, set.bInter_range]

lemma mem_infi {ι : Sort*} {S : ι → non_unital_subring R} {x : R} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp] lemma Inf_to_subsemigroup (s : set (non_unital_subring R)) :
  (Inf s).to_subsemigroup = ⨅ t ∈ s, non_unital_subring.to_subsemigroup t := mk'_to_subsemigroup _ _

@[simp] lemma Inf_to_add_subgroup (s : set (non_unital_subring R)) :
  (Inf s).to_add_subgroup = ⨅ t ∈ s, non_unital_subring.to_add_subgroup t := mk'_to_add_subgroup _ _

/-- non_unital_subrings of a ring form a complete lattice. -/
instance : complete_lattice (non_unital_subring R) :=
{ bot := (⊥),
  bot_le := λ s x hx, (mem_bot.mp hx).symm ▸ zero_mem s,
  top := (⊤),
  le_top := λ s x hx, trivial,
  inf := (⊓),
  inf_le_left := λ s t x, and.left,
  inf_le_right := λ s t x, and.right,
  le_inf := λ s t₁ t₂ h₁ h₂ x hx, ⟨h₁ hx, h₂ hx⟩,
  .. complete_lattice_of_Inf (non_unital_subring R)
    (λ s, is_glb.of_image (λ s t,
      show (s : set R) ≤ t ↔ s ≤ t, from set_like.coe_subset_coe) is_glb_binfi)}

lemma eq_top_iff' (A : non_unital_subring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
eq_top_iff.trans ⟨λ h m, h $ mem_top m, λ h m _, h m⟩

/-! ## Center of a ring -/

section

variables (R)

-- this needs to go elsewhere, or rather just generalize `set.neg_mem_center`
@[simp]
lemma _root_.set.neg_mem_center' {R : Type*} [non_unital_non_assoc_ring R] {a : R}
  (ha : a ∈ set.center R) : -a ∈ set.center R :=
λ c, by rw [←neg_mul_comm, ha (-c), neg_mul_comm]


/-- The center of a ring `R` is the set of elements that commute with everything in `R` -/
def center : non_unital_subring R :=
{ carrier := set.center R,
  neg_mem' := λ a, set.neg_mem_center',
  .. non_unital_subsemiring.center R }

lemma coe_center : ↑(center R) = set.center R := rfl

@[simp] lemma center_to_non_unital_subsemiring :
  (center R).to_non_unital_subsemiring = non_unital_subsemiring.center R := rfl

variables {R}

lemma mem_center_iff {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
iff.rfl

instance decidable_mem_center [decidable_eq R] [fintype R] : decidable_pred (∈ center R) :=
λ _, decidable_of_iff' _ mem_center_iff

@[simp] lemma center_eq_top (R) [non_unital_comm_ring R] : center R = ⊤ :=
set_like.coe_injective (set.center_eq_univ R)

/-- The center is commutative. -/
instance : non_unital_comm_ring (center R) :=
{ ..non_unital_subsemiring.center.non_unital_comm_semiring,
  ..(center R).to_non_unital_ring}

end

/-! ## non_unital_subring closure of a subset -/

/-- The `non_unital_subring` generated by a set. -/
def closure (s : set R) : non_unital_subring R := Inf {S | s ⊆ S}

lemma mem_closure {x : R} {s : set R} : x ∈ closure s ↔ ∀ S : non_unital_subring R, s ⊆ S → x ∈ S :=
mem_Inf

/-- The non_unital_subring generated by a set includes the set. -/
@[simp] lemma subset_closure {s : set R} : s ⊆ closure s := λ x hx, mem_closure.2 $ λ S hS, hS hx

lemma not_mem_of_not_mem_closure {s : set R} {P : R} (hP : P ∉ closure s) : P ∉ s :=
λ h, hP (subset_closure h)

/-- A non_unital_subring `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
lemma closure_le {s : set R} {t : non_unital_subring R} : closure s ≤ t ↔ s ⊆ t :=
⟨set.subset.trans subset_closure, λ h, Inf_le h⟩

/-- non_unital_subring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
lemma closure_mono ⦃s t : set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
closure_le.2 $ set.subset.trans h subset_closure

lemma closure_eq_of_le {s : set R} {t : non_unital_subring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
  closure s = t :=
le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_eliminator]
lemma closure_induction {s : set R} {p : R → Prop} {x} (h : x ∈ closure s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0)
  (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hneg : ∀ (x : R), p x → p (-x))
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
(@closure_le _ _ _ ⟨p, Hadd, H0, Hmul, Hneg⟩).2 Hs h

/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_eliminator]
lemma closure_induction₂ {s : set R} {p : R → R → Prop} {a b : R}
  (ha : a ∈ closure s) (hb : b ∈ closure s)
  (Hs : ∀ (x ∈ s) (y ∈ s), p x y)
  (H0_left : ∀ x, p 0 x)
  (H0_right : ∀ x, p x 0)
  (Hneg_left : ∀ x y, p x y → p (-x) y)
  (Hneg_right : ∀ x y, p x y → p x (-y))
  (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
  (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
  (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
  (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p a b :=
begin
  refine closure_induction hb _ (H0_right _)
    (Hadd_right a) (Hneg_right a) (Hmul_right a),
  refine closure_induction ha Hs (λ x _, H0_left x) _ _ _,
  { exact (λ x y H₁ H₂ z zs, Hadd_left x y z (H₁ z zs) (H₂ z zs)) },
  { exact (λ x hx z zs, Hneg_left x z (hx z zs)) },
  { exact (λ x y H₁ H₂ z zs, Hmul_left x y z (H₁ z zs) (H₂ z zs)) }
end

lemma mem_closure_iff {s : set R} {x} :
  x ∈ closure s ↔ x ∈ add_subgroup.closure (subsemigroup.closure s : set R) :=
⟨λ h, closure_induction h (λ x hx, add_subgroup.subset_closure $ subsemigroup.subset_closure hx)
 (add_subgroup.zero_mem _)
 (λ x y hx hy, add_subgroup.add_mem _ hx hy )
 (λ x hx, add_subgroup.neg_mem _ hx )
   (λ x y hx hy, add_subgroup.closure_induction hy
     (λ q hq, add_subgroup.closure_induction hx
       (λ p hp, add_subgroup.subset_closure ((subsemigroup.closure s).mul_mem hp hq))
       (begin rw zero_mul q, apply add_subgroup.zero_mem _, end)
       (λ p₁ p₂ ihp₁ ihp₂, begin rw add_mul p₁ p₂ q, apply add_subgroup.add_mem _ ihp₁ ihp₂, end)
       (λ x hx, begin have f : -x * q = -(x*q) :=
         by simp, rw f, apply add_subgroup.neg_mem _ hx, end))
     (begin rw mul_zero x, apply add_subgroup.zero_mem _, end)
     (λ q₁ q₂ ihq₁ ihq₂, begin rw mul_add x q₁ q₂, apply add_subgroup.add_mem _ ihq₁ ihq₂ end)
     (λ z hz, begin have f : x * -z = -(x*z) := by simp,
       rw f, apply add_subgroup.neg_mem _ hz, end)),
 λ h, add_subgroup.closure_induction h
   (λ x hx, subsemigroup.closure_induction hx
     (λ x hx, subset_closure hx)
     (λ x y hx hy, mul_mem hx hy))
 (zero_mem _)
 (λ x y hx hy, add_mem hx hy)
 (λ x hx, neg_mem hx)⟩

/-- If all elements of `s : set A` commute pairwise, then `closure s` is a commutative ring.  -/
def closure_non_unital_comm_ring_of_comm {s : set R} (hcomm : ∀ (a ∈ s) (b ∈ s), a * b = b * a) :
  non_unital_comm_ring (closure s) :=
{ mul_comm := λ x y,
  begin
    ext,
    simp only [non_unital_subring.coe_mul],
    refine closure_induction₂ x.prop y.prop
    hcomm
    (λ x, by simp only [mul_zero, zero_mul])
    (λ x, by simp only [mul_zero, zero_mul])
    (λ x y hxy, by simp only [mul_neg, neg_mul, hxy])
    (λ x y hxy, by simp only [mul_neg, neg_mul, hxy])
    (λ x₁ x₂ y h₁ h₂, by simp only [add_mul, mul_add, h₁, h₂])
    (λ x₁ x₂ y h₁ h₂, by simp only [add_mul, mul_add, h₁, h₂])
    (λ x₁ x₂ y h₁ h₂, by rw [←mul_assoc, ←h₁, mul_assoc x₁ y x₂, ←h₂, mul_assoc])
    (λ x₁ x₂ y h₁ h₂, by rw [←mul_assoc, h₁, mul_assoc, h₂, ←mul_assoc])
  end,
  ..(closure s).to_non_unital_ring }


/- probably there is a version if `x ≠ 0`, but we don't have `list.prod`
theorem exists_list_of_mem_closure {s : set R} {x : R} (h : x ∈ closure s) :
  (∃ L : list (list R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s ∨ y = (-1:R)) ∧ (L.map list.prod).sum = x) :=
add_subgroup.closure_induction (mem_closure_iff.1 h)
  (λ x hx, let ⟨l, hl, h⟩ :=submonoid.exists_list_of_mem_closure hx in ⟨[l], by simp [h];
    clear_aux_decl; tauto!⟩)
  ⟨[], by simp⟩
  (λ x y ⟨l, hl1, hl2⟩ ⟨m, hm1, hm2⟩, ⟨l ++ m, λ t ht, (list.mem_append.1 ht).elim (hl1 t) (hm1 t),
    by simp [hl2, hm2]⟩)
  (λ x ⟨L, hL⟩, ⟨L.map (list.cons (-1)), list.forall_mem_map_iff.2 $ λ j hj, list.forall_mem_cons.2
    ⟨or.inr rfl, hL.1 j hj⟩, hL.2 ▸ list.rec_on L (by simp)
      (by simp [list.map_cons, add_comm] {contextual := tt})⟩)
-/

variable (R)
/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure R _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variable {R}

/-- Closure of a non_unital_subring `S` equals `S`. -/
lemma closure_eq (s : non_unital_subring R) : closure (s : set R) = s :=
(non_unital_subring.gi R).l_u_eq s

@[simp] lemma closure_empty : closure (∅ : set R) = ⊥ := (non_unital_subring.gi R).gc.l_bot

@[simp] lemma closure_univ : closure (set.univ : set R) = ⊤ := @coe_top R _ ▸ closure_eq ⊤

lemma closure_union (s t : set R) : closure (s ∪ t) = closure s ⊔ closure t :=
(non_unital_subring.gi R).gc.l_sup

lemma closure_Union {ι} (s : ι → set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(non_unital_subring.gi R).gc.l_supr

lemma closure_sUnion (s : set (set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
(non_unital_subring.gi R).gc.l_Sup

lemma map_sup (s t : non_unital_subring R) (f : F) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
(@gc_map_comap F R S _ _ _ f).l_sup

lemma map_supr {ι : Sort*} (f : F) (s : ι → non_unital_subring R) :
  (supr s).map f = ⨆ i, (s i).map f :=
(@gc_map_comap F R S _ _ _ f).l_supr

lemma comap_inf (s t : non_unital_subring S) (f : F) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
(@gc_map_comap F R S _ _ _ f).u_inf

lemma comap_infi {ι : Sort*} (f : F) (s : ι → non_unital_subring S) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(@gc_map_comap F R S _ _ _ f).u_infi

@[simp] lemma map_bot (f : R →ₙ+* S) : (⊥ : non_unital_subring R).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma comap_top (f : R →ₙ+* S) : (⊤ : non_unital_subring S).comap f = ⊤ :=
(gc_map_comap f).u_top

/-- Given `non_unital_subring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×̂ t`
as a non_unital_subring of `R × S`. -/
def prod (s : non_unital_subring R) (t : non_unital_subring S) : non_unital_subring (R × S) :=
{ carrier := s ×ˢ t,
  .. s.to_subsemigroup.prod t.to_subsemigroup, .. s.to_add_subgroup.prod t.to_add_subgroup}

@[norm_cast]
lemma coe_prod (s : non_unital_subring R) (t : non_unital_subring S) :
  (s.prod t : set (R × S)) = s ×ˢ t := rfl

lemma mem_prod {s : non_unital_subring R} {t : non_unital_subring S} {p : R × S} :
  p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[mono] lemma prod_mono ⦃s₁ s₂ : non_unital_subring R⦄ (hs : s₁ ≤ s₂)
  ⦃t₁ t₂ : non_unital_subring S⦄ (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
set.prod_mono hs ht

lemma prod_mono_right (s : non_unital_subring R) :
  monotone (λ t : non_unital_subring S, s.prod t) :=
prod_mono (le_refl s)

lemma prod_mono_left (t : non_unital_subring S) :
  monotone (λ s : non_unital_subring R, s.prod t) :=
λ s₁ s₂ hs, prod_mono hs (le_refl t)

lemma prod_top (s : non_unital_subring R) :
  s.prod (⊤ : non_unital_subring S) = s.comap (non_unital_ring_hom.fst R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_fst]

lemma top_prod (s : non_unital_subring S) :
  (⊤ : non_unital_subring R).prod s = s.comap (non_unital_ring_hom.snd R S) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_snd]

@[simp]
lemma top_prod_top : (⊤ : non_unital_subring R).prod (⊤ : non_unital_subring S) = ⊤ :=
(top_prod _).trans $ comap_top _

/-- Product of non_unital_subrings is isomorphic to their product as rings. -/
def prod_equiv (s : non_unital_subring R) (t : non_unital_subring S) : s.prod t ≃+* s × t :=
{ map_mul' := λ x y, rfl, map_add' := λ x y, rfl, .. equiv.set.prod ↑s ↑t }

/-- The underlying set of a non-empty directed Sup of non_unital_subrings is just a union of the
non_unital_subrings. Note that this fails without the directedness assumption (the union of two
non_unital_subrings is typically not a non_unital_subring) -/
lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → non_unital_subring R}
  (hS : directed (≤) S) {x : R} : x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (set_like.le_def.1 $ le_supr S i) hi⟩,
  let U : non_unital_subring R := non_unital_subring.mk' (⋃ i, (S i : set R))
    (⨆ i, (S i).to_subsemigroup) (⨆ i, (S i).to_add_subgroup)
    (subsemigroup.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id))
    (add_subgroup.coe_supr_of_directed $ hS.mono_comp _ (λ _ _, id)),
  suffices : (⨆ i, S i) ≤ U, by simpa using @this x,
  exact supr_le (λ i x hx, set.mem_Union.2 ⟨i, hx⟩),
end

lemma coe_supr_of_directed {ι} [hι : nonempty ι] {S : ι → non_unital_subring R}
  (hS : directed (≤) S) : ((⨆ i, S i : non_unital_subring R) : set R) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

lemma mem_Sup_of_directed_on {S : set (non_unital_subring R)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : R} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]
end

lemma coe_Sup_of_directed_on {S : set (non_unital_subring R)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) : (↑(Sup S) : set R) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

lemma mem_map_equiv {f : R ≃+* S} {K : non_unital_subring R} {x : S} :
  x ∈ K.map (f : R →ₙ+* S) ↔ f.symm x ∈ K :=
@set.mem_image_equiv _ _ ↑K f.to_equiv x

lemma map_equiv_eq_comap_symm (f : R ≃+* S) (K : non_unital_subring R) :
  K.map (f : R →ₙ+* S) = K.comap f.symm :=
set_like.coe_injective (f.to_equiv.image_eq_preimage K)

lemma comap_equiv_eq_map_symm (f : R ≃+* S) (K : non_unital_subring S) :
  K.comap (f : R →ₙ+* S) = K.map f.symm :=
(map_equiv_eq_comap_symm f.symm K).symm

end non_unital_subring

namespace non_unital_ring_hom

variables {F : Type w} {R : Type u} {S : Type v} {T : Type*}
variables [non_unital_ring R] [non_unital_ring S] [non_unital_ring T]
variables [non_unital_ring_hom_class F R S]
variables (g : S →ₙ+* T) (f : R →ₙ+* S)
variables {s : non_unital_subring R}

open non_unital_subring

/-- Restriction of a ring homomorphism to its range interpreted as a non_unital_subsemiring.

This is the bundled version of `set.range_factorization`. -/
def range_restrict (f : R →ₙ+* S) : R →ₙ+* f.range :=
f.cod_restrict f.range $ λ x, ⟨x, rfl⟩

@[simp] lemma coe_range_restrict (f : R →ₙ+* S) (x : R) : (f.range_restrict x : S) = f x := rfl

lemma range_restrict_surjective (f : R →ₙ+* S) : function.surjective f.range_restrict :=
λ ⟨y, hy⟩, let ⟨x, hx⟩ := mem_range.mp hy in ⟨x, subtype.ext hx⟩

lemma range_top_iff_surjective {f : R →ₙ+* S} :
  f.range = (⊤ : non_unital_subring S) ↔ function.surjective f :=
set_like.ext'_iff.trans $ iff.trans (by rw [coe_range, coe_top]) set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
lemma range_top_of_surjective (f : R →ₙ+* S) (hf : function.surjective f) :
  f.range = (⊤ : non_unital_subring S) :=
range_top_iff_surjective.2 hf

/-- The non_unital_subring of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a non_unital_subring of R -/
def eq_locus (f g : R →ₙ+* S) : non_unital_subring R :=
{ carrier := {x | f x = g x}, .. (f : R →ₙ* S).eq_mlocus g, .. (f : R →+ S).eq_locus g }

@[simp] lemma eq_locus_same (f : R →ₙ+* S) : f.eq_locus f = ⊤ :=
set_like.ext $ λ _, eq_self_iff_true _

/-- If two ring homomorphisms are equal on a set, then they are equal on its non_unital_subring closure. -/
lemma eq_on_set_closure {f g : R →ₙ+* S} {s : set R} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_locus g, from closure_le.2 h

lemma eq_of_eq_on_set_top {f g : R →ₙ+* S} (h : set.eq_on f g (⊤ : non_unital_subring R)) :
  f = g :=
ext $ λ x, h trivial

lemma eq_of_eq_on_set_dense {s : set R} (hs : closure s = ⊤) {f g : R →ₙ+* S} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_set_top $ hs ▸ eq_on_set_closure h

lemma closure_preimage_le (f : R →ₙ+* S) (s : set S) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a ring homomorphism of the non_unital_subring generated by a set equals
the non_unital_subring generated by the image of the set. -/
lemma map_closure (f : R →ₙ+* S) (s : set R) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (closure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

end non_unital_ring_hom

namespace non_unital_subring

variables {F : Type w} {R : Type u} {S : Type v} {T : Type*}
variables [non_unital_ring R] [non_unital_ring S] [non_unital_ring T]
variables [non_unital_ring_hom_class F R S]
variables (g : S →ₙ+* T) (f : R →ₙ+* S)
variables {s : non_unital_subring R}

open non_unital_ring_hom

/-- The ring homomorphism associated to an inclusion of non_unital_subrings. -/
def inclusion {S T : non_unital_subring R} (h : S ≤ T) : S →ₙ+* T :=
(non_unital_subring_class.subtype S).cod_restrict _ (λ x, h x.2)

@[simp] lemma range_subtype (s : non_unital_subring R) :
  (non_unital_subring_class.subtype s).range = s :=
set_like.coe_injective $ (coe_srange _).trans subtype.range_coe

@[simp]
lemma range_fst : (fst R S).srange = ⊤ :=
(fst R S).srange_top_of_surjective $ prod.fst_surjective

@[simp]
lemma range_snd : (snd R S).srange = ⊤ :=
(snd R S).srange_top_of_surjective $ prod.snd_surjective

end non_unital_subring

namespace ring_equiv

variables {F : Type w} {R : Type u} {S : Type v} {T : Type*}
variables [non_unital_ring R] [non_unital_ring S] [non_unital_ring T]
variables [non_unital_ring_hom_class F R S]
variables (g : S →ₙ+* T) (f : R →ₙ+* S)
variables {s t : non_unital_subring R}

/-- Makes the identity isomorphism from a proof two non_unital_subrings of a multiplicative
    monoid are equal. -/
def non_unital_subring_congr (h : s = t) : s ≃+* t :=
{ map_mul' :=  λ _ _, rfl, map_add' := λ _ _, rfl, ..equiv.set_congr $ congr_arg _ h }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`ring_hom.range`. -/
def of_left_inverse {g : S → R} {f : R →ₙ+* S} (h : function.left_inverse g f) :
  R ≃+* f.range :=
{ to_fun := λ x, f.range_restrict x,
  inv_fun := λ x, (g ∘ (non_unital_subring_class.subtype f.range)) x,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := non_unital_ring_hom.mem_range.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  ..f.range_restrict }

@[simp] lemma of_left_inverse_apply
  {g : S → R} {f : R →ₙ+* S} (h : function.left_inverse g f) (x : R) :
  ↑(of_left_inverse h x) = f x := rfl

@[simp] lemma of_left_inverse_symm_apply
  {g : S → R} {f : R →ₙ+* S} (h : function.left_inverse g f) (x : f.range) :
  (of_left_inverse h).symm x = g x := rfl

/-
/-- Given an equivalence `e : R ≃+* S` of rings and a non_unital_subring `s` of `R`,
`non_unital_subring_equiv_map e s` is the induced equivalence between `s` and `s.map e` -/
@[simps] def non_unital_subring_map (e : R ≃+* S) :
  s ≃+* s.map e.to_ring_hom :=
e.non_unital_subsemiring_map s.to_non_unital_subsemiring
-/

end ring_equiv

namespace non_unital_subring

variables {F : Type w} {R : Type u} {S : Type v}
variables [non_unital_ring R] [non_unital_ring S]
variables [non_unital_ring_hom_class F R S]

lemma closure_preimage_le (f : F) (s : set S) :
  closure ((f : R → S) ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, set_like.mem_coe.2 $ mem_comap.2 $ subset_closure hx

end non_unital_subring

end hom
