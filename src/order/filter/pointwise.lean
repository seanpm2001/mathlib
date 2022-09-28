/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yaël Dillies
-/
import data.set.pointwise
import order.filter.n_ary
import order.filter.ultrafilter

/-!
# Pointwise operations on filters

This file defines pointwise operations on filters. This is useful because usual algebraic operations
distribute over pointwise operations. For example,
* `(f₁ * f₂).map m  = f₁.map m * f₂.map m`
* `𝓝 (x * y) = 𝓝 x * 𝓝 y`

## Main declarations

* `0` (`filter.has_zero`): Pure filter at `0 : α`, or alternatively principal filter at `0 : set α`.
* `1` (`filter.has_one`): Pure filter at `1 : α`, or alternatively principal filter at `1 : set α`.
* `f + g` (`filter.has_add`): Addition, filter generated by all `s + t` where `s ∈ f` and `t ∈ g`.
* `f * g` (`filter.has_mul`): Multiplication, filter generated by all `s * t` where `s ∈ f` and
  `t ∈ g`.
* `-f` (`filter.has_neg`): Negation, filter of all `-s` where `s ∈ f`.
* `f⁻¹` (`filter.has_inv`): Inversion, filter of all `s⁻¹` where `s ∈ f`.
* `f - g` (`filter.has_sub`): Subtraction, filter generated by all `s - t` where `s ∈ f` and
  `t ∈ g`.
* `f / g` (`filter.has_div`): Division, filter generated by all `s / t` where `s ∈ f` and `t ∈ g`.
* `f +ᵥ g` (`filter.has_vadd`): Scalar addition, filter generated by all `s +ᵥ t` where `s ∈ f` and
  `t ∈ g`.
* `f -ᵥ g` (`filter.has_vsub`): Scalar subtraction, filter generated by all `s -ᵥ t` where `s ∈ f`
  and `t ∈ g`.
* `f • g` (`filter.has_smul`): Scalar multiplication, filter generated by all `s • t` where
  `s ∈ f` and `t ∈ g`.
* `a +ᵥ f` (`filter.has_vadd_filter`): Translation, filter of all `a +ᵥ s` where `s ∈ f`.
* `a • f` (`filter.has_smul_filter`): Scaling, filter of all `a • s` where `s ∈ f`.

For `α` a semigroup/monoid, `filter α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • f`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition. See note [pointwise nat action].

## Implementation notes

We put all instances in the locale `pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the locale to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`.

## Tags

filter multiplication, filter addition, pointwise addition, pointwise multiplication,
-/

open function set
open_locale filter pointwise

variables {F α β γ δ ε : Type*}

namespace filter

/-! ### `0`/`1` as filters -/

section has_one
variables [has_one α] {f : filter α} {s : set α}

/-- `1 : filter α` is defined as the filter of sets containing `1 : α` in locale `pointwise`. -/
@[to_additive "`0 : filter α` is defined as the filter of sets containing `0 : α` in locale
`pointwise`."]
protected def has_one : has_one (filter α) := ⟨pure 1⟩

localized "attribute [instance] filter.has_one filter.has_zero" in pointwise

@[simp, to_additive] lemma mem_one : s ∈ (1 : filter α) ↔ (1 : α) ∈ s := mem_pure
@[to_additive] lemma one_mem_one : (1 : set α) ∈ (1 : filter α) := mem_pure.2 one_mem_one
@[simp, to_additive] lemma pure_one : pure 1 = (1 : filter α) := rfl
@[simp, to_additive] lemma principal_one : 𝓟 1 = (1 : filter α) := principal_singleton _
@[to_additive] lemma one_ne_bot : (1 : filter α).ne_bot := filter.pure_ne_bot
@[simp, to_additive] protected lemma map_one' (f : α → β) : (1 : filter α).map f = pure (f 1) := rfl
@[simp, to_additive] lemma le_one_iff : f ≤ 1 ↔ (1 : set α) ∈ f := le_pure_iff
@[to_additive] protected lemma ne_bot.le_one_iff (h : f.ne_bot) : f ≤ 1 ↔ f = 1 := h.le_pure_iff
@[simp, to_additive] lemma eventually_one {p : α → Prop} : (∀ᶠ x in 1, p x) ↔ p 1 := eventually_pure
@[simp, to_additive] lemma tendsto_one {a : filter β} {f : β → α} :
   tendsto f a 1 ↔ ∀ᶠ x in a, f x = 1 :=
tendsto_pure

/-- `pure` as a `one_hom`. -/
@[to_additive "`pure` as a `zero_hom`."]
def pure_one_hom : one_hom α (filter α) := ⟨pure, pure_one⟩

@[simp, to_additive] lemma coe_pure_one_hom : (pure_one_hom : α → filter α) = pure := rfl
@[simp, to_additive] lemma pure_one_hom_apply (a : α) : pure_one_hom a = pure a := rfl

variables [has_one β]

@[simp, to_additive]
protected lemma map_one [one_hom_class F α β] (φ : F) : map φ 1 = 1 :=
by rw [filter.map_one', map_one, pure_one]

end has_one

/-! ### Filter negation/inversion -/

section has_inv
variables [has_inv α] {f g : filter α} {s : set α} {a : α}

/-- The inverse of a filter is the pointwise preimage under `⁻¹` of its sets. -/
@[to_additive "The negation of a filter is the pointwise preimage under `-` of its sets."]
instance : has_inv (filter α) := ⟨map has_inv.inv⟩

@[simp, to_additive] protected lemma map_inv : f.map has_inv.inv = f⁻¹ := rfl
@[to_additive] lemma mem_inv : s ∈ f⁻¹ ↔ has_inv.inv ⁻¹' s ∈ f := iff.rfl
@[to_additive] protected lemma inv_le_inv (hf : f ≤ g) : f⁻¹ ≤ g⁻¹ := map_mono hf
@[simp, to_additive] lemma inv_pure : (pure a : filter α)⁻¹ = pure a⁻¹ := rfl
@[simp, to_additive] lemma inv_eq_bot_iff : f⁻¹ = ⊥ ↔ f = ⊥  := map_eq_bot_iff
@[simp, to_additive] lemma ne_bot_inv_iff : f⁻¹.ne_bot ↔ ne_bot f := map_ne_bot_iff _
@[to_additive] lemma ne_bot.inv : f.ne_bot → f⁻¹.ne_bot := λ h, h.map _

end has_inv

section has_involutive_inv
variables [has_involutive_inv α] {f : filter α} {s : set α}

@[to_additive] lemma inv_mem_inv (hs : s ∈ f) : s⁻¹ ∈ f⁻¹ := by rwa [mem_inv, inv_preimage, inv_inv]

/-- Inversion is involutive on `filter α` if it is on `α`. -/
@[to_additive "Negation is involutive on `filter α` if it is on `α`."]
protected def has_involutive_inv : has_involutive_inv (filter α) :=
{ inv_inv := λ f, map_map.trans $ by rw [inv_involutive.comp_self, map_id],
  ..filter.has_inv }

end has_involutive_inv

/-! ### Filter addition/multiplication -/

section has_mul
variables [has_mul α] [has_mul β] {f f₁ f₂ g g₁ g₂ h : filter α} {s t : set α} {a b : α}

/-- The filter `f * g` is generated by `{s * t | s ∈ f, t ∈ g}` in locale `pointwise`. -/
@[to_additive "The filter `f + g` is generated by `{s + t | s ∈ f, t ∈ g}` in locale `pointwise`."]
protected def has_mul : has_mul (filter α) :=
/- This is defeq to `map₂ (*) f g`, but the hypothesis unfolds to `t₁ * t₂ ⊆ s` rather than all the
way to `set.image2 (*) t₁ t₂ ⊆ s`. -/
⟨λ f g, { sets := {s | ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ * t₂ ⊆ s}, ..map₂ (*) f g }⟩

localized "attribute [instance] filter.has_mul filter.has_add" in pointwise

@[simp, to_additive] lemma map₂_mul : map₂ (*) f g = f * g := rfl
@[to_additive] lemma mem_mul : s ∈ f * g ↔ ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ * t₂ ⊆ s := iff.rfl
@[to_additive] lemma mul_mem_mul : s ∈ f → t ∈ g → s * t ∈ f * g := image2_mem_map₂
@[simp, to_additive] lemma bot_mul : ⊥ * g = ⊥ := map₂_bot_left
@[simp, to_additive] lemma mul_bot : f * ⊥ = ⊥ := map₂_bot_right
@[simp, to_additive] lemma mul_eq_bot_iff : f * g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := map₂_eq_bot_iff
@[simp, to_additive] lemma mul_ne_bot_iff : (f * g).ne_bot ↔ f.ne_bot ∧ g.ne_bot := map₂_ne_bot_iff
@[to_additive] lemma ne_bot.mul : ne_bot f → ne_bot g → ne_bot (f * g) := ne_bot.map₂
@[to_additive] lemma ne_bot.of_mul_left : (f * g).ne_bot → f.ne_bot := ne_bot.of_map₂_left
@[to_additive] lemma ne_bot.of_mul_right : (f * g).ne_bot → g.ne_bot := ne_bot.of_map₂_right
@[simp, to_additive] lemma pure_mul : pure a * g = g.map ((*) a)  := map₂_pure_left
@[simp, to_additive] lemma mul_pure : f * pure b = f.map (* b)  := map₂_pure_right
@[simp, to_additive] lemma pure_mul_pure : (pure a : filter α) * pure b = pure (a * b) := map₂_pure
@[simp, to_additive] lemma le_mul_iff : h ≤ f * g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s * t ∈ h :=
le_map₂_iff

@[to_additive] instance covariant_mul : covariant_class (filter α) (filter α) (*) (≤) :=
⟨λ f g h, map₂_mono_left⟩

@[to_additive] instance covariant_swap_mul : covariant_class (filter α) (filter α) (swap (*)) (≤) :=
⟨λ f g h, map₂_mono_right⟩

@[to_additive]
protected lemma map_mul [mul_hom_class F α β] (m : F) : (f₁ * f₂).map m = f₁.map m * f₂.map m :=
map_map₂_distrib $ map_mul m

/-- `pure` operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def pure_mul_hom : α →ₙ* filter α := ⟨pure, λ a b, pure_mul_pure.symm⟩

@[simp, to_additive] lemma coe_pure_mul_hom : (pure_mul_hom : α → filter α) = pure := rfl
@[simp, to_additive] lemma pure_mul_hom_apply (a : α) : pure_mul_hom a = pure a := rfl

end has_mul

/-! ### Filter subtraction/division -/

section div
variables [has_div α] {f f₁ f₂ g g₁ g₂ h : filter α} {s t : set α} {a b : α}

/-- The filter `f / g` is generated by `{s / t | s ∈ f, t ∈ g}` in locale `pointwise`. -/
@[to_additive "The filter `f - g` is generated by `{s - t | s ∈ f, t ∈ g}` in locale `pointwise`."]
protected def has_div : has_div (filter α) :=
/- This is defeq to `map₂ (/) f g`, but the hypothesis unfolds to `t₁ / t₂ ⊆ s` rather than all the
way to `set.image2 (/) t₁ t₂ ⊆ s`. -/
⟨λ f g, { sets := {s | ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ / t₂ ⊆ s}, ..map₂ (/) f g }⟩

localized "attribute [instance] filter.has_div filter.has_sub" in pointwise

@[simp, to_additive] lemma map₂_div : map₂ (/) f g = f / g := rfl
@[to_additive] lemma mem_div : s ∈ f / g ↔ ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ / t₂ ⊆ s := iff.rfl
@[to_additive] lemma div_mem_div : s ∈ f → t ∈ g → s / t ∈ f / g := image2_mem_map₂
@[simp, to_additive] lemma bot_div : ⊥ / g = ⊥ := map₂_bot_left
@[simp, to_additive] lemma div_bot : f / ⊥ = ⊥ := map₂_bot_right
@[simp, to_additive] lemma div_eq_bot_iff : f / g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := map₂_eq_bot_iff
@[simp, to_additive] lemma div_ne_bot_iff : (f / g).ne_bot ↔ f.ne_bot ∧ g.ne_bot := map₂_ne_bot_iff
@[to_additive] lemma ne_bot.div : ne_bot f → ne_bot g → ne_bot (f / g) := ne_bot.map₂
@[to_additive] lemma ne_bot.of_div_left : (f / g).ne_bot → f.ne_bot := ne_bot.of_map₂_left
@[to_additive] lemma ne_bot.of_div_right : (f / g).ne_bot → g.ne_bot := ne_bot.of_map₂_right
@[simp, to_additive] lemma pure_div : pure a / g = g.map ((/) a)  := map₂_pure_left
@[simp, to_additive] lemma div_pure : f / pure b = f.map (/ b)  := map₂_pure_right
@[simp, to_additive] lemma pure_div_pure : (pure a : filter α) / pure b = pure (a / b) := map₂_pure
@[to_additive] protected lemma div_le_div : f₁ ≤ f₂ → g₁ ≤ g₂ → f₁ / g₁ ≤ f₂ / g₂ := map₂_mono
@[to_additive] protected lemma div_le_div_left : g₁ ≤ g₂ → f / g₁ ≤ f / g₂ := map₂_mono_left
@[to_additive] protected lemma div_le_div_right : f₁ ≤ f₂ → f₁ / g ≤ f₂ / g := map₂_mono_right
@[simp, to_additive] protected lemma le_div_iff :
  h ≤ f / g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s / t ∈ h :=
le_map₂_iff

@[to_additive] instance covariant_div : covariant_class (filter α) (filter α) (/) (≤) :=
⟨λ f g h, map₂_mono_left⟩

@[to_additive] instance covariant_swap_div : covariant_class (filter α) (filter α) (swap (/)) (≤) :=
⟨λ f g h, map₂_mono_right⟩

end div

open_locale pointwise

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `filter`. See
Note [pointwise nat action].-/
protected def has_nsmul [has_zero α] [has_add α] : has_smul ℕ (filter α) := ⟨nsmul_rec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`filter`. See Note [pointwise nat action]. -/
@[to_additive]
protected def has_npow [has_one α] [has_mul α] : has_pow (filter α) ℕ := ⟨λ s n, npow_rec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `filter`. See Note [pointwise nat action]. -/
protected def has_zsmul [has_zero α] [has_add α] [has_neg α] : has_smul ℤ (filter α) :=
⟨zsmul_rec⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `filter`. See Note [pointwise nat action]. -/
@[to_additive] protected def has_zpow [has_one α] [has_mul α] [has_inv α] : has_pow (filter α) ℤ :=
⟨λ s n, zpow_rec n s⟩

localized "attribute [instance] filter.has_nsmul filter.has_npow filter.has_zsmul filter.has_zpow"
  in pointwise

/-- `filter α` is a `semigroup` under pointwise operations if `α` is.-/
@[to_additive "`filter α` is an `add_semigroup` under pointwise operations if `α` is."]
protected def semigroup [semigroup α] : semigroup (filter α) :=
{ mul := (*),
  mul_assoc := λ f g h, map₂_assoc mul_assoc }

/-- `filter α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`filter α` is an `add_comm_semigroup` under pointwise operations if `α` is."]
protected def comm_semigroup [comm_semigroup α] : comm_semigroup (filter α) :=
{ mul_comm := λ f g, map₂_comm mul_comm,
  ..filter.semigroup }

section mul_one_class
variables [mul_one_class α] [mul_one_class β]

/-- `filter α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`filter α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mul_one_class : mul_one_class (filter α) :=
{ one := 1,
  mul := (*),
  one_mul := λ f, by simp only [←pure_one, ←map₂_mul, map₂_pure_left, one_mul, map_id'],
  mul_one := λ f, by simp only [←pure_one, ←map₂_mul, map₂_pure_right, mul_one, map_id'] }

localized "attribute [instance] filter.semigroup filter.add_semigroup filter.comm_semigroup
  filter.add_comm_semigroup filter.mul_one_class filter.add_zero_class" in pointwise

/-- If `φ : α →* β` then `map_monoid_hom φ` is the monoid homomorphism
`filter α →* filter β` induced by `map φ`. -/
@[to_additive "If `φ : α →+ β` then `map_add_monoid_hom φ` is the monoid homomorphism
`filter α →+ filter β` induced by `map φ`."]
def map_monoid_hom [monoid_hom_class F α β] (φ : F) : filter α →* filter β :=
{ to_fun := map φ,
  map_one' := filter.map_one φ,
  map_mul' := λ _ _, filter.map_mul φ }

-- The other direction does not hold in general
@[to_additive]
lemma comap_mul_comap_le [mul_hom_class F α β] (m : F) {f g : filter β} :
  f.comap m * g.comap m ≤ (f * g).comap m  :=
λ s ⟨t, ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩, mt⟩,
  ⟨m ⁻¹' t₁, m ⁻¹' t₂, ⟨t₁, ht₁, subset.rfl⟩, ⟨t₂, ht₂, subset.rfl⟩,
    (preimage_mul_preimage_subset _).trans $ (preimage_mono t₁t₂).trans mt⟩

@[to_additive]
lemma tendsto.mul_mul [mul_hom_class F α β] (m : F) {f₁ g₁ : filter α} {f₂ g₂ : filter β} :
  tendsto m f₁ f₂ → tendsto m g₁ g₂ → tendsto m (f₁ * g₁) (f₂ * g₂) :=
λ hf hg, (filter.map_mul m).trans_le $ mul_le_mul' hf hg

/-- `pure` as a `monoid_hom`. -/
@[to_additive "`pure` as an `add_monoid_hom`."]
def pure_monoid_hom : α →* filter α := { ..pure_mul_hom, ..pure_one_hom }

@[simp, to_additive] lemma coe_pure_monoid_hom : (pure_monoid_hom : α → filter α) = pure := rfl
@[simp, to_additive] lemma pure_monoid_hom_apply (a : α) : pure_monoid_hom a = pure a := rfl

end mul_one_class

section monoid
variables [monoid α] {f g : filter α} {s : set α} {a : α} {m n : ℕ}

/-- `filter α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`filter α` is an `add_monoid` under pointwise operations if `α` is."]
protected def monoid : monoid (filter α) :=
{ ..filter.mul_one_class, ..filter.semigroup, ..filter.has_npow }

localized "attribute [instance] filter.monoid filter.add_monoid" in pointwise

@[to_additive] lemma pow_mem_pow (hs : s ∈ f) : ∀ n : ℕ, s ^ n ∈ f ^ n
| 0 := by { rw pow_zero, exact one_mem_one }
| (n + 1) := by { rw pow_succ, exact mul_mem_mul hs (pow_mem_pow _) }

@[simp, to_additive nsmul_bot] lemma bot_pow {n : ℕ} (hn : n ≠ 0) : (⊥  : filter α) ^ n = ⊥ :=
by rw [←tsub_add_cancel_of_le (nat.succ_le_of_lt $ nat.pos_of_ne_zero hn), pow_succ, bot_mul]

@[to_additive] lemma mul_top_of_one_le (hf : 1 ≤ f) : f * ⊤ = ⊤ :=
begin
  refine top_le_iff.1 (λ s, _),
  simp only [mem_mul, mem_top, exists_and_distrib_left, exists_eq_left],
  rintro ⟨t, ht, hs⟩,
  rwa [mul_univ_of_one_mem (mem_one.1 $ hf ht), univ_subset_iff] at hs,
end

@[to_additive] lemma top_mul_of_one_le (hf : 1 ≤ f) : ⊤ * f = ⊤ :=
begin
  refine top_le_iff.1 (λ s, _),
  simp only [mem_mul, mem_top, exists_and_distrib_left, exists_eq_left],
  rintro ⟨t, ht, hs⟩,
  rwa [univ_mul_of_one_mem (mem_one.1 $ hf ht), univ_subset_iff] at hs,
end

@[simp, to_additive] lemma top_mul_top : (⊤ : filter α) * ⊤ = ⊤ := mul_top_of_one_le le_top

--TODO: `to_additive` trips up on the `1 : ℕ` used in the pattern-matching.
lemma nsmul_top {α : Type*} [add_monoid α] : ∀ {n : ℕ}, n ≠ 0 → n • (⊤ : filter α) = ⊤
| 0 := λ h, (h rfl).elim
| 1 := λ _, one_nsmul _
| (n + 2) := λ _, by { rw [succ_nsmul, nsmul_top n.succ_ne_zero, top_add_top] }

@[to_additive nsmul_top] lemma top_pow : ∀ {n : ℕ}, n ≠ 0 → (⊤ : filter α) ^ n = ⊤
| 0 := λ h, (h rfl).elim
| 1 := λ _, pow_one _
| (n + 2) := λ _, by { rw [pow_succ, top_pow n.succ_ne_zero, top_mul_top] }

@[to_additive] protected lemma _root_.is_unit.filter : is_unit a → is_unit (pure a : filter α) :=
is_unit.map (pure_monoid_hom : α →* filter α)

end monoid

/-- `filter α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`filter α` is an `add_comm_monoid` under pointwise operations if `α` is."]
protected def comm_monoid [comm_monoid α] : comm_monoid (filter α) :=
{ ..filter.mul_one_class, ..filter.comm_semigroup }

open_locale pointwise

section division_monoid
variables [division_monoid α] {f g : filter α}

@[to_additive]
protected lemma mul_eq_one_iff : f * g = 1 ↔ ∃ a b, f = pure a ∧ g = pure b ∧ a * b = 1 :=
begin
  refine ⟨λ hfg, _, _⟩,
  { obtain ⟨t₁, t₂, h₁, h₂, h⟩ : (1 : set α) ∈ f * g := hfg.symm.subst one_mem_one,
    have hfg : (f * g).ne_bot := hfg.symm.subst one_ne_bot,
    rw [(hfg.nonempty_of_mem $ mul_mem_mul h₁ h₂).subset_one_iff, set.mul_eq_one_iff] at h,
    obtain ⟨a, b, rfl, rfl, h⟩ := h,
    refine ⟨a, b, _, _, h⟩,
    { rwa [←hfg.of_mul_left.le_pure_iff, le_pure_iff] },
    { rwa [←hfg.of_mul_right.le_pure_iff, le_pure_iff] } },
  { rintro ⟨a, b, rfl, rfl, h⟩,
    rw [pure_mul_pure, h, pure_one] }
end

/-- `filter α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive subtraction_monoid "`filter α` is a subtraction monoid under pointwise
operations if `α` is."]
protected def division_monoid : division_monoid (filter α) :=
{ mul_inv_rev := λ s t, map_map₂_antidistrib mul_inv_rev,
  inv_eq_of_mul := λ s t h, begin
    obtain ⟨a, b, rfl, rfl, hab⟩ := filter.mul_eq_one_iff.1 h,
    rw [inv_pure, inv_eq_of_mul_eq_one_right hab],
  end,
  div_eq_mul_inv := λ f g, map_map₂_distrib_right div_eq_mul_inv,
  ..filter.monoid, ..filter.has_involutive_inv, ..filter.has_div, ..filter.has_zpow }

@[to_additive] lemma is_unit_iff : is_unit f ↔ ∃ a, f = pure a ∧ is_unit a :=
begin
  split,
  { rintro ⟨u, rfl⟩,
    obtain ⟨a, b, ha, hb, h⟩ := filter.mul_eq_one_iff.1 u.mul_inv,
    refine ⟨a, ha, ⟨a, b, h, pure_injective _⟩, rfl⟩,
    rw [←pure_mul_pure, ←ha, ←hb],
    exact u.inv_mul },
  { rintro ⟨a, rfl, ha⟩,
    exact ha.filter }
end

end division_monoid

/-- `filter α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtraction_comm_monoid "`filter α` is a commutative subtraction monoid under
pointwise operations if `α` is."]
protected def division_comm_monoid [division_comm_monoid α] : division_comm_monoid (filter α) :=
{ ..filter.division_monoid, ..filter.comm_semigroup }

/-- `filter α` has distributive negation if `α` has. -/
protected def has_distrib_neg [has_mul α] [has_distrib_neg α] : has_distrib_neg (filter α) :=
{ neg_mul := λ _ _, map₂_map_left_comm neg_mul,
  mul_neg := λ _ _, map_map₂_right_comm mul_neg,
  ..filter.has_involutive_neg }

localized "attribute [instance] filter.comm_monoid filter.add_comm_monoid filter.division_monoid
  filter.subtraction_monoid filter.division_comm_monoid filter.subtraction_comm_monoid
  filter.has_distrib_neg" in pointwise

section distrib
variables [distrib α] {f g h : filter α}

/-!
Note that `filter α` is not a `distrib` because `f * g + f * h` has cross terms that `f * (g + h)`
lacks.
-/

lemma mul_add_subset : f * (g + h) ≤ f * g + f * h := map₂_distrib_le_left mul_add
lemma add_mul_subset : (f + g) * h ≤ f * h + g * h := map₂_distrib_le_right add_mul

end distrib

section mul_zero_class
variables [mul_zero_class α] {f g : filter α}

/-! Note that `filter` is not a `mul_zero_class` because `0 * ⊥ ≠ 0`. -/

lemma ne_bot.mul_zero_nonneg (hf : f.ne_bot) : 0 ≤ f * 0 :=
le_mul_iff.2 $ λ t₁ h₁ t₂ h₂, let ⟨a, ha⟩ := hf.nonempty_of_mem h₁ in ⟨_, _, ha, h₂, mul_zero _⟩

lemma ne_bot.zero_mul_nonneg (hg : g.ne_bot) : 0 ≤ 0 * g :=
le_mul_iff.2 $ λ t₁ h₁ t₂ h₂, let ⟨b, hb⟩ := hg.nonempty_of_mem h₂ in ⟨_, _, h₁, hb, zero_mul _⟩

end mul_zero_class

section group
variables [group α] [division_monoid β] [monoid_hom_class F α β] (m : F) {f g f₁ g₁ : filter α}
  {f₂ g₂ : filter β}

/-! Note that `filter α` is not a group because `f / f ≠ 1` in general -/

@[simp, to_additive] protected lemma one_le_div_iff : 1 ≤ f / g ↔ ¬ disjoint f g :=
begin
  refine ⟨λ h hfg, _, _⟩,
  { obtain ⟨s, hs, t, ht, hst⟩ := hfg (mem_bot : ∅ ∈ ⊥),
    exact set.one_mem_div_iff.1 (h $ div_mem_div hs ht) (disjoint_iff.2 hst.symm) },
  { rintro h s ⟨t₁, t₂, h₁, h₂, hs⟩,
    exact hs (set.one_mem_div_iff.2 $ λ ht, h $ disjoint_of_disjoint_of_mem ht h₁ h₂) }
end

@[to_additive] lemma not_one_le_div_iff : ¬ 1 ≤ f / g ↔ disjoint f g :=
filter.one_le_div_iff.not_left

@[to_additive] lemma ne_bot.one_le_div (h : f.ne_bot) : 1 ≤ f / f :=
begin
  rintro s ⟨t₁, t₂, h₁, h₂, hs⟩,
  obtain ⟨a, ha₁, ha₂⟩ := set.not_disjoint_iff.1 (h.not_disjoint h₁ h₂),
  rw [mem_one, ←div_self' a],
  exact hs (set.div_mem_div ha₁ ha₂),
end

@[to_additive] lemma is_unit_pure (a : α) : is_unit (pure a : filter α) := (group.is_unit a).filter

@[simp] lemma is_unit_iff_singleton : is_unit f ↔ ∃ a, f = pure a :=
by simp only [is_unit_iff, group.is_unit, and_true]

include β

@[to_additive] lemma map_inv' : f⁻¹.map m = (f.map m)⁻¹ := semiconj.filter_map (map_inv m) f

@[to_additive] lemma tendsto.inv_inv : tendsto m f₁ f₂ → tendsto m f₁⁻¹ f₂⁻¹ :=
λ hf, (filter.map_inv' m).trans_le $ filter.inv_le_inv hf

@[to_additive] protected lemma map_div : (f / g).map m = f.map m / g.map m :=
map_map₂_distrib $ map_div m

@[to_additive]
lemma tendsto.div_div : tendsto m f₁ f₂ → tendsto m g₁ g₂ → tendsto m (f₁ / g₁) (f₂ / g₂) :=
λ hf hg, (filter.map_div m).trans_le $ filter.div_le_div hf hg

end group

open_locale pointwise

section group_with_zero
variables [group_with_zero α] {f g : filter α}

lemma ne_bot.div_zero_nonneg (hf : f.ne_bot) : 0 ≤ f / 0 :=
filter.le_div_iff.2 $ λ t₁ h₁ t₂ h₂, let ⟨a, ha⟩ := hf.nonempty_of_mem h₁ in
  ⟨_, _, ha, h₂, div_zero _⟩

lemma ne_bot.zero_div_nonneg (hg : g.ne_bot) : 0 ≤ 0 / g :=
filter.le_div_iff.2 $ λ t₁ h₁ t₂ h₂, let ⟨b, hb⟩ := hg.nonempty_of_mem h₂ in
  ⟨_, _, h₁, hb, zero_div _⟩

end group_with_zero

/-! ### Scalar addition/multiplication of filters -/

section smul
variables [has_smul α β] {f f₁ f₂ : filter α} {g g₁ g₂ h : filter β} {s : set α} {t : set β}
  {a : α} {b : β}

/-- The filter `f • g` is generated by `{s • t | s ∈ f, t ∈ g}` in locale `pointwise`. -/
@[to_additive filter.has_vadd
"The filter `f +ᵥ g` is generated by `{s +ᵥ t | s ∈ f, t ∈ g}` in locale `pointwise`."]
protected def has_smul : has_smul (filter α) (filter β) :=
/- This is defeq to `map₂ (•) f g`, but the hypothesis unfolds to `t₁ • t₂ ⊆ s` rather than all the
way to `set.image2 (•) t₁ t₂ ⊆ s`. -/
⟨λ f g, { sets := {s | ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ • t₂ ⊆ s}, ..map₂ (•) f g }⟩

localized "attribute [instance] filter.has_smul filter.has_vadd" in pointwise

@[simp, to_additive] lemma map₂_smul : map₂ (•) f g = f • g := rfl
@[to_additive] lemma mem_smul : t ∈ f • g ↔ ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ • t₂ ⊆ t := iff.rfl
@[to_additive] lemma smul_mem_smul : s ∈ f → t ∈ g → s • t ∈ f • g :=  image2_mem_map₂
@[simp, to_additive] lemma bot_smul : (⊥ : filter α) • g = ⊥ := map₂_bot_left
@[simp, to_additive] lemma smul_bot : f • (⊥ : filter β) = ⊥ := map₂_bot_right
@[simp, to_additive] lemma smul_eq_bot_iff : f • g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := map₂_eq_bot_iff
@[simp, to_additive] lemma smul_ne_bot_iff : (f • g).ne_bot ↔ f.ne_bot ∧ g.ne_bot := map₂_ne_bot_iff
@[to_additive] lemma ne_bot.smul : ne_bot f → ne_bot g → ne_bot (f • g) := ne_bot.map₂
@[to_additive] lemma ne_bot.of_smul_left : (f • g).ne_bot → f.ne_bot := ne_bot.of_map₂_left
@[to_additive] lemma ne_bot.of_smul_right : (f • g).ne_bot → g.ne_bot := ne_bot.of_map₂_right
@[simp, to_additive] lemma pure_smul : (pure a : filter α) • g = g.map ((•) a)  := map₂_pure_left
@[simp, to_additive] lemma smul_pure : f • pure b = f.map (• b)  := map₂_pure_right
@[simp, to_additive] lemma pure_smul_pure :
  (pure a : filter α) • (pure b : filter β) = pure (a • b) := map₂_pure
@[to_additive] lemma smul_le_smul : f₁ ≤ f₂ → g₁ ≤ g₂ → f₁ • g₁ ≤ f₂ • g₂ := map₂_mono
@[to_additive] lemma smul_le_smul_left : g₁ ≤ g₂ → f • g₁ ≤ f • g₂ := map₂_mono_left
@[to_additive] lemma smul_le_smul_right : f₁ ≤ f₂ → f₁ • g ≤ f₂ • g := map₂_mono_right
@[simp, to_additive] lemma le_smul_iff : h ≤ f • g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s • t ∈ h :=
le_map₂_iff

@[to_additive] instance covariant_smul : covariant_class (filter α) (filter β) (•) (≤) :=
⟨λ f g h, map₂_mono_left⟩

end smul

/-! ### Scalar subtraction of filters -/

section vsub
variables [has_vsub α β] {f f₁ f₂ g g₁ g₂ : filter β} {h : filter α} {s t : set β} {a b : β}
include α

/-- The filter `f -ᵥ g` is generated by `{s -ᵥ t | s ∈ f, t ∈ g}` in locale `pointwise`. -/
protected def has_vsub : has_vsub (filter α) (filter β) :=
/- This is defeq to `map₂ (-ᵥ) f g`, but the hypothesis unfolds to `t₁ -ᵥ t₂ ⊆ s` rather than all
the way to `set.image2 (-ᵥ) t₁ t₂ ⊆ s`. -/
⟨λ f g, { sets := {s | ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ -ᵥ t₂ ⊆ s}, ..map₂ (-ᵥ) f g }⟩

localized "attribute [instance] filter.has_vsub" in pointwise

@[simp] lemma map₂_vsub : map₂ (-ᵥ) f g = f -ᵥ g := rfl
lemma mem_vsub {s : set α} : s ∈ f -ᵥ g ↔ ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ -ᵥ t₂ ⊆ s := iff.rfl
lemma vsub_mem_vsub : s ∈ f → t ∈ g → s -ᵥ t ∈ f -ᵥ g :=  image2_mem_map₂
@[simp] lemma bot_vsub : (⊥ : filter β) -ᵥ g = ⊥ := map₂_bot_left
@[simp] lemma vsub_bot : f -ᵥ (⊥ : filter β) = ⊥ := map₂_bot_right
@[simp] lemma vsub_eq_bot_iff : f -ᵥ g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := map₂_eq_bot_iff
@[simp] lemma vsub_ne_bot_iff : (f -ᵥ g : filter α).ne_bot ↔ f.ne_bot ∧ g.ne_bot := map₂_ne_bot_iff
lemma ne_bot.vsub : ne_bot f → ne_bot g → ne_bot (f -ᵥ g) := ne_bot.map₂
lemma ne_bot.of_vsub_left : (f -ᵥ g : filter α).ne_bot → f.ne_bot := ne_bot.of_map₂_left
lemma ne_bot.of_vsub_right : (f -ᵥ g : filter α).ne_bot → g.ne_bot := ne_bot.of_map₂_right
@[simp] lemma pure_vsub : (pure a : filter β) -ᵥ g = g.map ((-ᵥ) a)  := map₂_pure_left
@[simp] lemma vsub_pure : f -ᵥ pure b = f.map (-ᵥ b)  := map₂_pure_right
@[simp] lemma pure_vsub_pure : (pure a : filter β) -ᵥ pure b = (pure (a -ᵥ b) : filter α) :=
map₂_pure
lemma vsub_le_vsub : f₁ ≤ f₂ → g₁ ≤ g₂ → f₁ -ᵥ g₁ ≤ f₂ -ᵥ g₂ := map₂_mono
lemma vsub_le_vsub_left : g₁ ≤ g₂ → f -ᵥ g₁ ≤ f -ᵥ g₂ := map₂_mono_left
lemma vsub_le_vsub_right : f₁ ≤ f₂ → f₁ -ᵥ g ≤ f₂ -ᵥ g := map₂_mono_right
@[simp] lemma le_vsub_iff : h ≤ f -ᵥ g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s -ᵥ t ∈ h := le_map₂_iff

end vsub

/-! ### Translation/scaling of filters -/

section smul
variables [has_smul α β] {f f₁ f₂ : filter β} {s : set β} {a : α}

/-- `a • f` is the map of `f` under `a •` in locale `pointwise`. -/
@[to_additive filter.has_vadd_filter
"`a +ᵥ f` is the map of `f` under `a +ᵥ` in locale `pointwise`."]
protected def has_smul_filter : has_smul α (filter β) := ⟨λ a, map ((•) a)⟩

localized "attribute [instance] filter.has_smul_filter filter.has_vadd_filter" in pointwise

@[simp, to_additive] lemma map_smul : map (λ b, a • b) f = a • f := rfl
@[to_additive] lemma mem_smul_filter : s ∈ a • f ↔ (•) a ⁻¹' s ∈ f := iff.rfl

@[to_additive] lemma smul_set_mem_smul_filter : s ∈ f → a • s ∈ a • f := image_mem_map
@[simp, to_additive] lemma smul_filter_bot : a • (⊥ : filter β) = ⊥ := map_bot
@[simp, to_additive] lemma smul_filter_eq_bot_iff : a • f = ⊥ ↔ f = ⊥ := map_eq_bot_iff
@[simp, to_additive] lemma smul_filter_ne_bot_iff : (a • f).ne_bot ↔ f.ne_bot := map_ne_bot_iff _
@[to_additive] lemma ne_bot.smul_filter : f.ne_bot → (a • f).ne_bot := λ h, h.map _
@[to_additive] lemma ne_bot.of_smul_filter : (a • f).ne_bot → f.ne_bot := ne_bot.of_map
@[to_additive] lemma smul_filter_le_smul_filter (hf : f₁ ≤ f₂) : a • f₁ ≤ a • f₂ :=
map_mono hf

@[to_additive] instance covariant_smul_filter : covariant_class α (filter β) (•) (≤) :=
⟨λ f, map_mono⟩

end smul

open_locale pointwise

@[to_additive]
instance smul_comm_class_filter [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α β (filter γ) :=
⟨λ _ _ _,  map_comm (funext $ smul_comm _ _) _⟩

@[to_additive]
instance smul_comm_class_filter' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α (filter β) (filter γ) :=
⟨λ a f g, map_map₂_distrib_right $ smul_comm a⟩

@[to_additive]
instance smul_comm_class_filter'' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (filter α) β (filter γ) :=
by haveI := smul_comm_class.symm α β γ; exact smul_comm_class.symm _ _ _

@[to_additive]
instance smul_comm_class [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (filter α) (filter β) (filter γ) :=
⟨λ f g h, map₂_left_comm smul_comm⟩

@[to_additive]
instance is_scalar_tower [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α β (filter γ) :=
⟨λ a b f, by simp only [←map_smul, map_map, smul_assoc]⟩

@[to_additive]
instance is_scalar_tower' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α (filter β) (filter γ) :=
⟨λ a f g, by { refine (map_map₂_distrib_left $ λ _ _, _).symm, exact (smul_assoc a _ _).symm }⟩

@[to_additive]
instance is_scalar_tower'' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower (filter α) (filter β) (filter γ) :=
⟨λ f g h, map₂_assoc smul_assoc⟩

instance is_central_scalar [has_smul α β] [has_smul αᵐᵒᵖ β] [is_central_scalar α β] :
  is_central_scalar α (filter β) :=
⟨λ a f, congr_arg (λ m, map m f) $ by exact funext (λ _, op_smul_eq_smul _ _)⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of
`filter α` on `filter β`. -/
@[to_additive "An additive action of an additive monoid `α` on a type `β` gives an additive action
of `filter α` on `filter β`"]
protected def mul_action [monoid α] [mul_action α β] : mul_action (filter α) (filter β) :=
{ one_smul := λ f, map₂_pure_left.trans $ by simp_rw [one_smul, map_id'],
  mul_smul := λ f g h, map₂_assoc mul_smul }

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `filter β`.
-/
@[to_additive "An additive action of an additive monoid on a type `β` gives an additive action on
`filter β`."]
protected def mul_action_filter [monoid α] [mul_action α β] : mul_action α (filter β) :=
{ mul_smul := λ a b f, by simp only [←map_smul, map_map, function.comp, ←mul_smul],
  one_smul := λ f, by simp only [←map_smul, one_smul, map_id'] }

localized "attribute [instance] filter.mul_action filter.add_action filter.mul_action_filter
  filter.add_action_filter" in pointwise

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `filter β`. -/
protected def distrib_mul_action_filter [monoid α] [add_monoid β] [distrib_mul_action α β] :
  distrib_mul_action α (filter β) :=
{ smul_add := λ _ _ _, map_map₂_distrib $ smul_add _,
  smul_zero := λ _, (map_pure _ _).trans $ by rw [smul_zero, pure_zero] }

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mul_distrib_mul_action_filter [monoid α] [monoid β] [mul_distrib_mul_action α β] :
  mul_distrib_mul_action α (set β) :=
{ smul_mul := λ _ _ _, image_image2_distrib $ smul_mul' _,
  smul_one := λ _, image_singleton.trans $ by rw [smul_one, singleton_one] }

localized "attribute [instance] filter.distrib_mul_action_filter
  filter.mul_distrib_mul_action_filter" in pointwise

section smul_with_zero
variables [has_zero α] [has_zero β] [smul_with_zero α β] {f : filter α} {g : filter β}

/-!
Note that we have neither `smul_with_zero α (filter β)` nor `smul_with_zero (filter α) (filter β)`
because `0 * ⊥ ≠ 0`.
-/

lemma ne_bot.smul_zero_nonneg (hf : f.ne_bot) : 0 ≤ f • (0 : filter β) :=
le_smul_iff.2 $ λ t₁ h₁ t₂ h₂, let ⟨a, ha⟩ := hf.nonempty_of_mem h₁ in
  ⟨_, _, ha, h₂, smul_zero _⟩

lemma ne_bot.zero_smul_nonneg (hg : g.ne_bot) : 0 ≤ (0 : filter α) • g :=
le_smul_iff.2 $ λ t₁ h₁ t₂ h₂, let ⟨b, hb⟩ := hg.nonempty_of_mem h₂ in ⟨_, _, h₁, hb, zero_smul _ _⟩

lemma zero_smul_filter_nonpos : (0 : α) • g ≤ 0 :=
begin
  refine λ s hs, mem_smul_filter.2 _,
  convert univ_mem,
  refine eq_univ_iff_forall.2 (λ a, _),
  rwa [mem_preimage, zero_smul],
end

lemma zero_smul_filter (hg : g.ne_bot) : (0 : α) • g = 0 :=
zero_smul_filter_nonpos.antisymm $ le_map_iff.2 $ λ s hs, begin
  simp_rw [set.image_eta, zero_smul, (hg.nonempty_of_mem hs).image_const],
  exact zero_mem_zero,
end

end smul_with_zero

end filter
