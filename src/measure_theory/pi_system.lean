/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Martin Zinkevich, Rémy Degenne
-/
import logic.encodable.lattice
import measure_theory.measurable_space_def

/-!
# Induction principles for measurable sets, related to π-systems and λ-systems.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main statements

* The main theorem of this file is Dynkin's π-λ theorem, which appears
  here as an induction principle `induction_on_inter`. Suppose `s` is a
  collection of subsets of `α` such that the intersection of two members
  of `s` belongs to `s` whenever it is nonempty. Let `m` be the σ-algebra
  generated by `s`. In order to check that a predicate `C` holds on every
  member of `m`, it suffices to check that `C` holds on the members of `s` and
  that `C` is preserved by complementation and *disjoint* countable
  unions.

* The proof of this theorem relies on the notion of `is_pi_system`, i.e., a collection of sets
  which is closed under binary non-empty intersections. Note that this is a small variation around
  the usual notion in the literature, which often requires that a π-system is non-empty, and closed
  also under disjoint intersections. This variation turns out to be convenient for the
  formalization.

* The proof of Dynkin's π-λ theorem also requires the notion of `dynkin_system`, i.e., a collection
  of sets which contains the empty set, is closed under complementation and under countable union
  of pairwise disjoint sets. The disjointness condition is the only difference with `σ`-algebras.

* `generate_pi_system g` gives the minimal π-system containing `g`.
  This can be considered a Galois insertion into both measurable spaces and sets.

* `generate_from_generate_pi_system_eq` proves that if you start from a collection of sets `g`,
  take the generated π-system, and then the generated σ-algebra, you get the same result as
  the σ-algebra generated from `g`. This is useful because there are connections between
  independent sets that are π-systems and the generated independent spaces.

* `mem_generate_pi_system_Union_elim` and `mem_generate_pi_system_Union_elim'` show that any
  element of the π-system generated from the union of a set of π-systems can be
  represented as the intersection of a finite number of elements from these sets.

* `pi_Union_Inter` defines a new π-system from a family of π-systems `π : ι → set (set α)` and a
  set of indices `S : set ι`. `pi_Union_Inter π S` is the set of sets that can be written
  as `⋂ x ∈ t, f x` for some finset `t ∈ S` and sets `f x ∈ π x`.

## Implementation details

* `is_pi_system` is a predicate, not a type. Thus, we don't explicitly define the galois
  insertion, nor do we define a complete lattice. In theory, we could define a complete
  lattice and galois insertion on the subtype corresponding to `is_pi_system`.
-/

open measurable_space set
open_locale classical measure_theory

/-- A π-system is a collection of subsets of `α` that is closed under binary intersection of
  non-disjoint sets. Usually it is also required that the collection is nonempty, but we don't do
  that here. -/
def is_pi_system {α} (C : set (set α)) : Prop :=
∀ s t ∈ C, (s ∩ t : set α).nonempty → s ∩ t ∈ C

namespace measurable_space

lemma is_pi_system_measurable_set {α:Type*} [measurable_space α] :
  is_pi_system {s : set α | measurable_set s} :=
λ s hs t ht _, hs.inter ht

end measurable_space

lemma is_pi_system.singleton {α} (S : set α) : is_pi_system ({S} : set (set α)) :=
begin
  intros s h_s t h_t h_ne,
  rw [set.mem_singleton_iff.1 h_s, set.mem_singleton_iff.1 h_t, set.inter_self,
      set.mem_singleton_iff],
end

lemma is_pi_system.insert_empty {α} {S : set (set α)} (h_pi : is_pi_system S) :
  is_pi_system (insert ∅ S) :=
begin
  intros s hs t ht hst,
  cases hs,
  { simp [hs], },
  { cases ht,
    { simp [ht], },
    { exact set.mem_insert_of_mem _ (h_pi s hs t ht hst), }, },
end

lemma is_pi_system.insert_univ {α} {S : set (set α)} (h_pi : is_pi_system S) :
  is_pi_system (insert set.univ S) :=
begin
  intros s hs t ht hst,
  cases hs,
  { cases ht; simp [hs, ht], },
  { cases ht,
    { simp [hs, ht], },
    { exact set.mem_insert_of_mem _ (h_pi s hs t ht hst), }, },
end

lemma is_pi_system.comap {α β} {S : set (set β)} (h_pi : is_pi_system S) (f : α → β) :
  is_pi_system {s : set α | ∃ t ∈ S, f ⁻¹' t = s} :=
begin
  rintros _ ⟨s, hs_mem, rfl⟩ _ ⟨t, ht_mem, rfl⟩ hst,
  rw ← set.preimage_inter at hst ⊢,
  refine ⟨s ∩ t, h_pi s hs_mem t ht_mem _, rfl⟩,
  by_contra,
  rw set.not_nonempty_iff_eq_empty at h,
  rw h at hst,
  simpa using hst,
end

lemma is_pi_system_Union_of_directed_le {α ι} (p : ι → set (set α))
  (hp_pi : ∀ n, is_pi_system (p n)) (hp_directed : directed (≤) p) :
  is_pi_system (⋃ n, p n) :=
begin
  intros t1 ht1 t2 ht2 h,
  rw set.mem_Union at ht1 ht2 ⊢,
  cases ht1 with n ht1,
  cases ht2 with m ht2,
  obtain ⟨k, hpnk, hpmk⟩ : ∃ k, p n ≤ p k ∧ p m ≤ p k := hp_directed n m,
  exact ⟨k, hp_pi k t1 (hpnk ht1) t2 (hpmk ht2) h⟩,
end

lemma is_pi_system_Union_of_monotone {α ι} [semilattice_sup ι] (p : ι → set (set α))
  (hp_pi : ∀ n, is_pi_system (p n)) (hp_mono : monotone p) :
  is_pi_system (⋃ n, p n) :=
is_pi_system_Union_of_directed_le p hp_pi (monotone.directed_le hp_mono)

section order

variables {α : Type*} {ι ι' : Sort*} [linear_order α]

lemma is_pi_system_image_Iio (s : set α) : is_pi_system (Iio '' s) :=
begin
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -,
  exact ⟨a ⊓ b, inf_ind a b ha hb, Iio_inter_Iio.symm⟩
end

lemma is_pi_system_Iio : is_pi_system (range Iio : set (set α)) :=
@image_univ α _ Iio ▸ is_pi_system_image_Iio univ

lemma is_pi_system_image_Ioi (s : set α) : is_pi_system (Ioi '' s) :=
@is_pi_system_image_Iio αᵒᵈ _ s

lemma is_pi_system_Ioi : is_pi_system (range Ioi : set (set α)) :=
@image_univ α _ Ioi ▸ is_pi_system_image_Ioi univ

lemma is_pi_system_Ixx_mem {Ixx : α → α → set α} {p : α → α → Prop}
  (Hne : ∀ {a b}, (Ixx a b).nonempty → p a b)
  (Hi : ∀ {a₁ b₁ a₂ b₂}, Ixx a₁ b₁ ∩ Ixx a₂ b₂ = Ixx (max a₁ a₂) (min b₁ b₂)) (s t : set α) :
  is_pi_system {S | ∃ (l ∈ s) (u ∈ t) (hlu : p l u), Ixx l u = S} :=
begin
  rintro _ ⟨l₁, hls₁, u₁, hut₁, hlu₁, rfl⟩ _ ⟨l₂, hls₂, u₂, hut₂, hlu₂, rfl⟩,
  simp only [Hi, ← sup_eq_max, ← inf_eq_min],
  exact λ H, ⟨l₁ ⊔ l₂, sup_ind l₁ l₂ hls₁ hls₂, u₁ ⊓ u₂, inf_ind u₁ u₂ hut₁ hut₂, Hne H, rfl⟩
end

lemma is_pi_system_Ixx {Ixx : α → α → set α} {p : α → α → Prop}
  (Hne : ∀ {a b}, (Ixx a b).nonempty → p a b)
  (Hi : ∀ {a₁ b₁ a₂ b₂}, Ixx a₁ b₁ ∩ Ixx a₂ b₂ = Ixx (max a₁ a₂) (min b₁ b₂))
  (f : ι → α) (g : ι' → α) :
  @is_pi_system α ({S | ∃ i j (h : p (f i) (g j)), Ixx (f i) (g j) = S}) :=
by simpa only [exists_range_iff] using is_pi_system_Ixx_mem @Hne @Hi (range f) (range g)

lemma is_pi_system_Ioo_mem (s t : set α) :
  is_pi_system {S | ∃ (l ∈ s) (u ∈ t) (h : l < u), Ioo l u = S} :=
is_pi_system_Ixx_mem (λ a b ⟨x, hax, hxb⟩, hax.trans hxb) (λ _ _ _ _, Ioo_inter_Ioo) s t

lemma is_pi_system_Ioo (f : ι → α) (g : ι' → α) :
  @is_pi_system α {S | ∃ l u (h : f l < g u), Ioo (f l) (g u) = S} :=
is_pi_system_Ixx (λ a b ⟨x, hax, hxb⟩, hax.trans hxb) (λ _ _ _ _, Ioo_inter_Ioo) f g

lemma is_pi_system_Ioc_mem (s t : set α) :
  is_pi_system {S | ∃ (l ∈ s) (u ∈ t) (h : l < u), Ioc l u = S} :=
is_pi_system_Ixx_mem (λ a b ⟨x, hax, hxb⟩, hax.trans_le hxb) (λ _ _ _ _, Ioc_inter_Ioc) s t

lemma is_pi_system_Ioc (f : ι → α) (g : ι' → α) :
  @is_pi_system α {S | ∃ i j (h : f i < g j), Ioc (f i) (g j) = S} :=
is_pi_system_Ixx (λ a b ⟨x, hax, hxb⟩, hax.trans_le hxb) (λ _ _ _ _, Ioc_inter_Ioc) f g

lemma is_pi_system_Ico_mem (s t : set α) :
  is_pi_system {S | ∃ (l ∈ s) (u ∈ t) (h : l < u), Ico l u = S} :=
is_pi_system_Ixx_mem (λ a b ⟨x, hax, hxb⟩, hax.trans_lt hxb) (λ _ _ _ _, Ico_inter_Ico) s t

lemma is_pi_system_Ico (f : ι → α) (g : ι' → α) :
  @is_pi_system α {S | ∃ i j (h : f i < g j), Ico (f i) (g j) = S} :=
is_pi_system_Ixx (λ a b ⟨x, hax, hxb⟩, hax.trans_lt hxb) (λ _ _ _ _, Ico_inter_Ico) f g

lemma is_pi_system_Icc_mem (s t : set α) :
  is_pi_system {S | ∃ (l ∈ s) (u ∈ t) (h : l ≤ u), Icc l u = S} :=
is_pi_system_Ixx_mem (λ a b, nonempty_Icc.1) (λ _ _ _ _, Icc_inter_Icc) s t

lemma is_pi_system_Icc (f : ι → α) (g : ι' → α) :
  @is_pi_system α {S | ∃ i j (h : f i ≤ g j), Icc (f i) (g j) = S} :=
is_pi_system_Ixx (λ a b, nonempty_Icc.1) (λ _ _ _ _, Icc_inter_Icc) f g

end order

/-- Given a collection `S` of subsets of `α`, then `generate_pi_system S` is the smallest
π-system containing `S`. -/
inductive generate_pi_system {α} (S : set (set α)) : set (set α)
| base {s : set α} (h_s : s ∈ S) : generate_pi_system s
| inter {s t : set α} (h_s : generate_pi_system s) (h_t : generate_pi_system t)
  (h_nonempty : (s ∩ t).nonempty) : generate_pi_system (s ∩ t)

lemma is_pi_system_generate_pi_system {α} (S : set (set α)) :
  is_pi_system (generate_pi_system S) :=
λ s h_s t h_t h_nonempty, generate_pi_system.inter h_s h_t h_nonempty

lemma subset_generate_pi_system_self {α} (S : set (set α)) : S ⊆ generate_pi_system S :=
λ s, generate_pi_system.base

lemma generate_pi_system_subset_self {α} {S : set (set α)} (h_S : is_pi_system S) :
  generate_pi_system S ⊆ S :=
begin
  intros x h,
  induction h with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  { exact h_s, },
  { exact h_S _ h_s _ h_u h_nonempty, },
end

lemma generate_pi_system_eq {α} {S : set (set α)} (h_pi : is_pi_system S) :
  generate_pi_system S = S :=
set.subset.antisymm (generate_pi_system_subset_self h_pi) (subset_generate_pi_system_self S)

lemma generate_pi_system_mono {α} {S T : set (set α)} (hST : S ⊆ T) :
  generate_pi_system S ⊆ generate_pi_system T :=
begin
  intros t ht,
  induction ht with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  { exact generate_pi_system.base (set.mem_of_subset_of_mem hST h_s),},
  { exact is_pi_system_generate_pi_system T _ h_s _ h_u h_nonempty, },
end

lemma generate_pi_system_measurable_set {α} [M : measurable_space α] {S : set (set α)}
  (h_meas_S : ∀ s ∈ S, measurable_set s) (t : set α)
  (h_in_pi : t ∈ generate_pi_system S) : measurable_set t :=
begin
  induction h_in_pi with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  { apply h_meas_S _ h_s, },
  { apply measurable_set.inter h_s h_u, },
end

lemma generate_from_measurable_set_of_generate_pi_system {α} {g : set (set α)} (t : set α)
  (ht : t ∈ generate_pi_system g) :
  measurable_set[generate_from g] t :=
@generate_pi_system_measurable_set α (generate_from g) g
  (λ s h_s_in_g, measurable_set_generate_from h_s_in_g) t ht

lemma generate_from_generate_pi_system_eq {α} {g : set (set α)} :
  generate_from (generate_pi_system g) = generate_from g :=
begin
  apply le_antisymm; apply generate_from_le,
  { exact λ t h_t, generate_from_measurable_set_of_generate_pi_system t h_t, },
  { exact λ t h_t, measurable_set_generate_from (generate_pi_system.base h_t), },
end

/- Every element of the π-system generated by the union of a family of π-systems
is a finite intersection of elements from the π-systems.
For an indexed union version, see `mem_generate_pi_system_Union_elim'`. -/
lemma mem_generate_pi_system_Union_elim {α β} {g : β → set (set α)}
  (h_pi : ∀ b, is_pi_system (g b)) (t : set α) (h_t : t ∈ generate_pi_system (⋃ b, g b)) :
  ∃ (T : finset β) (f : β → set α), (t = ⋂ b ∈ T, f b) ∧ (∀ b ∈ T, f b ∈ g b) :=
begin
  induction h_t with s h_s s t' h_gen_s h_gen_t' h_nonempty h_s h_t',
  { rcases h_s with ⟨t', ⟨⟨b, rfl⟩, h_s_in_t'⟩⟩,
    refine ⟨{b}, (λ _, s), _⟩,
    simpa using h_s_in_t', },
  { rcases h_t' with ⟨T_t', ⟨f_t', ⟨rfl, h_t'⟩⟩⟩,
    rcases h_s with ⟨T_s, ⟨f_s, ⟨rfl, h_s⟩ ⟩ ⟩,
    use [(T_s ∪ T_t'), (λ (b:β),
      if (b ∈ T_s) then (if (b ∈ T_t') then (f_s b ∩ (f_t' b)) else (f_s b))
      else (if (b ∈ T_t') then (f_t' b) else (∅ : set α)))],
    split,
    { ext a,
      simp_rw [set.mem_inter_iff, set.mem_Inter, finset.mem_union, or_imp_distrib],
      rw ← forall_and_distrib,
      split; intros h1 b; by_cases hbs : b ∈ T_s; by_cases hbt : b ∈ T_t'; specialize h1 b;
        simp only [hbs, hbt, if_true, if_false, true_implies_iff, and_self, false_implies_iff,
          and_true, true_and] at h1 ⊢,
      all_goals { exact h1, }, },
    intros b h_b,
    split_ifs with hbs hbt hbt,
    { refine h_pi b (f_s b) (h_s b hbs) (f_t' b) (h_t' b hbt) (set.nonempty.mono _ h_nonempty),
      exact set.inter_subset_inter (set.bInter_subset_of_mem hbs) (set.bInter_subset_of_mem hbt), },
    { exact h_s b hbs, },
    { exact h_t' b hbt, },
    { rw finset.mem_union at h_b,
      apply false.elim (h_b.elim hbs hbt), }, },
end

/- Every element of the π-system generated by an indexed union of a family of π-systems
is a finite intersection of elements from the π-systems.
For a total union version, see `mem_generate_pi_system_Union_elim`. -/
lemma mem_generate_pi_system_Union_elim' {α β} {g : β → set (set α)} {s : set β}
  (h_pi : ∀ b ∈ s, is_pi_system (g b)) (t : set α) (h_t : t ∈ generate_pi_system (⋃ b ∈ s, g b)) :
  ∃ (T : finset β) (f : β → set α), (↑T ⊆ s) ∧ (t = ⋂ b ∈ T, f b) ∧ (∀ b ∈ T, f b ∈ g b) :=
begin
  have : t ∈ generate_pi_system (⋃ (b : subtype s), (g ∘ subtype.val) b),
  { suffices h1 : (⋃ (b : subtype s), (g ∘ subtype.val) b) = (⋃ b ∈ s, g b), by rwa h1,
    ext x,
    simp only [exists_prop, set.mem_Union, function.comp_app, subtype.exists, subtype.coe_mk],
    refl },
  rcases @mem_generate_pi_system_Union_elim α (subtype s) (g ∘ subtype.val)
    (λ b, h_pi b.val b.property) t this with ⟨T, ⟨f, ⟨rfl, h_t'⟩⟩⟩,
  refine ⟨T.image subtype.val, function.extend subtype.val f (λ b : β, (∅ : set α)), by simp, _, _⟩,
  { ext a, split;
    { simp only [set.mem_Inter, subtype.forall, finset.set_bInter_finset_image],
      intros h1 b h_b h_b_in_T,
      have h2 := h1 b h_b h_b_in_T,
      revert h2,
      rw subtype.val_injective.extend_apply,
      apply id } },
  { intros b h_b,
    simp_rw [finset.mem_image, exists_prop, subtype.exists,
             exists_and_distrib_right, exists_eq_right] at h_b,
    cases h_b,
    have h_b_alt : b = (subtype.mk b h_b_w).val := rfl,
    rw [h_b_alt, subtype.val_injective.extend_apply],
    apply h_t',
    apply h_b_h },
end

section Union_Inter

variables {α ι : Type*}

/-! ### π-system generated by finite intersections of sets of a π-system family -/

/-- From a set of indices `S : set ι` and a family of sets of sets `π : ι → set (set α)`,
define the set of sets that can be written as `⋂ x ∈ t, f x` for some finset `t ⊆ S` and sets
`f x ∈ π x`. If `π` is a family of π-systems, then it is a π-system. -/
def pi_Union_Inter (π : ι → set (set α)) (S : set ι) : set (set α) :=
{s : set α | ∃ (t : finset ι) (htS : ↑t ⊆ S) (f : ι → set α) (hf : ∀ x, x ∈ t → f x ∈ π x),
  s = ⋂ x ∈ t, f x}

lemma pi_Union_Inter_singleton (π : ι → set (set α)) (i : ι) :
  pi_Union_Inter π {i} = π i ∪ {univ} :=
begin
  ext1 s,
  simp only [pi_Union_Inter, exists_prop, mem_union],
  refine ⟨_, λ h, _⟩,
  { rintros ⟨t, hti, f, hfπ, rfl⟩,
    simp only [subset_singleton_iff, finset.mem_coe] at hti,
    by_cases hi : i ∈ t,
    { have ht_eq_i : t = {i},
      { ext1 x, rw finset.mem_singleton, exact ⟨λ h, hti x h, λ h, h.symm ▸ hi⟩, },
      simp only [ht_eq_i, finset.mem_singleton, Inter_Inter_eq_left],
      exact or.inl (hfπ i hi), },
     { have ht_empty : t = ∅,
      { ext1 x,
        simp only [finset.not_mem_empty, iff_false],
        exact λ hx, hi (hti x hx ▸ hx), },
      simp only [ht_empty, Inter_false, Inter_univ, set.mem_singleton univ, or_true], }, },
  { cases h with hs hs,
    { refine ⟨{i}, _, λ _, s, ⟨λ x hx, _, _⟩⟩,
      { rw finset.coe_singleton, },
      { rw finset.mem_singleton at hx,
        rwa hx, },
      { simp only [finset.mem_singleton, Inter_Inter_eq_left], }, },
    { refine ⟨∅, _⟩,
      simpa only [finset.coe_empty, subset_singleton_iff, mem_empty_iff_false, is_empty.forall_iff,
        implies_true_iff, finset.not_mem_empty, Inter_false, Inter_univ, true_and, exists_const]
        using hs, }, },
end

lemma pi_Union_Inter_singleton_left (s : ι → set α) (S : set ι) :
  pi_Union_Inter (λ i, ({s i} : set (set α))) S
    = {s' : set α | ∃ (t : finset ι) (htS : ↑t ⊆ S), s' = ⋂ i ∈ t, s i} :=
begin
  ext1 s',
  simp_rw [pi_Union_Inter, set.mem_singleton_iff, exists_prop, set.mem_set_of_eq],
  refine ⟨λ h, _, λ ⟨t, htS, h_eq⟩, ⟨t, htS, s, λ _ _, rfl, h_eq⟩⟩,
  obtain ⟨t, htS, f, hft_eq, rfl⟩ := h,
  refine ⟨t, htS, _⟩,
  congr' with i x,
  simp_rw set.mem_Inter,
  exact ⟨λ h hit, by { rw ← hft_eq i hit, exact h hit, },
    λ h hit, by { rw hft_eq i hit, exact h hit, }⟩,
end

lemma generate_from_pi_Union_Inter_singleton_left (s : ι → set α) (S : set ι) :
  generate_from (pi_Union_Inter (λ k, {s k}) S) = generate_from {t | ∃ k ∈ S, s k = t} :=
begin
  refine le_antisymm (generate_from_le _) (generate_from_mono _),
  { rintro _ ⟨I, hI, f, hf, rfl⟩,
    refine finset.measurable_set_bInter _ (λ m hm, measurable_set_generate_from _),
    exact ⟨m, hI hm, (hf m hm).symm⟩, },
  { rintro _ ⟨k, hk, rfl⟩,
    refine ⟨{k}, λ m hm, _, s, λ i hi, _, _⟩,
    { rw [finset.mem_coe, finset.mem_singleton] at hm,
      rwa hm, },
    { exact set.mem_singleton _, },
    { simp only [finset.mem_singleton, set.Inter_Inter_eq_left], }, },
end

/-- If `π` is a family of π-systems, then `pi_Union_Inter π S` is a π-system. -/
lemma is_pi_system_pi_Union_Inter (π : ι → set (set α))
  (hpi : ∀ x, is_pi_system (π x)) (S : set ι) :
  is_pi_system (pi_Union_Inter π S) :=
begin
  rintros t1 ⟨p1, hp1S, f1, hf1m, ht1_eq⟩ t2 ⟨p2, hp2S, f2, hf2m, ht2_eq⟩ h_nonempty,
  simp_rw [pi_Union_Inter, set.mem_set_of_eq],
  let g := λ n, (ite (n ∈ p1) (f1 n) set.univ) ∩ (ite (n ∈ p2) (f2 n) set.univ),
  have hp_union_ss : ↑(p1 ∪ p2) ⊆ S,
  { simp only [hp1S, hp2S, finset.coe_union, union_subset_iff, and_self], },
  use [p1 ∪ p2, hp_union_ss, g],
  have h_inter_eq : t1 ∩ t2 = ⋂ i ∈ p1 ∪ p2, g i,
  { rw [ht1_eq, ht2_eq],
    simp_rw [← set.inf_eq_inter, g],
    ext1 x,
    simp only [inf_eq_inter, mem_inter_iff, mem_Inter, finset.mem_union],
    refine ⟨λ h i hi_mem_union, _, λ h, ⟨λ i hi1, _, λ i hi2, _⟩⟩,
    { split_ifs,
      exacts [⟨h.1 i h_1, h.2 i h_2⟩, ⟨h.1 i h_1, set.mem_univ _⟩,
        ⟨set.mem_univ _, h.2 i h_2⟩, ⟨set.mem_univ _, set.mem_univ _⟩], },
    { specialize h i (or.inl hi1),
      rw if_pos hi1 at h,
      exact h.1, },
    { specialize h i (or.inr hi2),
      rw if_pos hi2 at h,
      exact h.2, }, },
  refine ⟨λ n hn, _, h_inter_eq⟩,
  simp_rw g,
  split_ifs with hn1 hn2,
  { refine hpi n (f1 n) (hf1m n hn1) (f2 n) (hf2m n hn2) (set.nonempty_iff_ne_empty.2 (λ h, _)),
    rw h_inter_eq at h_nonempty,
    suffices h_empty : (⋂ i ∈ p1 ∪ p2, g i) = ∅,
      from (set.not_nonempty_iff_eq_empty.mpr h_empty) h_nonempty,
    refine le_antisymm (set.Inter_subset_of_subset n _) (set.empty_subset _),
    refine set.Inter_subset_of_subset hn _,
    simp_rw [g, if_pos hn1, if_pos hn2],
    exact h.subset, },
  { simp [hf1m n hn1], },
  { simp [hf2m n h], },
  { exact absurd hn (by simp [hn1, h]), },
end

lemma pi_Union_Inter_mono_left {π π' : ι → set (set α)} (h_le : ∀ i, π i ⊆ π' i) (S : set ι) :
  pi_Union_Inter π S ⊆ pi_Union_Inter π' S :=
λ s ⟨t, ht_mem, ft, hft_mem_pi, h_eq⟩, ⟨t, ht_mem, ft, λ x hxt, h_le x (hft_mem_pi x hxt), h_eq⟩

lemma pi_Union_Inter_mono_right {π : ι → set (set α)} {S T : set ι} (hST : S ⊆ T) :
  pi_Union_Inter π S ⊆ pi_Union_Inter π T :=
λ s ⟨t, ht_mem, ft, hft_mem_pi, h_eq⟩, ⟨t, ht_mem.trans hST, ft, hft_mem_pi, h_eq⟩

lemma generate_from_pi_Union_Inter_le {m : measurable_space α}
  (π : ι → set (set α)) (h : ∀ n, generate_from (π n) ≤ m) (S : set ι) :
  generate_from (pi_Union_Inter π S) ≤ m :=
begin
  refine generate_from_le _,
  rintros t ⟨ht_p, ht_p_mem, ft, hft_mem_pi, rfl⟩,
  refine finset.measurable_set_bInter _ (λ x hx_mem, (h x) _ _),
  exact measurable_set_generate_from (hft_mem_pi x hx_mem),
end

lemma subset_pi_Union_Inter {π : ι → set (set α)} {S : set ι} {i : ι} (his : i ∈ S) :
  π i ⊆ pi_Union_Inter π S :=
begin
  have h_ss : {i} ⊆ S,
  { intros j hj, rw mem_singleton_iff at hj, rwa hj, },
  refine subset.trans _ (pi_Union_Inter_mono_right h_ss),
  rw pi_Union_Inter_singleton,
  exact subset_union_left _ _,
end

lemma mem_pi_Union_Inter_of_measurable_set (m : ι → measurable_space α)
  {S : set ι} {i : ι} (hiS : i ∈ S) (s : set α)
  (hs : measurable_set[m i] s) :
  s ∈ pi_Union_Inter (λ n, {s | measurable_set[m n] s}) S :=
subset_pi_Union_Inter hiS hs

lemma le_generate_from_pi_Union_Inter {π : ι → set (set α)} (S : set ι) {x : ι} (hxS : x ∈ S) :
  generate_from (π x) ≤ generate_from (pi_Union_Inter π S) :=
generate_from_mono (subset_pi_Union_Inter hxS)

lemma measurable_set_supr_of_mem_pi_Union_Inter (m : ι → measurable_space α)
  (S : set ι) (t : set α) (ht : t ∈ pi_Union_Inter (λ n, {s | measurable_set[m n] s}) S) :
  measurable_set[⨆ i ∈ S, m i] t :=
begin
  rcases ht with ⟨pt, hpt, ft, ht_m, rfl⟩,
  refine pt.measurable_set_bInter (λ i hi, _),
  suffices h_le : m i ≤ (⨆ i ∈ S, m i), from h_le (ft i) (ht_m i hi),
  have hi' : i ∈ S := hpt hi,
  exact le_supr₂ i hi',
end

lemma generate_from_pi_Union_Inter_measurable_set (m : ι → measurable_space α) (S : set ι) :
  generate_from (pi_Union_Inter (λ n, {s | measurable_set[m n] s}) S) = ⨆ i ∈ S, m i :=
begin
  refine le_antisymm _ _,
  { rw ← @generate_from_measurable_set α (⨆ i ∈ S, m i),
    exact generate_from_mono (measurable_set_supr_of_mem_pi_Union_Inter m S), },
  { refine supr₂_le (λ i hi, _),
    rw ← @generate_from_measurable_set α (m i),
    exact generate_from_mono (mem_pi_Union_Inter_of_measurable_set m hi), },
end

end Union_Inter

namespace measurable_space
variable {α : Type*}

/-! ## Dynkin systems and Π-λ theorem -/

/-- A Dynkin system is a collection of subsets of a type `α` that contains the empty set,
  is closed under complementation and under countable union of pairwise disjoint sets.
  The disjointness condition is the only difference with `σ`-algebras.

  The main purpose of Dynkin systems is to provide a powerful induction rule for σ-algebras
  generated by a collection of sets which is stable under intersection.

  A Dynkin system is also known as a "λ-system" or a "d-system".
-/
structure dynkin_system (α : Type*) :=
(has : set α → Prop)
(has_empty : has ∅)
(has_compl : ∀ {a}, has a → has aᶜ)
(has_Union_nat : ∀ {f : ℕ → set α}, pairwise (disjoint on f) → (∀ i, has (f i)) → has (⋃ i, f i))

namespace dynkin_system

@[ext] lemma ext : ∀ {d₁ d₂ : dynkin_system α}, (∀ s : set α, d₁.has s ↔ d₂.has s) → d₁ = d₂
| ⟨s₁, _, _, _⟩ ⟨s₂, _, _, _⟩ h := have s₁ = s₂, from funext $ assume x, propext $ h x,
  by subst this

variable (d : dynkin_system α)

lemma has_compl_iff {a} : d.has aᶜ ↔ d.has a :=
⟨λ h, by simpa using d.has_compl h, λ h, d.has_compl h⟩

lemma has_univ : d.has univ :=
by simpa using d.has_compl d.has_empty

lemma has_Union {β} [countable β] {f : β → set α} (hd : pairwise (disjoint on f))
  (h : ∀ i, d.has (f i)) : d.has (⋃ i, f i) :=
by { casesI nonempty_encodable β, rw ← encodable.Union_decode₂, exact
  d.has_Union_nat (encodable.Union_decode₂_disjoint_on hd)
    (λ n, encodable.Union_decode₂_cases d.has_empty h) }

theorem has_union {s₁ s₂ : set α}
  (h₁ : d.has s₁) (h₂ : d.has s₂) (h : disjoint s₁ s₂) : d.has (s₁ ∪ s₂) :=
by { rw union_eq_Union, exact
  d.has_Union (pairwise_disjoint_on_bool.2 h) (bool.forall_bool.2 ⟨h₂, h₁⟩) }

lemma has_diff {s₁ s₂ : set α} (h₁ : d.has s₁) (h₂ : d.has s₂) (h : s₂ ⊆ s₁) : d.has (s₁ \ s₂) :=
begin
  apply d.has_compl_iff.1,
  simp [diff_eq, compl_inter],
  exact d.has_union (d.has_compl h₁) h₂ (disjoint_compl_left.mono_right h),
end

instance : has_le (dynkin_system α) :=
{ le          := λ m₁ m₂, m₁.has ≤ m₂.has }

lemma le_def {α} {a b : dynkin_system α} : a ≤ b ↔ a.has ≤ b.has := iff.rfl

instance : partial_order (dynkin_system α) :=
{ le_refl     := assume a b, le_rfl,
  le_trans    := assume a b c hab hbc, le_def.mpr (le_trans hab hbc),
  le_antisymm := assume a b h₁ h₂, ext $ assume s, ⟨h₁ s, h₂ s⟩,
  ..dynkin_system.has_le }

/-- Every measurable space (σ-algebra) forms a Dynkin system -/
def of_measurable_space (m : measurable_space α) : dynkin_system α :=
{ has       := m.measurable_set',
  has_empty := m.measurable_set_empty,
  has_compl := m.measurable_set_compl,
  has_Union_nat := assume f _ hf, m.measurable_set_Union f hf }

lemma of_measurable_space_le_of_measurable_space_iff {m₁ m₂ : measurable_space α} :
  of_measurable_space m₁ ≤ of_measurable_space m₂ ↔ m₁ ≤ m₂ :=
iff.rfl

/-- The least Dynkin system containing a collection of basic sets.
  This inductive type gives the underlying collection of sets. -/
inductive generate_has (s : set (set α)) : set α → Prop
| basic : ∀ t ∈ s, generate_has t
| empty : generate_has ∅
| compl : ∀ {a}, generate_has a → generate_has aᶜ
| Union : ∀ {f : ℕ → set α}, pairwise (disjoint on f) →
    (∀ i, generate_has (f i)) → generate_has (⋃ i, f i)

lemma generate_has_compl {C : set (set α)} {s : set α} : generate_has C sᶜ ↔ generate_has C s :=
by { refine ⟨_, generate_has.compl⟩, intro h, convert generate_has.compl h, simp }

/-- The least Dynkin system containing a collection of basic sets. -/
def generate (s : set (set α)) : dynkin_system α :=
{ has := generate_has s,
  has_empty := generate_has.empty,
  has_compl := assume a, generate_has.compl,
  has_Union_nat := assume f, generate_has.Union }

lemma generate_has_def {C : set (set α)} : (generate C).has = generate_has C := rfl

instance : inhabited (dynkin_system α) := ⟨generate univ⟩

/-- If a Dynkin system is closed under binary intersection, then it forms a `σ`-algebra. -/
def to_measurable_space (h_inter : ∀ s₁ s₂, d.has s₁ → d.has s₂ → d.has (s₁ ∩ s₂)) :=
{ measurable_space .
  measurable_set'      := d.has,
  measurable_set_empty := d.has_empty,
  measurable_set_compl := assume s h, d.has_compl h,
  measurable_set_Union := λ f hf,
    begin
      rw ←Union_disjointed,
      exact d.has_Union (disjoint_disjointed _)
        (λ n, disjointed_rec (λ t i h, h_inter _ _ h $ d.has_compl $ hf i) (hf n)),
    end }

lemma of_measurable_space_to_measurable_space
  (h_inter : ∀ s₁ s₂, d.has s₁ → d.has s₂ → d.has (s₁ ∩ s₂)) :
  of_measurable_space (d.to_measurable_space h_inter) = d :=
ext $ assume s, iff.rfl

/-- If `s` is in a Dynkin system `d`, we can form the new Dynkin system `{s ∩ t | t ∈ d}`. -/
def restrict_on {s : set α} (h : d.has s) : dynkin_system α :=
{ has       := λ t, d.has (t ∩ s),
  has_empty := by simp [d.has_empty],
  has_compl := assume t hts,
    have tᶜ ∩ s = ((t ∩ s)ᶜ) \ sᶜ,
      from set.ext $ assume x, by { by_cases x ∈ s; simp [h] },
    by { rw [this], exact d.has_diff (d.has_compl hts) (d.has_compl h)
      (compl_subset_compl.mpr $ inter_subset_right _ _) },
  has_Union_nat := assume f hd hf,
    begin
      rw [Union_inter],
      refine d.has_Union_nat _ hf,
      exact hd.mono (λ i j,
        disjoint.mono (inter_subset_left _ _) (inter_subset_left _ _)),
    end }

lemma generate_le {s : set (set α)} (h : ∀ t ∈ s, d.has t) : generate s ≤ d :=
λ t ht, ht.rec_on h d.has_empty
  (assume a _ h, d.has_compl h)
  (assume f hd _ hf, d.has_Union hd hf)

lemma generate_has_subset_generate_measurable {C : set (set α)} {s : set α}
  (hs : (generate C).has s) : measurable_set[generate_from C] s :=
generate_le (of_measurable_space (generate_from C)) (λ t, measurable_set_generate_from) s hs

lemma generate_inter {s : set (set α)}
  (hs : is_pi_system s) {t₁ t₂ : set α}
  (ht₁ : (generate s).has t₁) (ht₂ : (generate s).has t₂) : (generate s).has (t₁ ∩ t₂) :=
have generate s ≤ (generate s).restrict_on ht₂,
  from generate_le _ $ assume s₁ hs₁,
  have (generate s).has s₁, from generate_has.basic s₁ hs₁,
  have generate s ≤ (generate s).restrict_on this,
    from generate_le _ $ assume s₂ hs₂,
      show (generate s).has (s₂ ∩ s₁), from
        (s₂ ∩ s₁).eq_empty_or_nonempty.elim
        (λ h,  h.symm ▸ generate_has.empty)
        (λ h, generate_has.basic _ $ hs _ hs₂ _ hs₁ h),
  have (generate s).has (t₂ ∩ s₁), from this _ ht₂,
  show (generate s).has (s₁ ∩ t₂), by rwa [inter_comm],
this _ ht₁

/--
  **Dynkin's π-λ theorem**:
  Given a collection of sets closed under binary intersections, then the Dynkin system it
  generates is equal to the σ-algebra it generates.
  This result is known as the π-λ theorem.
  A collection of sets closed under binary intersection is called a π-system (often requiring
  additionnally that is is non-empty, but we drop this condition in the formalization).
-/
lemma generate_from_eq {s : set (set α)} (hs : is_pi_system s) :
  generate_from s = (generate s).to_measurable_space (λ t₁ t₂, generate_inter hs) :=
le_antisymm
  (generate_from_le $ assume t ht, generate_has.basic t ht)
  (of_measurable_space_le_of_measurable_space_iff.mp $
    by { rw [of_measurable_space_to_measurable_space],
    exact (generate_le _ $ assume t ht, measurable_set_generate_from ht) })

end dynkin_system

theorem induction_on_inter {C : set α → Prop} {s : set (set α)} [m : measurable_space α]
  (h_eq : m = generate_from s) (h_inter : is_pi_system s)
  (h_empty : C ∅) (h_basic : ∀ t ∈ s, C t) (h_compl : ∀ t, measurable_set t → C t → C tᶜ)
  (h_union : ∀ f : ℕ → set α, pairwise (disjoint on f) →
    (∀ i, measurable_set (f i)) → (∀ i, C (f i)) → C (⋃ i, f i)) :
  ∀ ⦃t⦄, measurable_set t → C t :=
have eq : measurable_set = dynkin_system.generate_has s,
  by { rw [h_eq, dynkin_system.generate_from_eq h_inter], refl },
assume t ht,
have dynkin_system.generate_has s t, by rwa [eq] at ht,
this.rec_on h_basic h_empty
  (assume t ht, h_compl t $ by { rw [eq], exact ht })
  (assume f hf ht, h_union f hf $ assume i, by { rw [eq], exact ht _ })

end measurable_space
