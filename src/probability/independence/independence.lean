/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.independence.kernel_independence

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → measurable_space Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `measurable_space.comap f m`.

## Main statements

* `Indep_sets.Indep`: if π-systems are independent as sets of sets, then the
  measurable space structures they generate are independent.
* `indep_sets.indep`: variant with two π-systems.
* `measure_zero_or_one_of_measurable_set_limsup_at_top`: Kolmogorov's 0-1 law. Any set which is
  measurable with respect to the tail σ-algebra `limsup s at_top` of an independent sequence of
  σ-algebras `s` has probability 0 or 1.

## Implementation notes

We provide one main definition of independence:
* `Indep_sets`: independence of a family of sets of sets `pi : ι → set (set Ω)`.
Three other independence notions are defined using `Indep_sets`:
* `Indep`: independence of a family of measurable space structures `m : ι → measurable_space Ω`,
* `Indep_set`: independence of a family of sets `s : ι → set Ω`,
* `Indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), measurable_space (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without a capital letter, for example `indep_fun` is the version of `Indep_fun`
for two functions.

The definition of independence for `Indep_sets` uses finite sets (`finset`). An alternative and
equivalent way of defining independence would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep.symm {Ω} {m₁ m₂ : measurable_space Ω} [measurable_space Ω] {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space Ω]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/

open measure_theory measurable_space
open_locale big_operators measure_theory ennreal

namespace probability_theory

variables {Ω ι : Type*}

section definitions


/-- A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def Indep_sets [measurable_space Ω] (π : ι → set (set Ω)) (μ : measure Ω . volume_tac) :
  Prop :=
Indep_setsₖ π (λ u, μ) (measure.dirac unit.star : measure unit)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep_sets [measurable_space Ω] (s1 s2 : set (set Ω)) (μ : measure Ω . volume_tac) : Prop :=
indep_setsₖ s1 s2 (λ u, μ) (measure.dirac unit.star : measure unit)

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def Indep (m : ι → measurable_space Ω) [measurable_space Ω] (μ : measure Ω . volume_tac) :
  Prop :=
Indepₖ m (λ u, μ) (measure.dirac unit.star : measure unit)

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep (m₁ m₂ : measurable_space Ω) [measurable_space Ω] (μ : measure Ω . volume_tac) :
  Prop :=
indepₖ m₁ m₂ (λ u, μ) (measure.dirac unit.star : measure unit)

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def Indep_set [measurable_space Ω] (s : ι → set Ω) (μ : measure Ω . volume_tac) : Prop :=
Indep_setₖ s (λ u, μ) (measure.dirac unit.star : measure unit)

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def indep_set [measurable_space Ω] (s t : set Ω) (μ : measure Ω . volume_tac) : Prop :=
indep_setₖ s t (λ u, μ) (measure.dirac unit.star : measure unit)

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def Indep_fun [measurable_space Ω] {β : ι → Type*} (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), Ω → β x) (μ : measure Ω . volume_tac) : Prop :=
Indep_funₖ m f (λ u, μ) (measure.dirac unit.star : measure unit)

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def indep_fun {β γ} [measurable_space Ω] [mβ : measurable_space β] [mγ : measurable_space γ]
  (f : Ω → β) (g : Ω → γ) (μ : measure Ω . volume_tac) : Prop :=
indep_funₖ f g (λ u, μ) (measure.dirac unit.star : measure unit)

end definitions

section indep

@[symm] lemma indep_sets.symm {s₁ s₂ : set (set Ω)} [measurable_space Ω] {μ : measure Ω}
  (h : indep_sets s₁ s₂ μ) :
  indep_sets s₂ s₁ μ :=
h.symm

@[symm] lemma indep.symm {m₁ m₂ : measurable_space Ω} [measurable_space Ω] {μ : measure Ω}
  (h : indep m₁ m₂ μ) :
  indep m₂ m₁ μ :=
indep_sets.symm h

lemma indep_bot_right (m' : measurable_space Ω) {m : measurable_space Ω}
  {μ : measure Ω} [is_probability_measure μ] :
  indep m' ⊥ μ :=
indepₖ_bot_right m'

lemma indep_bot_left (m' : measurable_space Ω) {m : measurable_space Ω}
  {μ : measure Ω} [is_probability_measure μ] :
  indep ⊥ m' μ :=
indepₖ_bot_left m'

lemma indep_set_empty_right {m : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (s : set Ω) :
  indep_set s ∅ μ :=
indep_setₖ_empty_right s

lemma indep_set_empty_left {m : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (s : set Ω) :
  indep_set ∅ s μ :=
(indep_set_empty_right s).symm

lemma indep_sets_of_indep_sets_of_le_left {s₁ s₂ s₃: set (set Ω)} [measurable_space Ω]
  {μ : measure Ω} (h_indep : indep_sets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
  indep_sets s₃ s₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

lemma indep_sets_of_indep_sets_of_le_right {s₁ s₂ s₃: set (set Ω)} [measurable_space Ω]
  {μ : measure Ω} (h_indep : indep_sets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
  indep_sets s₁ s₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

lemma indep_of_indep_of_le_left {m₁ m₂ m₃: measurable_space Ω} [measurable_space Ω]
  {μ : measure Ω} (h_indep : indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
  indep m₃ m₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (h31 _ ht1) ht2

lemma indep_of_indep_of_le_right {m₁ m₂ m₃: measurable_space Ω} [measurable_space Ω]
  {μ : measure Ω} (h_indep : indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
  indep m₁ m₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (h32 _ ht2)

lemma indep_sets.union [measurable_space Ω] {s₁ s₂ s' : set (set Ω)} {μ : measure Ω}
  (h₁ : indep_sets s₁ s' μ) (h₂ : indep_sets s₂ s' μ) :
  indep_sets (s₁ ∪ s₂) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  cases (set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂,
  { exact h₁ t1 t2 ht1₁ ht2, },
  { exact h₂ t1 t2 ht1₂ ht2, },
end

@[simp] lemma indep_sets.union_iff [measurable_space Ω] {s₁ s₂ s' : set (set Ω)}
  {μ : measure Ω} :
  indep_sets (s₁ ∪ s₂) s' μ ↔ indep_sets s₁ s' μ ∧ indep_sets s₂ s' μ :=
⟨λ h, ⟨indep_sets_of_indep_sets_of_le_left h (set.subset_union_left s₁ s₂),
    indep_sets_of_indep_sets_of_le_left h (set.subset_union_right s₁ s₂)⟩,
  λ h, indep_sets.union h.left h.right⟩

lemma indep_sets.Union [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} (hyp : ∀ n, indep_sets (s n) s' μ) :
  indep_sets (⋃ n, s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  rw set.mem_Union at ht1,
  cases ht1 with n ht1,
  exact hyp n t1 t2 ht1 ht2,
end

lemma indep_sets.bUnion [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} {u : set ι} (hyp : ∀ n ∈ u, indep_sets (s n) s' μ) :
  indep_sets (⋃ n ∈ u, s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  simp_rw set.mem_Union at ht1,
  rcases ht1 with ⟨n, hpn, ht1⟩,
  exact hyp n hpn t1 t2 ht1 ht2,
end

lemma indep_sets.inter [measurable_space Ω] {s₁ s' : set (set Ω)} (s₂ : set (set Ω))
  {μ : measure Ω} (h₁ : indep_sets s₁ s' μ) :
  indep_sets (s₁ ∩ s₂) s' μ :=
λ t1 t2 ht1 ht2, h₁ t1 t2 ((set.mem_inter_iff _ _ _).mp ht1).left ht2

lemma indep_sets.Inter [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} (h : ∃ n, indep_sets (s n) s' μ) :
  indep_sets (⋂ n, s n) s' μ :=
by {intros t1 t2 ht1 ht2, cases h with n h, exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2 }

lemma indep_sets.bInter [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} {u : set ι} (h : ∃ n ∈ u, indep_sets (s n) s' μ) :
  indep_sets (⋂ n ∈ u, s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  rcases h with ⟨n, hn, h⟩,
  exact h t1 t2 (set.bInter_subset_of_mem hn ht1) ht2,
end

lemma indep_sets_singleton_iff [measurable_space Ω] {s t : set Ω} {μ : measure Ω} :
  indep_sets {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t :=
begin
  rw [indep_sets, indep_setsₖ_singleton_iff],
  simp only [ae_dirac_eq, filter.eventually_pure],
end

end indep

/-! ### Deducing `indep` from `Indep` -/
section from_Indep_to_indep

lemma Indep_sets.indep_sets {s : ι → set (set Ω)} [measurable_space Ω] {μ : measure Ω}
  (h_indep : Indep_sets s μ) {i j : ι} (hij : i ≠ j) :
  indep_sets (s i) (s j) μ :=
Indep_setsₖ.indep_setsₖ h_indep hij

lemma Indep.indep {m : ι → measurable_space Ω} [measurable_space Ω] {μ : measure Ω}
  (h_indep : Indep m μ) {i j : ι} (hij : i ≠ j) :
  indep (m i) (m j) μ :=
begin
  change indep_sets ((λ x, measurable_set[m x]) i) ((λ x, measurable_set[m x]) j) μ,
  exact Indep_sets.indep_sets h_indep hij,
end

lemma Indep_fun.indep_fun {m₀ : measurable_space Ω} {μ : measure Ω} {β : ι → Type*}
  {m : Π x, measurable_space (β x)} {f : Π i, Ω → β i} (hf_Indep : Indep_fun m f μ)
  {i j : ι} (hij : i ≠ j) :
  indep_fun (f i) (f j) μ :=
Indep_funₖ.indep_funₖ hf_Indep hij

end from_Indep_to_indep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

section from_measurable_spaces_to_sets_of_sets
/-! ### Independence of measurable space structures implies independence of generating π-systems -/

lemma Indep.Indep_sets [measurable_space Ω] {μ : measure Ω} {m : ι → measurable_space Ω}
  {s : ι → set (set Ω)} (hms : ∀ n, m n = generate_from (s n))
  (h_indep : Indep m μ) :
  Indep_sets s μ :=
λ S f hfs, h_indep S $ λ x hxS,
  ((hms x).symm ▸ measurable_set_generate_from (hfs x hxS) : measurable_set[m x] (f x))

lemma indep.indep_sets [measurable_space Ω] {μ : measure Ω} {s1 s2 : set (set Ω)}
  (h_indep : indep (generate_from s1) (generate_from s2) μ) :
  indep_sets s1 s2 μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end from_measurable_spaces_to_sets_of_sets

section from_pi_systems_to_measurable_spaces
/-! ### Independence of generating π-systems implies independence of measurable space structures -/

lemma indep_sets.indep {m1 m2 : measurable_space Ω} {m : measurable_space Ω}
  {μ : measure Ω} [is_probability_measure μ] {p1 p2 : set (set Ω)} (h1 : m1 ≤ m) (h2 : m2 ≤ m)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m1 = generate_from p1)
  (hpm2 : m2 = generate_from p2) (hyp : indep_sets p1 p2 μ) :
  indep m1 m2 μ :=
indep_setsₖ.indepₖ h1 h2 hp1 hp2 hpm1 hpm2 hyp

lemma indep_sets.indep' {m : measurable_space Ω}
  {μ : measure Ω} [is_probability_measure μ] {p1 p2 : set (set Ω)}
  (hp1m : ∀ s ∈ p1, measurable_set s) (hp2m : ∀ s ∈ p2, measurable_set s)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hyp : indep_sets p1 p2 μ) :
  indep (generate_from p1) (generate_from p2) μ :=
hyp.indep (generate_from_le hp1m) (generate_from_le hp2m) hp1 hp2 rfl rfl

variables {m0 : measurable_space Ω} {μ : measure Ω}

lemma indep_sets_pi_Union_Inter_of_disjoint [is_probability_measure μ]
  {s : ι → set (set Ω)} {S T : set ι}
  (h_indep : Indep_sets s μ) (hST : disjoint S T) :
  indep_sets (pi_Union_Inter s S) (pi_Union_Inter s T) μ :=
indep_setsₖ_pi_Union_Inter_of_disjoint h_indep hST

lemma Indep_set.indep_generate_from_of_disjoint [is_probability_measure μ] {s : ι → set Ω}
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (S T : set ι) (hST : disjoint S T) :
  indep (generate_from {t | ∃ n ∈ S, s n = t}) (generate_from {t | ∃ k ∈ T, s k = t}) μ :=
Indep_setₖ.indepₖ_generate_from_of_disjoint hsm hs S T hST

lemma indep_supr_of_disjoint [is_probability_measure μ] {m : ι → measurable_space Ω}
  (h_le : ∀ i, m i ≤ m0) (h_indep : Indep m μ) {S T : set ι} (hST : disjoint S T) :
  indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ :=
indepₖ_supr_of_disjoint h_le h_indep hST

lemma indep_supr_of_directed_le {Ω} {m : ι → measurable_space Ω}
  {m' m0 : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (h_indep : ∀ i, indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
  (hm : directed (≤) m) :
  indep (⨆ i, m i) m' μ :=
indepₖ_supr_of_directed_le h_indep h_le h_le' hm

lemma Indep_set.indep_generate_from_lt [preorder ι] [is_probability_measure μ]
  {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (i : ι) :
  indep (generate_from {s i}) (generate_from {t | ∃ j < i, s j = t}) μ :=
Indep_setₖ.indepₖ_generate_from_lt hsm hs i

lemma Indep_set.indep_generate_from_le [linear_order ι] [is_probability_measure μ]
  {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ)
  (i : ι) {k : ι} (hk : i < k) :
  indep (generate_from {s k}) (generate_from {t | ∃ j ≤ i, s j = t}) μ :=
Indep_setₖ.indepₖ_generate_from_le hsm hs i hk

lemma Indep_set.indep_generate_from_le_nat [is_probability_measure μ]
  {s : ℕ → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ):
  indep (generate_from {s (n + 1)}) (generate_from {t | ∃ k ≤ n, s k = t}) μ :=
hs.indep_generate_from_le hsm _ n.lt_succ_self

lemma indep_supr_of_monotone [semilattice_sup ι] {Ω} {m : ι → measurable_space Ω}
  {m' m0 : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (h_indep : ∀ i, indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : monotone m) :
  indep (⨆ i, m i) m' μ :=
indep_supr_of_directed_le h_indep h_le h_le' (monotone.directed_le hm)

lemma indep_supr_of_antitone [semilattice_inf ι] {Ω} {m : ι → measurable_space Ω}
  {m' m0 : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (h_indep : ∀ i, indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : antitone m) :
  indep (⨆ i, m i) m' μ :=
indep_supr_of_directed_le h_indep h_le h_le' (directed_of_inf hm)

lemma Indep_sets.pi_Union_Inter_of_not_mem {π : ι → set (set Ω)} {a : ι} {S : finset ι}
  (hp_ind : Indep_sets π μ) (haS : a ∉ S) :
  indep_sets (pi_Union_Inter π S) (π a) μ :=
Indep_setsₖ.pi_Union_Inter_of_not_mem hp_ind haS

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem Indep_sets.Indep [is_probability_measure μ] (m : ι → measurable_space Ω)
  (h_le : ∀ i, m i ≤ m0) (π : ι → set (set Ω)) (h_pi : ∀ n, is_pi_system (π n))
  (h_generate : ∀ i, m i = generate_from (π i)) (h_ind : Indep_sets π μ) :
  Indep m μ :=
Indep_setsₖ.Indepₖ m h_le π h_pi h_generate h_ind

end from_pi_systems_to_measurable_spaces

section indep_set
/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
-/

variables {s t : set Ω} (S T : set (set Ω))

lemma indep_set_iff_indep_sets_singleton {m0 : measurable_space Ω}
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure Ω . volume_tac) [is_probability_measure μ] :
  indep_set s t μ ↔ indep_sets {s} {t} μ :=
indep_setₖ_iff_indep_setsₖ_singleton hs_meas ht_meas

lemma indep_set_iff_measure_inter_eq_mul {m0 : measurable_space Ω}
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure Ω . volume_tac) [is_probability_measure μ] :
  indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t :=
(indep_set_iff_indep_sets_singleton hs_meas ht_meas μ).trans indep_sets_singleton_iff

lemma indep_sets.indep_set_of_mem {m0 : measurable_space Ω} (hs : s ∈ S) (ht : t ∈ T)
  (hs_meas : measurable_set s) (ht_meas : measurable_set t) (μ : measure Ω . volume_tac)
  [is_probability_measure μ] (h_indep : indep_sets S T μ) :
  indep_set s t μ :=
indep_setsₖ.indep_setₖ_of_mem S T hs ht hs_meas ht_meas h_indep

lemma indep.indep_set_of_measurable_set {m₁ m₂ m0 : measurable_space Ω} {μ : measure Ω}
  (h_indep : indep m₁ m₂ μ) {s t : set Ω} (hs : measurable_set[m₁] s) (ht : measurable_set[m₂] t) :
  indep_set s t μ :=
indepₖ.indep_setₖ_of_measurable_set h_indep hs ht

lemma indep_iff_forall_indep_set (m₁ m₂ : measurable_space Ω) {m0 : measurable_space Ω}
  (μ : measure Ω) :
  indep m₁ m₂ μ ↔ ∀ s t, measurable_set[m₁] s → measurable_set[m₂] t → indep_set s t μ :=
indepₖ_iff_forall_indep_setₖ m₁ m₂

end indep_set

section indep_fun

/-! ### Independence of random variables

-/

variables {β β' γ γ' : Type*} {mΩ : measurable_space Ω} {μ : measure Ω} {f : Ω → β} {g : Ω → β'}

lemma indep_fun_iff_measure_inter_preimage_eq_mul
  {mβ : measurable_space β} {mβ' : measurable_space β'} :
  indep_fun f g μ
    ↔ ∀ s t, measurable_set s → measurable_set t
      → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) :=
begin
  rw [Indep_fun, indep_fun_iff_measure_inter_preimage_eq_mul],
  simp only [ae_dirac_eq, filter.eventually_pure],
  split; intro h,
  { refine λ s t hs ht, h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩, },
  { rintros _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩, exact h s t hs ht, },
end

lemma Indep_fun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
  (m : Π x, measurable_space (β x)) (f : Π i, Ω → β i) :
  Indep_fun m f μ
    ↔ ∀ (S : finset ι) {sets : Π i : ι, set (β i)} (H : ∀ i, i ∈ S → measurable_set[m i] (sets i)),
      μ (⋂ i ∈ S, (f i) ⁻¹' (sets i)) = ∏ i in S, μ ((f i) ⁻¹' (sets i)) :=
begin
  rw [Indep_fun, Indep_funₖ_iff_measure_inter_preimage_eq_mul],
  simp only [ae_dirac_eq, filter.eventually_pure],
end

lemma indep_fun_iff_indep_set_preimage {mβ : measurable_space β} {mβ' : measurable_space β'}
  [is_probability_measure μ] (hf : measurable f) (hg : measurable g) :
  indep_fun f g μ ↔ ∀ s t, measurable_set s → measurable_set t → indep_set (f ⁻¹' s) (g ⁻¹' t) μ :=
begin
  rw [Indep_fun, Indep_funₖ_iff_indepₖ_set_preimage],
  simp only [ae_dirac_eq, filter.eventually_pure],
  refine indep_fun_iff_measure_inter_preimage_eq_mul.trans _,
  split; intros h s t hs ht; specialize h s t hs ht,
  { rwa indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ, },
  { rwa ← indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ, },
end

@[symm] lemma indep_fun.symm {mβ : measurable_space β} {f g : Ω → β} (hfg : indep_fun f g μ) :
  indep_fun g f μ :=
hfg.symm

lemma indep_fun.ae_eq {mβ : measurable_space β} {f g f' g' : Ω → β}
  (hfg : indep_fun f g μ) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
  indep_fun f' g' μ :=
begin
  refine indep_funₖ.ae_eq hfg _ _; simp only [ae_dirac_eq, filter.eventually_pure],
  exacts [hf, hg],
end

lemma indep_fun.comp {mβ : measurable_space β} {mβ' : measurable_space β'}
  {mγ : measurable_space γ} {mγ' : measurable_space γ'} {φ : β → γ} {ψ : β' → γ'}
  (hfg : indep_fun f g μ) (hφ : measurable φ) (hψ : measurable ψ) :
  indep_fun (φ ∘ f) (ψ ∘ g) μ :=
indep_funₖ.comp hfg hφ hψ

/-- If `f` is a family of mutually independent random variables (`Indep_fun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
lemma Indep_fun.indep_fun_finset [is_probability_measure μ]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (S T : finset ι) (hST : disjoint S T) (hf_Indep : Indep_fun m f μ)
  (hf_meas : ∀ i, measurable (f i)) :
  indep_fun (λ a (i : S), f i a) (λ a (i : T), f i a) μ :=
Indep_funₖ.indep_funₖ_finset S T hST hf_Indep hf_meas

lemma Indep_fun.indep_fun_prod [is_probability_measure μ]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (hf_Indep : Indep_fun m f μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  indep_fun (λ a, (f i a, f j a)) (f k) μ :=
Indep_funₖ.indep_funₖ_prod hf_Indep hf_meas i j k hik hjk

@[to_additive]
lemma Indep_fun.mul [is_probability_measure μ]
  {ι : Type*} {β : Type*} {m : measurable_space β} [has_mul β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : Indep_fun (λ _, m) f μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  indep_fun (f i * f j) (f k) μ :=
Indep_funₖ.mul hf_Indep hf_meas i j k hik hjk

@[to_additive]
lemma Indep_fun.indep_fun_finset_prod_of_not_mem [is_probability_measure μ]
  {ι : Type*} {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : Indep_fun (λ _, m) f μ) (hf_meas : ∀ i, measurable (f i))
  {s : finset ι} {i : ι} (hi : i ∉ s) :
  indep_fun (∏ j in s, f j) (f i) μ :=
Indep_funₖ.indep_funₖ_finset_prod_of_not_mem hf_Indep hf_meas hi

@[to_additive]
lemma Indep_fun.indep_fun_prod_range_succ [is_probability_measure μ]
  {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ℕ → Ω → β} (hf_Indep : Indep_fun (λ _, m) f μ) (hf_meas : ∀ i, measurable (f i))
  (n : ℕ) :
  indep_fun (∏ j in finset.range n, f j) (f n) μ :=
hf_Indep.indep_fun_finset_prod_of_not_mem hf_meas finset.not_mem_range_self

lemma Indep_set.Indep_fun_indicator [has_zero β] [has_one β] {m : measurable_space β}
  {s : ι → set Ω} (hs : Indep_set s μ) :
  Indep_fun (λ n, m) (λ n, (s n).indicator (λ ω, 1)) μ :=
Indep_setₖ.Indep_funₖ_indicator hs

end indep_fun


/-! ### Kolmogorov's 0-1 law

Let `s : ι → measurable_space Ω` be an independent sequence of sub-σ-algebras. Then any set which
is measurable with respect to the tail σ-algebra `limsup s at_top` has probability 0 or 1.
-/

section zero_one_law

variables {m m0 : measurable_space Ω} {μ : measure Ω}

lemma measure_eq_zero_or_one_or_top_of_indep_set_self {t : set Ω} (h_indep : indep_set t t μ) :
  μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ :=
begin
  specialize h_indep t t (measurable_set_generate_from (set.mem_singleton t))
    (measurable_set_generate_from (set.mem_singleton t)),
  by_cases h0 : μ t = 0,
  { exact or.inl h0, },
  by_cases h_top : μ t = ∞,
  { exact or.inr (or.inr h_top), },
  rw [← one_mul (μ (t ∩ t)), set.inter_self, ennreal.mul_eq_mul_right h0 h_top] at h_indep,
  exact or.inr (or.inl h_indep.symm),
end

lemma measure_eq_zero_or_one_of_indep_set_self [is_finite_measure μ] {t : set Ω}
  (h_indep : indep_set t t μ) :
  μ t = 0 ∨ μ t = 1 :=
begin
  have h_0_1_top := measure_eq_zero_or_one_or_top_of_indep_set_self h_indep,
  simpa [measure_ne_top μ] using h_0_1_top,
end

variables [is_probability_measure μ] {s : ι → measurable_space Ω}

open filter

lemma indep_bsupr_compl (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) (t : set ι) :
  indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ :=
indep_supr_of_disjoint h_le h_indep disjoint_compl_right

section abstract
variables {α : Type*} {p : set ι → Prop} {f : filter ι} {ns : α → set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = set.univ`.

For the example of `f = at_top`, we can take `p = bdd_above` and `ns : ι → set ι := λ i, set.Iic i`.
-/

lemma indep_bsupr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ)
  (hf : ∀ t, p t → tᶜ ∈ f) {t : set ι} (ht : p t) :
  indep (⨆ n ∈ t, s n) (limsup s f) μ :=
begin
  refine indep_of_indep_of_le_right (indep_bsupr_compl h_le h_indep t) _,
  refine Limsup_le_of_le (by is_bounded_default) _,
  simp only [set.mem_compl_iff, eventually_map],
  exact eventually_of_mem (hf t ht) le_supr₂,
end

lemma indep_supr_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ)
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) :
  indep (⨆ a, ⨆ n ∈ (ns a), s n) (limsup s f) μ :=
begin
  refine indep_supr_of_directed_le _ _ _ _,
  { exact λ a, indep_bsupr_limsup h_le h_indep hf (hnsp a), },
  { exact λ a, supr₂_le (λ n hn, h_le n), },
  { exact limsup_le_supr.trans (supr_le h_le), },
  { intros a b,
    obtain ⟨c, hc⟩ := hns a b,
    refine ⟨c, _, _⟩; refine supr_mono (λ n, supr_mono' (λ hn, ⟨_, le_rfl⟩)),
    { exact hc.1 hn, },
    { exact hc.2 hn, }, },
end

lemma indep_supr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indep (⨆ n, s n) (limsup s f) μ :=
begin
  suffices : (⨆ a, ⨆ n ∈ (ns a), s n) = ⨆ n, s n,
  { rw ← this,
    exact indep_supr_directed_limsup h_le h_indep hf hns hnsp, },
  rw supr_comm,
  refine supr_congr (λ n, _),
  have : (⨆ (i : α) (H : n ∈ ns i), s n) = (⨆ (h : ∃ i, n ∈ ns i), s n), by rw supr_exists,
  haveI : nonempty (∃ (i : α), n ∈ ns i) := ⟨hns_univ n⟩,
  rw [this, supr_const],
end

lemma indep_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indep (limsup s f) (limsup s f) μ :=
indep_of_indep_of_le_left (indep_supr_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_supr

theorem measure_zero_or_one_of_measurable_set_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ)
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a))
  (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : set Ω} (ht_tail : measurable_set[limsup s f] t) :
  μ t = 0 ∨ μ t = 1 :=
measure_eq_zero_or_one_of_indep_set_self
  ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indep_set_of_measurable_set
    ht_tail ht_tail)

end abstract

section at_top
variables [semilattice_sup ι] [no_max_order ι] [nonempty ι]

lemma indep_limsup_at_top_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) :
  indep (limsup s at_top) (limsup s at_top) μ :=
begin
  let ns : ι → set ι := set.Iic,
  have hnsp : ∀ i, bdd_above (ns i) := λ i, bdd_above_Iic,
  refine indep_limsup_self h_le h_indep _ _ hnsp _,
  { simp only [mem_at_top_sets, ge_iff_le, set.mem_compl_iff, bdd_above, upper_bounds,
      set.nonempty],
    rintros t ⟨a, ha⟩,
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a,
    refine ⟨b, λ c hc hct, _⟩,
    suffices : ∀ i ∈ t, i < c, from lt_irrefl c (this c hct),
    exact λ i hi, (ha hi).trans_lt (hb.trans_le hc), },
  { exact monotone.directed_le (λ i j hij k hki, le_trans hki hij), },
  { exact λ n, ⟨n, le_rfl⟩, },
end

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s at_top` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_top (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indep s μ) {t : set Ω} (ht_tail : measurable_set[limsup s at_top] t) :
  μ t = 0 ∨ μ t = 1 :=
measure_eq_zero_or_one_of_indep_set_self
  ((indep_limsup_at_top_self h_le h_indep).indep_set_of_measurable_set ht_tail ht_tail)

end at_top

section at_bot
variables [semilattice_inf ι] [no_min_order ι] [nonempty ι]

lemma indep_limsup_at_bot_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) :
  indep (limsup s at_bot) (limsup s at_bot) μ :=
begin
  let ns : ι → set ι := set.Ici,
  have hnsp : ∀ i, bdd_below (ns i) := λ i, bdd_below_Ici,
  refine indep_limsup_self h_le h_indep _ _ hnsp _,
  { simp only [mem_at_bot_sets, ge_iff_le, set.mem_compl_iff, bdd_below, lower_bounds,
      set.nonempty],
    rintros t ⟨a, ha⟩,
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a,
    refine ⟨b, λ c hc hct, _⟩,
    suffices : ∀ i ∈ t, c < i, from lt_irrefl c (this c hct),
    exact λ i hi, hc.trans_lt (hb.trans_le (ha hi)), },
  { exact directed_of_inf (λ i j hij k hki, hij.trans hki), },
  { exact λ n, ⟨n, le_rfl⟩, },
end

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_bot (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indep s μ) {t : set Ω} (ht_tail : measurable_set[limsup s at_bot] t) :
  μ t = 0 ∨ μ t = 1 :=
measure_eq_zero_or_one_of_indep_set_self
  ((indep_limsup_at_bot_self h_le h_indep).indep_set_of_measurable_set ht_tail ht_tail)

end at_bot

end zero_one_law

end probability_theory
