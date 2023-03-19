/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.independence.kernel_independence
import probability.kernel.condexp_kernel

/-!
# Conditional Independence

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation


-/


open measure_theory measurable_space
open_locale big_operators measure_theory ennreal probability_theory

namespace probability_theory

variables {Ω α ι : Type*} [measurable_space α]

section definitions

/-- A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def cond_Indep_sets (m : measurable_space Ω) [measurable_space Ω] (π : ι → set (set Ω))
  (μ : measure Ω . volume_tac) : Prop :=
Indep_setsₖ π (condexp_to_measure m μ) μ

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def cond_indep_sets (m : measurable_space Ω) [measurable_space Ω] (s1 s2 : set (set Ω))
  (μ : measure Ω . volume_tac) : Prop :=
indep_setsₖ s1 s2 (condexp_to_measure m μ) μ

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def cond_Indep (m' : measurable_space Ω) (m : ι → measurable_space Ω) [measurable_space Ω]
  (μ : measure Ω . volume_tac) : Prop :=
Indepₖ m (condexp_to_measure m' μ) μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def cond_indep (m' m₁ m₂ : measurable_space Ω) [measurable_space Ω]
  (μ : measure Ω . volume_tac) : Prop :=
indepₖ m₁ m₂ (condexp_to_measure m' μ) μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def cond_Indep_set (m : measurable_space Ω) [measurable_space Ω] (s : ι → set Ω)
  (μ : measure Ω . volume_tac) : Prop :=
Indep_setₖ s (condexp_to_measure m μ) μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def cond_indep_set (m : measurable_space Ω) [measurable_space Ω] (s t : set Ω)
  (μ : measure Ω . volume_tac) : Prop :=
indep_setₖ s t (condexp_to_measure m μ) μ

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def cond_Indep_fun (m' : measurable_space Ω) [measurable_space Ω] {β : ι → Type*}
  (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), Ω → β x) (μ : measure Ω . volume_tac) : Prop :=
Indep_funₖ m f (condexp_to_measure m' μ) μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def cond_indep_fun {β γ} (m' : measurable_space Ω)
  [measurable_space Ω] [mβ : measurable_space β] [mγ : measurable_space γ]
  (f : Ω → β) (g : Ω → γ) (μ : measure Ω . volume_tac) : Prop :=
indep_funₖ f g (condexp_to_measure m' μ) μ

end definitions

section indep

variables {m₀ : measurable_space Ω}

@[symm] lemma cond_indep_sets.symm {s₁ s₂ : set (set Ω)} [measurable_space Ω] {μ : measure Ω}
  (h : cond_indep_sets m₀ s₁ s₂ μ) :
  cond_indep_sets m₀ s₂ s₁ μ :=
h.symm

@[symm] lemma cond_indep.symm {m₁ m₂ : measurable_space Ω} [measurable_space Ω]
  {μ : measure Ω}
  (h : cond_indep m₀ m₁ m₂ μ) :
  cond_indep m₀ m₂ m₁ μ :=
h.symm

lemma cond_indep_bot_right (m' : measurable_space Ω) {m : measurable_space Ω} [fact (m₀ ≤ m)]
  {μ : measure Ω} [is_probability_measure μ] :
  cond_indep m₀ m' ⊥ μ :=
indepₖ_bot_right m'

lemma cond_indep_bot_left (m' : measurable_space Ω) {m : measurable_space Ω} [fact (m₀ ≤ m)]
  {μ : measure Ω} [is_probability_measure μ] :
  cond_indep m₀ ⊥ m' μ :=
indepₖ_bot_left m'

lemma cond_indep_set_empty_right {m : measurable_space Ω} [fact (m₀ ≤ m)]
  {μ : measure Ω} [is_probability_measure μ]
  (s : set Ω) :
  cond_indep_set m₀ s ∅ μ :=
indep_setₖ_empty_right s

lemma cond_indep_set_empty_left {m : measurable_space Ω} [fact (m₀ ≤ m)]
  {μ : measure Ω} [is_probability_measure μ]
  (s : set Ω) :
  cond_indep_set m₀ ∅ s μ :=
(cond_indep_set_empty_right s).symm

lemma cond_indep_sets_of_cond_indep_sets_of_le_left {s₁ s₂ s₃: set (set Ω)} [measurable_space Ω]
  {μ : measure Ω} (h_indep : cond_indep_sets m₀ s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
  cond_indep_sets m₀ s₃ s₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

lemma cond_indep_sets_of_cond_indep_sets_of_le_right {s₁ s₂ s₃: set (set Ω)} [measurable_space Ω]
  {μ : measure Ω} (h_indep : cond_indep_sets m₀ s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
  cond_indep_sets m₀ s₁ s₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

lemma cond_indep_of_cond_indep_of_le_left {m₁ m₂ m₃: measurable_space Ω} [measurable_space Ω]
  {μ : measure Ω} (h_indep : cond_indep m₀ m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
  cond_indep m₀ m₃ m₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (h31 _ ht1) ht2

lemma cond_indep_of_cond_indep_of_le_right {m₁ m₂ m₃: measurable_space Ω} [measurable_space Ω]
  {μ : measure Ω} (h_indep : cond_indep m₀ m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
  cond_indep m₀ m₁ m₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (h32 _ ht2)

lemma cond_indep_sets.union [measurable_space Ω] {s₁ s₂ s' : set (set Ω)}
  {μ : measure Ω}
  (h₁ : cond_indep_sets m₀ s₁ s' μ) (h₂ : cond_indep_sets m₀ s₂ s' μ) :
  cond_indep_sets m₀ (s₁ ∪ s₂) s' μ :=
indep_setsₖ.union h₁ h₂

@[simp] lemma cond_indep_sets.union_iff [measurable_space Ω] {s₁ s₂ s' : set (set Ω)}
  {μ : measure Ω} :
  cond_indep_sets m₀ (s₁ ∪ s₂) s' μ ↔ cond_indep_sets m₀ s₁ s' μ ∧ cond_indep_sets m₀ s₂ s' μ :=
indep_setsₖ.union_iff

lemma cond_indep_sets.Union [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} (hyp : ∀ n, cond_indep_sets m₀ (s n) s' μ) :
  cond_indep_sets m₀ (⋃ n, s n) s' μ :=
indep_setsₖ.Union hyp

lemma cond_indep_sets.bUnion [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} {u : set ι} (hyp : ∀ n ∈ u, cond_indep_sets m₀ (s n) s' μ) :
  cond_indep_sets m₀ (⋃ n ∈ u, s n) s' μ :=
indep_setsₖ.bUnion hyp

lemma cond_indep_sets.inter [measurable_space Ω] {s₁ s' : set (set Ω)} (s₂ : set (set Ω))
  {μ : measure Ω} (h₁ : cond_indep_sets m₀ s₁ s' μ) :
  cond_indep_sets m₀ (s₁ ∩ s₂) s' μ :=
λ t1 t2 ht1 ht2, h₁ t1 t2 ((set.mem_inter_iff _ _ _).mp ht1).left ht2

lemma cond_indep_sets.Inter [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} (h : ∃ n, cond_indep_sets m₀ (s n) s' μ) :
  cond_indep_sets m₀ (⋂ n, s n) s' μ :=
by {intros t1 t2 ht1 ht2, cases h with n h, exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2 }

lemma cond_indep_sets.bInter [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} {u : set ι} (h : ∃ n ∈ u, cond_indep_sets m₀ (s n) s' μ) :
  cond_indep_sets m₀ (⋂ n ∈ u, s n) s' μ :=
indep_setsₖ.bInter h

-- todo this one lost some generality
lemma cond_indep_sets_singleton_iff [m0 : measurable_space Ω] {s t : set Ω}
  {μ : measure Ω} (hm : m₀ ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (ht : measurable_set t) :
  cond_indep_sets m₀ {s} {t} μ ↔ ∀ᵐ a ∂μ, μ⟦s ∩ t | m₀⟧ a = μ⟦s | m₀⟧ a * μ⟦t | m₀⟧ a :=
begin
  rw [cond_indep_sets, indep_setsₖ_singleton_iff],
  filter_upwards [(cond_measure_nonneg : 0 ≤ᵐ[μ] μ⟦s | m₀⟧)] with a ha,
  congr' 2 with a,
  rw condexp_to_measure_apply hm a (hs.inter ht),
  swap, exact hμm,
  rw condexp_to_measure_apply hm a hs,
  swap, exact hμm,
  rw condexp_to_measure_apply hm a ht,
  swap, exact hμm,
  rw ← ennreal.of_real_mul,
  rw ennreal.of_real_eq_of_real_iff,
  { sorry }, --exact cond_measure_nonneg,},
  { },
  { },
end

end indep

/-! ### Deducing `indep` from `Indep` -/
section from_Indep_to_indep

variables {m₀ : measurable_space Ω}

lemma cond_Indep_sets.cond_indep_sets {s : ι → set (set Ω)} [measurable_space Ω]
  {μ : measure Ω}
  (h_indep : cond_Indep_sets m₀ s μ) {i j : ι} (hij : i ≠ j) :
  cond_indep_sets m₀ (s i) (s j) μ :=
Indep_setsₖ.indep_setsₖ h_indep hij

lemma cond_Indep.cond_indep {m : ι → measurable_space Ω} [measurable_space Ω]
  {μ : measure Ω}
  (h_indep : cond_Indep m₀ m μ) {i j : ι} (hij : i ≠ j) :
  cond_indep m₀ (m i) (m j) μ :=
h_indep.indepₖ hij

lemma cond_Indep_fun.cond_indep_fun {m₀ : measurable_space Ω}
  {μ : measure Ω} {β : ι → Type*}
  {m : Π x, measurable_space (β x)} {f : Π i, Ω → β i} (hf_Indep : cond_Indep_fun m₀ m f μ)
  {i j : ι} (hij : i ≠ j) :
  cond_indep_fun m₀ (f i) (f j) μ :=
hf_Indep.indep_funₖ hij

end from_Indep_to_indep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

section from_measurable_spaces_to_sets_of_sets
/-! ### Independence of measurable space structures implies independence of generating π-systems -/

variables {m₀ : measurable_space Ω}

lemma cond_Indep.cond_Indep_sets [measurable_space Ω]
  {μ : measure Ω} {m : ι → measurable_space Ω}
  {s : ι → set (set Ω)} (hms : ∀ n, m n = generate_from (s n))
  (h_indep : cond_Indep m₀ m μ) :
  cond_Indep_sets m₀ s μ :=
λ S f hfs, h_indep S $ λ x hxS,
  ((hms x).symm ▸ measurable_set_generate_from (hfs x hxS) : measurable_set[m x] (f x))

lemma cond_indep.cond_indep_sets [measurable_space Ω]
  {μ : measure Ω} {s1 s2 : set (set Ω)}
  (h_indep : cond_indep m₀ (generate_from s1) (generate_from s2) μ) :
  cond_indep_sets m₀ s1 s2 μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end from_measurable_spaces_to_sets_of_sets

section from_pi_systems_to_measurable_spaces
/-! ### Independence of generating π-systems implies independence of measurable space structures -/

variables {m₀ : measurable_space Ω}

lemma cond_indep_sets.cond_indep {m1 m2 : measurable_space Ω} {m : measurable_space Ω}
  [fact (m₀ ≤ m)]
  {μ : measure Ω} [is_probability_measure μ] {p1 p2 : set (set Ω)}
  (h1 : m1 ≤ m) (h2 : m2 ≤ m)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m1 = generate_from p1)
  (hpm2 : m2 = generate_from p2) (hyp : cond_indep_sets m₀ p1 p2 μ) :
  cond_indep m₀ m1 m2 μ :=
indep_setsₖ.indepₖ h1 h2 hp1 hp2 hpm1 hpm2 hyp

lemma cond_indep_sets.cond_indep' {m : measurable_space Ω} [fact (m₀ ≤ m)]
  {μ : measure Ω} [is_probability_measure μ] {p1 p2 : set (set Ω)}
  (hp1m : ∀ s ∈ p1, measurable_set s) (hp2m : ∀ s ∈ p2, measurable_set s)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hyp : cond_indep_sets m₀ p1 p2 μ) :
  cond_indep m₀ (generate_from p1) (generate_from p2) μ :=
hyp.cond_indep (generate_from_le hp1m) (generate_from_le hp2m) hp1 hp2 rfl rfl

variables {m0 : measurable_space Ω} {μ : measure Ω}

lemma cond_indep_sets_pi_Union_Inter_of_disjoint [is_probability_measure μ] [fact (m₀ ≤ m0)]
  {s : ι → set (set Ω)} {S T : set ι}
  (h_indep : cond_Indep_sets m₀ s μ) (hST : disjoint S T) :
  cond_indep_sets m₀ (pi_Union_Inter s S) (pi_Union_Inter s T) μ :=
indep_setsₖ_pi_Union_Inter_of_disjoint h_indep hST

lemma cond_Indep_set.cond_indep_generate_from_of_disjoint [is_probability_measure μ]
  [fact (m₀ ≤ m0)] {s : ι → set Ω}
  (hsm : ∀ n, measurable_set (s n)) (hs : cond_Indep_set m₀ s μ) (S T : set ι)
  (hST : disjoint S T) :
  cond_indep m₀ (generate_from {t | ∃ n ∈ S, s n = t}) (generate_from {t | ∃ k ∈ T, s k = t}) μ :=
Indep_setₖ.indepₖ_generate_from_of_disjoint hsm hs S T hST

lemma cond_indep_supr_of_disjoint [is_probability_measure μ] [fact (m₀ ≤ m0)]
  {m : ι → measurable_space Ω}
  (h_le : ∀ i, m i ≤ m0) (h_indep : cond_Indep m₀ m μ) {S T : set ι} (hST : disjoint S T) :
  cond_indep m₀ (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ :=
indepₖ_supr_of_disjoint h_le h_indep hST

lemma cond_indep_supr_of_directed_le {m : ι → measurable_space Ω}
  {m' m0 : measurable_space Ω} {μ : measure Ω} [fact (m₀ ≤ m0)]
  [is_probability_measure μ]
  (h_indep : ∀ i, cond_indep m₀ (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
  (hm : directed (≤) m) :
  cond_indep m₀ (⨆ i, m i) m' μ :=
indepₖ_supr_of_directed_le h_indep h_le h_le' hm

lemma cond_Indep_set.cond_indep_generate_from_lt [preorder ι] [is_probability_measure μ]
  [fact (m₀ ≤ m0)]
  {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : cond_Indep_set m₀ s μ) (i : ι) :
  cond_indep m₀ (generate_from {s i}) (generate_from {t | ∃ j < i, s j = t}) μ :=
Indep_setₖ.indepₖ_generate_from_lt hsm hs i

lemma cond_Indep_set.cond_indep_generate_from_le [linear_order ι] [is_probability_measure μ]
  [fact (m₀ ≤ m0)] {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : cond_Indep_set m₀ s μ)
  (i : ι) {k : ι} (hk : i < k) :
  cond_indep m₀ (generate_from {s k}) (generate_from {t | ∃ j ≤ i, s j = t}) μ :=
Indep_setₖ.indepₖ_generate_from_le hsm hs i hk

lemma cond_Indep_set.cond_indep_generate_from_le_nat [is_probability_measure μ] [fact (m₀ ≤ m0)]
  {s : ℕ → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : cond_Indep_set m₀ s μ) (n : ℕ):
  cond_indep m₀ (generate_from {s (n + 1)}) (generate_from {t | ∃ k ≤ n, s k = t}) μ :=
hs.cond_indep_generate_from_le hsm _ n.lt_succ_self

lemma cond_indep_supr_of_monotone [semilattice_sup ι] {m : ι → measurable_space Ω}
  {m' m0 : measurable_space Ω} {μ : measure Ω} [fact (m₀ ≤ m0)]
  [is_probability_measure μ]
  (h_indep : ∀ i, cond_indep m₀ (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : monotone m) :
  cond_indep m₀ (⨆ i, m i) m' μ :=
cond_indep_supr_of_directed_le h_indep h_le h_le' (monotone.directed_le hm)

lemma cond_indep_supr_of_antitone [semilattice_inf ι] {m : ι → measurable_space Ω}
  {m' m0 : measurable_space Ω} {μ : measure Ω} [fact (m₀ ≤ m0)]
  [is_probability_measure μ]
  (h_indep : ∀ i, cond_indep m₀ (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : antitone m) :
  cond_indep m₀ (⨆ i, m i) m' μ :=
cond_indep_supr_of_directed_le h_indep h_le h_le' (directed_of_inf hm)

lemma cond_Indep_sets.pi_Union_Inter_of_not_mem {π : ι → set (set Ω)} {a : ι} {S : finset ι}
  (hp_ind : cond_Indep_sets m₀ π μ) (haS : a ∉ S) :
  cond_indep_sets m₀ (pi_Union_Inter π S) (π a) μ :=
Indep_setsₖ.pi_Union_Inter_of_not_mem hp_ind haS

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem cond_Indep_sets.cond_Indep [is_probability_measure μ] [fact (m₀ ≤ m0)]
  (m : ι → measurable_space Ω)
  (h_le : ∀ i, m i ≤ m0) (π : ι → set (set Ω)) (h_pi : ∀ n, is_pi_system (π n))
  (h_generate : ∀ i, m i = generate_from (π i)) (h_ind : cond_Indep_sets m₀ π μ) :
  cond_Indep m₀ m μ :=
Indep_setsₖ.Indepₖ m h_le π h_pi h_generate h_ind

end from_pi_systems_to_measurable_spaces

section indep_set
/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ cond_indep_sets {s} {t} μ`.
-/

variables {m₀ : measurable_space Ω} {s t : set Ω} (S T : set (set Ω))

lemma cond_indep_set_iff_cond_indep_sets_singleton {m0 : measurable_space Ω}
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure Ω . volume_tac) [is_probability_measure μ] [fact (m₀ ≤ m0)] :
  cond_indep_set m₀ s t μ ↔ cond_indep_sets m₀ {s} {t} μ :=
indep_setₖ_iff_indep_setsₖ_singleton hs_meas ht_meas _ μ

lemma cond_indep_set_iff_measure_inter_eq_mul {m0 : measurable_space Ω}
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure Ω . volume_tac) [is_probability_measure μ] :
  cond_indep_set m₀ s t μ ↔ ∀ᵐ a ∂μ, ν a (s ∩ t) = ν a s * ν a t :=
(cond_indep_set_iff_cond_indep_sets_singleton hs_meas ht_meas ν μ).trans cond_indep_sets_singleton_iff

lemma cond_indep_sets.cond_indep_set_of_mem {m0 : measurable_space Ω} (hs : s ∈ S) (ht : t ∈ T)
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure Ω . volume_tac) [is_probability_measure μ] [fact (m₀ ≤ m0)]
  (h_indep : cond_indep_sets m₀ S T μ) :
  cond_indep_set m₀ s t μ :=
indep_setsₖ.indep_setₖ_of_mem S T hs ht hs_meas ht_meas _ μ h_indep

lemma cond_indep.cond_indep_set_of_measurable_set {m₁ m₂ m0 : measurable_space Ω}
  {μ : measure Ω} (h_indep : cond_indep m₀ m₁ m₂ μ) {s t : set Ω}
  (hs : measurable_set[m₁] s) (ht : measurable_set[m₂] t) :
  cond_indep_set m₀ s t μ :=
indepₖ.indep_setₖ_of_measurable_set h_indep hs ht

lemma cond_indep_iff_forall_cond_indep_set (m₁ m₂ : measurable_space Ω) {m0 : measurable_space Ω}
  (μ : measure Ω . volume_tac) :
  cond_indep m₀ m₁ m₂ μ ↔
    ∀ s t, measurable_set[m₁] s → measurable_set[m₂] t → cond_indep_set m₀ s t μ :=
indepₖ_iff_forall_indep_setₖ m₁ m₂ _ μ

end indep_set

section indep_fun

/-! ### Independence of random variables

-/

variables {β β' γ γ' : Type*} {m₀ mΩ : measurable_space Ω} {μ : measure Ω}
  {f : Ω → β} {g : Ω → β'}

lemma cond_indep_fun_iff_measure_inter_preimage_eq_mul
  {mβ : measurable_space β} {mβ' : measurable_space β'} :
  cond_indep_fun m₀ f g μ
    ↔ ∀ s t, measurable_set s → measurable_set t
      → ∀ᵐ a ∂μ, ν a (f ⁻¹' s ∩ g ⁻¹' t) = ν a (f ⁻¹' s) * ν a (g ⁻¹' t) :=
begin
  split; intro h,
  { refine λ s t hs ht, h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩, },
  { rintros _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩, exact h s t hs ht, },
end

lemma cond_Indep_fun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
  (m : Π x, measurable_space (β x)) (f : Π i, Ω → β i) :
  cond_Indep_fun m₀ m f μ
    ↔ ∀ (S : finset ι) {sets : Π i : ι, set (β i)} (H : ∀ i, i ∈ S → measurable_set[m i] (sets i)),
      ∀ᵐ a ∂μ, ν a (⋂ i ∈ S, (f i) ⁻¹' (sets i)) = ∏ i in S, ν a ((f i) ⁻¹' (sets i)) :=
begin
  refine ⟨λ h S sets h_meas, h _ (λ i hi_mem, ⟨sets i, h_meas i hi_mem, rfl⟩), _⟩,
  intros h S setsΩ h_meas,
  classical,
  let setsβ : (Π i : ι, set (β i)) := λ i,
    dite (i ∈ S) (λ hi_mem, (h_meas i hi_mem).some) (λ _, set.univ),
  have h_measβ : ∀ i ∈ S, measurable_set[m i] (setsβ i),
  { intros i hi_mem,
    simp_rw [setsβ, dif_pos hi_mem],
    exact (h_meas i hi_mem).some_spec.1, },
  have h_preim : ∀ i ∈ S, setsΩ i = (f i) ⁻¹' (setsβ i),
  { intros i hi_mem,
    simp_rw [setsβ, dif_pos hi_mem],
    exact (h_meas i hi_mem).some_spec.2.symm, },
  have h_left_eq : ∀ a, ν a (⋂ i ∈ S, setsΩ i) = ν a (⋂ i ∈ S, (f i) ⁻¹' (setsβ i)),
  { intros a,
    congr' with i x,
    simp only [set.mem_Inter],
    split; intros h hi_mem; specialize h hi_mem,
    { rwa h_preim i hi_mem at h, },
    { rwa h_preim i hi_mem, }, },
  have h_right_eq : ∀ a, (∏ i in S, ν a (setsΩ i)) = ∏ i in S, ν a ((f i) ⁻¹' (setsβ i)),
  { refine λ a, finset.prod_congr rfl (λ i hi_mem, _),
    rw h_preim i hi_mem, },
  filter_upwards [h S h_measβ] with a ha,
  rw [h_left_eq a, h_right_eq a, ha],
end

lemma cond_indep_fun_iff_cond_indep_set_preimage {mβ : measurable_space β}
  {mβ' : measurable_space β'}
  [is_probability_measure μ] [fact (m₀ ≤ mΩ)] (hf : measurable f) (hg : measurable g) :
  cond_indep_fun m₀ f g μ ↔
    ∀ s t, measurable_set s → measurable_set t → cond_indep_set m₀ (f ⁻¹' s) (g ⁻¹' t) μ :=
indep_funₖ_iff_indep_setₖ_preimage hf hg

@[symm] lemma cond_indep_fun.symm {mβ : measurable_space β} {f g : Ω → β}
  (hfg : cond_indep_fun m₀ f g μ) :
  cond_indep_fun m₀ g f μ :=
hfg.symm

lemma cond_indep_fun.ae_eq {mβ : measurable_space β} {f g f' g' : Ω → β}
  (hfg : cond_indep_fun m₀ f g μ) (hf : ∀ᵐ a ∂μ, f =ᵐ[ν a] f') (hg : ∀ᵐ a ∂μ, g =ᵐ[ν a] g') :
  cond_indep_fun m₀ f' g' μ :=
begin
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩,
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg',
  have h1 : f ⁻¹' A =ᵐ[ν a] f' ⁻¹' A := hf'.fun_comp A,
  have h2 : g ⁻¹' B =ᵐ[ν a] g' ⁻¹' B := hg'.fun_comp B,
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)],
end

lemma cond_indep_fun.comp {mβ : measurable_space β} {mβ' : measurable_space β'}
  {mγ : measurable_space γ} {mγ' : measurable_space γ'} {φ : β → γ} {ψ : β' → γ'}
  (hfg : cond_indep_fun m₀ f g μ) (hφ : measurable φ) (hψ : measurable ψ) :
  cond_indep_fun m₀ (φ ∘ f) (ψ ∘ g) μ :=
hfg.comp hφ hψ

/-- If `f` is a family of mutually independent random variables (`Indep_fun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
lemma cond_Indep_fun.cond_indep_fun_finset [is_probability_measure μ] [fact (m₀ ≤ mΩ)]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (S T : finset ι) (hST : disjoint S T) (hf_Indep : cond_Indep_fun m₀ m f μ)
  (hf_meas : ∀ i, measurable (f i)) :
  cond_indep_fun m₀ (λ a (i : S), f i a) (λ a (i : T), f i a) μ :=
Indep_funₖ.indep_funₖ_finset S T hST hf_Indep hf_meas

lemma cond_Indep_fun.cond_indep_fun_prod [is_probability_measure μ] [fact (m₀ ≤ mΩ)]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (hf_Indep : cond_Indep_fun m₀ m f μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  cond_indep_fun m₀ (λ a, (f i a, f j a)) (f k) μ :=
Indep_funₖ.indep_funₖ_prod hf_Indep hf_meas i j k hik hjk

@[to_additive]
lemma cond_Indep_fun.mul [is_probability_measure μ] [fact (m₀ ≤ mΩ)]
  {ι : Type*} {β : Type*} {m : measurable_space β} [has_mul β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : cond_Indep_fun m₀ (λ _, m) f μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  cond_indep_fun m₀ (f i * f j) (f k) μ :=
Indep_funₖ.mul hf_Indep hf_meas i j k hik hjk

@[to_additive]
lemma cond_Indep_fun.cond_indep_fun_finset_prod_of_not_mem [is_probability_measure μ]
  [fact (m₀ ≤ mΩ)]
  {ι : Type*} {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : cond_Indep_fun m₀ (λ _, m) f μ) (hf_meas : ∀ i, measurable (f i))
  {s : finset ι} {i : ι} (hi : i ∉ s) :
  cond_indep_fun m₀ (∏ j in s, f j) (f i) μ :=
Indep_funₖ.indep_funₖ_finset_prod_of_not_mem hf_Indep hf_meas hi

@[to_additive]
lemma cond_Indep_fun.cond_indep_fun_prod_range_succ [is_probability_measure μ] [fact (m₀ ≤ mΩ)]
  {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ℕ → Ω → β} (hf_Indep : cond_Indep_fun m₀ (λ _, m) f μ) (hf_meas : ∀ i, measurable (f i))
  (n : ℕ) :
  cond_indep_fun m₀ (∏ j in finset.range n, f j) (f n) μ :=
hf_Indep.cond_indep_fun_finset_prod_of_not_mem hf_meas finset.not_mem_range_self

lemma cond_Indep_set.cond_Indep_fun_indicator [has_zero β] [has_one β] {m : measurable_space β}
  {s : ι → set Ω} (hs : cond_Indep_set m₀ s μ) :
  cond_Indep_fun m₀ (λ n, m) (λ n, (s n).indicator (λ ω, 1)) μ :=
Indep_setₖ.Indep_funₖ_indicator hs

end indep_fun

end probability_theory
