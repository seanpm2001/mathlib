/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

import linear_algebra.finite_dimensional
import combinatorics.rado.rado

/-!
# The Linear Algebra version of Rado's Theorem

We show that `s ↦ rank (span s)` defines a rank function on a module `M`
over a division ring `R`.

We also show that a family `f : ι → M` is linearly independent if and only if
`#s ≤ rank (span (f '' s))` for all finite subsets `s` of `ι`; see
`linear_independent.iff_card_le_rank_span_on_finsets`.

We then use this show the linear algebra version of Rado's Theorem:

*`F : ι → finset M` has the property that `#s ≤ rank (span ⋃ i in s, F i)`
for all finite subsets `s` of `\io` if and only if there exists a linearly independent
family `f : ι → M` such that `f i ∈ F i` for all `i` ("`f` is a section of `F`").*

See `linear_independent.rado`.
-/

namespace submodule

/-- The rank of a submodule spanned by a single element is at most one. -/
lemma finrank_span_singleton_le {K V : Type*} [division_ring K] [add_comm_group V] [module K V]
  (v : V) : finite_dimensional.finrank K (span K ({v} : set V)) ≤ 1 :=
begin
  rcases eq_or_ne v 0 with h | h,
  { rw [span_singleton_eq_bot.mpr h, finrank_bot],
    exact zero_le_one, },
  { rw finrank_span_singleton h, }
end

end submodule

namespace linear_independent

open finite_dimensional submodule rank_fn finset

variables {R : Type*} [division_ring R]
          {M : Type*} [add_comm_group M] [decidable_eq M] [module R M]

/-- A convenience lemma: if `s` and `insert a s` span the same submodule, then
any submodule containing `s` also contains `a` (version for a finset `s`). -/
lemma mem_submodule_of_rank_eq_of_finset_subset {s : finset M} {a : M}
  (h: finrank R (span R (↑(has_insert.insert a s) : set M)) = finrank R (span R (s : set M)))
  (p : submodule R M) (hsp : (s : set M) ⊆ p) : a ∈ p :=
begin
  have ha : a ∈ span R (↑(has_insert.insert a s) : set M),
  { rw [coe_insert],
    exact subset_span (set.mem_insert a ↑s), },
  rw ← eq_of_le_of_finrank_eq (span_mono $ coe_subset.mpr (subset_insert _ _)) h.symm at ha,
  exact mem_span.mp ha p hsp,
end

/-- If `rank (span ({a} ∪ s)) = rank (span s) = rank (span ({b} ∪ s))`,
then `rank (span ({a, b} ∪ s)) = rank (span s)` -/
lemma submodule_insert_insert_eq_of_submodule_insert_eq {s : finset M} {a b : M}
  (ha: finrank R (span R (↑(has_insert.insert a s) : set M)) = finrank R (span R (s : set M)))
  (hb: finrank R (span R (↑(has_insert.insert b s) : set M)) = finrank R (span R (s : set M))) :
  span R (↑(has_insert.insert b (has_insert.insert a s)) : set M) = span R (s : set M) :=
begin
  ext m,
  simp_rw mem_span,
  refine ⟨λ h' (p : submodule R M) hi, _, λ h' (p : submodule R M) hi, _⟩,
  { refine h' p _,
    simp_rw [coe_insert],
    exact set.insert_subset.mpr ⟨mem_submodule_of_rank_eq_of_finset_subset hb p hi,
            set.insert_subset.mpr ⟨mem_submodule_of_rank_eq_of_finset_subset ha p hi, hi⟩⟩, },
  { rw [coe_insert, coe_insert] at hi,
    exact h' p (((set.subset_insert a ↑s).trans (set.subset_insert b _)).trans hi), }
end

variables (R M)

/-- The rank of the submodule generated by a finset defines a rank function. -/
noncomputable
def rank_rk : rank_fn M :=
{ to_fun := λ s, finrank R (span R (s : set M)), -- there is `set.finrank`, but no API for it...
  empty' := by { rw [coe_empty, span_empty, finrank_bot], },
  mono' := λ s t h, finrank_le_finrank_of_le (span_mono $ coe_subset.mpr h),
  insert_le' := λ a s, by
  { rw [insert_eq, union_comm, coe_union, coe_singleton, span_union],
    exact (finrank_add_le_finrank_add_finrank _ _).trans
            (nat.add_le_add_left (finrank_span_singleton_le a) _), },
  dep' :=  λ s a b ha hb, by rw submodule_insert_insert_eq_of_submodule_insert_eq ha hb }

variables {ι : Type*}

@[simp]
lemma rank_rk_eq_finrank (s : finset M) : rank_rk R M s = set.finrank R (s : set M) := rfl

/-- A family `f : ι → M` is linearly independent if and only if the rank of the span of
the image of `s` under `f` is (at least) the cardinality of `s`, for all finite subsets `s`
of `ι`. -/
lemma iff_card_le_rank_span_on_finsets (f : ι → M) :
  linear_independent R f ↔ ∀ s : finset ι, s.card ≤ finrank R (span R (s.image f : set M)) :=
begin
  refine ⟨λ H s, _, λ H, _⟩,
  { have H₁ := comp H (coe : s → ι) subtype.coe_injective,
    convert linear_independent_iff_card_le_finrank_span.mp H₁ using 1,
    { exact (fintype.card_coe s).symm, },
    { rw image_eq_range_coe, refl, } },
  { rw linear_independent_iff',
    refine λ s g hg i hi, _,
    rw ← sum_finset_coe at hg,
    specialize H s,
    rw [← fintype.card_coe, image_eq_range_coe] at H,
    replace H := fintype.linear_independent_iff.mp
                   (linear_independent_iff_card_le_finrank_span.mpr H) (g ∘ coe) hg ⟨i, hi⟩,
    exact H, }
end

variables {R M}

/-- **Rado's Theorem**, linear algebra version: The family `F : ι → finset M` of finite
subsets of the `R`-module `M` has the property that the span of `⋃ i ∈ s, F i`
has dimension at least `#s` for all finite subsets `s` of `ι` if and only if there is
a section `f : ι → M` of `F` (i.e., `f i ∈ F i` for all `i : ι`) that is linearly independent. -/
theorem rado {F : ι → finset M} :
  (∀ s : finset ι, s.card ≤ set.finrank R (s.bUnion F : set M)) ↔
    ∃ f : ι → M, is_section F f ∧ linear_independent R f :=
begin
  simp_rw [← rank_rk_eq_finrank, iff_card_le_rank_span_on_finsets],
  exact rado,
end

end linear_independent
