/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Sébastien Gouëzel
-/
import measure_theory.constructions.borel_space.basic
import topology.algebra.order.left_right_lim

/-!
# Stieltjes measures on the real line

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Consider a function `f : ℝ → ℝ` which is monotone and right-continuous. Then one can define a
corrresponding measure, giving mass `f b - f a` to the interval `(a, b]`.

## Main definitions

* `stieltjes_function` is a structure containing a function from `ℝ → ℝ`, together with the
assertions that it is monotone and right-continuous. To `f : stieltjes_function`, one associates
a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = of_real (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = of_real (left_lim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
-/


section move_this
-- this section contains lemmas that should be moved to appropriate places after the port to lean 4

open filter set
open_locale topology

lemma infi_Ioi_eq_infi_rat_gt {f : ℝ → ℝ} (x : ℝ) (hf : bdd_below (f '' Ioi x))
  (hf_mono : monotone f) :
  (⨅ r : Ioi x, f r) = ⨅ q : {q' : ℚ // x < q'}, f q :=
begin
  refine le_antisymm _ _,
  { haveI : nonempty {r' : ℚ // x < ↑r'},
    { obtain ⟨r, hrx⟩ := exists_rat_gt x,
      exact ⟨⟨r, hrx⟩⟩, },
    refine le_cinfi (λ r, _),
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop,
    refine cinfi_set_le hf (hxy.trans _),
    exact_mod_cast hyr, },
  { refine le_cinfi (λ q, _),
    have hq := q.prop,
    rw mem_Ioi at hq,
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq,
    refine (cinfi_le _ _).trans _,
    { exact ⟨y, hxy⟩, },
    { refine ⟨hf.some, λ z, _⟩,
      rintros ⟨u, rfl⟩,
      suffices hfu : f u ∈ f '' Ioi x, from hf.some_spec hfu,
      exact ⟨u, u.prop, rfl⟩, },
    { refine hf_mono (le_trans _ hyq.le),
      norm_cast, }, },
end

-- todo after the port: move to topology/algebra/order/left_right_lim
lemma right_lim_eq_of_tendsto {α β : Type*} [linear_order α] [topological_space β]
  [hα : topological_space α] [h'α : order_topology α] [t2_space β]
  {f : α → β} {a : α} {y : β} (h : 𝓝[>] a ≠ ⊥) (h' : tendsto f (𝓝[>] a) (𝓝 y)) :
  function.right_lim f a = y :=
@left_lim_eq_of_tendsto αᵒᵈ _ _ _ _ _ _ f a y h h'

-- todo after the port: move to topology/algebra/order/left_right_lim
lemma right_lim_eq_Inf {α β : Type*} [linear_order α] [topological_space β]
  [conditionally_complete_linear_order β] [order_topology β] {f : α → β}
  (hf : monotone f) {x : α}
  [topological_space α] [order_topology α] (h : 𝓝[>] x ≠ ⊥) :
  function.right_lim f x = Inf (f '' (Ioi x)) :=
right_lim_eq_of_tendsto h (hf.tendsto_nhds_within_Ioi x)

-- todo after the port: move to order/filter/at_top_bot
lemma exists_seq_monotone_tendsto_at_top_at_top (α : Type*) [semilattice_sup α] [nonempty α]
  [(at_top : filter α).is_countably_generated] :
  ∃ xs : ℕ → α, monotone xs ∧ tendsto xs at_top at_top :=
begin
  haveI h_ne_bot : (at_top : filter α).ne_bot := at_top_ne_bot,
  obtain ⟨ys, h⟩ := exists_seq_tendsto (at_top : filter α),
  let xs : ℕ → α := λ n, finset.sup' (finset.range (n + 1)) finset.nonempty_range_succ ys,
  have h_mono : monotone xs,
  { intros i j hij,
    rw finset.sup'_le_iff,
    intros k hk,
    refine finset.le_sup'_of_le _ _ le_rfl,
    rw finset.mem_range at hk ⊢,
    exact hk.trans_le (add_le_add_right hij _), },
  refine ⟨xs, h_mono, _⟩,
  { refine tendsto_at_top_at_top_of_monotone h_mono _,
    have : ∀ (a : α), ∃ (n : ℕ), a ≤ ys n,
    { rw tendsto_at_top_at_top at h,
      intro a,
      obtain ⟨i, hi⟩ := h a,
      exact ⟨i, hi i le_rfl⟩, },
    intro a,
    obtain ⟨i, hi⟩ := this a,
    refine ⟨i, hi.trans _⟩,
    refine finset.le_sup'_of_le _ _ le_rfl,
    rw finset.mem_range_succ_iff, },
end

lemma exists_seq_antitone_tendsto_at_top_at_bot (α : Type*) [semilattice_inf α] [nonempty α]
  [h2 : (at_bot : filter α).is_countably_generated] :
  ∃ xs : ℕ → α, antitone xs ∧ tendsto xs at_top at_bot :=
@exists_seq_monotone_tendsto_at_top_at_top αᵒᵈ _ _ h2

-- todo after the port: move to topology/algebra/order/monotone_convergence
lemma supr_eq_supr_subseq_of_antitone {ι₁ ι₂ α : Type*} [preorder ι₂] [complete_lattice α]
  {l : filter ι₁} [l.ne_bot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : antitone f)
  (hφ : tendsto φ l at_bot) :
  (⨆ i, f i) = (⨆ i, f (φ i)) :=
le_antisymm
  (supr_mono' (λ i, exists_imp_exists (λ j (hj : φ j ≤ i), hf hj)
    (hφ.eventually $ eventually_le_at_bot i).exists))
  (supr_mono' (λ i, ⟨φ i, le_rfl⟩))

namespace measure_theory
-- todo after the port: move these lemmas to measure_theory/measure/measure_space?
variables {α : Type*} {mα : measurable_space α}
include mα

lemma tendsto_measure_Ico_at_top [semilattice_sup α] [no_max_order α]
  [(at_top : filter α).is_countably_generated] (μ : measure α) (a : α) :
  tendsto (λ x, μ (Ico a x)) at_top (𝓝 (μ (Ici a))) :=
begin
  haveI : nonempty α := ⟨a⟩,
  have h_mono : monotone (λ x, μ (Ico a x)) := λ i j hij, measure_mono (Ico_subset_Ico_right hij),
  convert tendsto_at_top_supr h_mono,
  obtain ⟨xs, hxs_mono, hxs_tendsto⟩ := exists_seq_monotone_tendsto_at_top_at_top α,
  have h_Ici : Ici a = ⋃ n, Ico a (xs n),
  { ext1 x,
    simp only [mem_Ici, mem_Union, mem_Ico, exists_and_distrib_left, iff_self_and],
    intro _,
    obtain ⟨y, hxy⟩ := no_max_order.exists_gt x,
    obtain ⟨n, hn⟩ := tendsto_at_top_at_top.mp hxs_tendsto y,
    exact ⟨n, hxy.trans_le (hn n le_rfl)⟩, },
  rw [h_Ici, measure_Union_eq_supr, supr_eq_supr_subseq_of_monotone h_mono hxs_tendsto],
  exact monotone.directed_le (λ i j hij, Ico_subset_Ico_right (hxs_mono hij)),
end

lemma tendsto_measure_Ioc_at_bot [semilattice_inf α] [no_min_order α]
  [(at_bot : filter α).is_countably_generated] (μ : measure α) (a : α) :
  tendsto (λ x, μ (Ioc x a)) at_bot (𝓝 (μ (Iic a))) :=
begin
  haveI : nonempty α := ⟨a⟩,
  have h_mono : antitone (λ x, μ (Ioc x a)) := λ i j hij, measure_mono (Ioc_subset_Ioc_left hij),
  convert tendsto_at_bot_supr h_mono,
  obtain ⟨xs, hxs_mono, hxs_tendsto⟩ := exists_seq_antitone_tendsto_at_top_at_bot α,
  have h_Iic : Iic a = ⋃ n, Ioc (xs n) a,
  { ext1 x,
    simp only [mem_Iic, mem_Union, mem_Ioc, exists_and_distrib_right, iff_and_self],
    intro _,
    obtain ⟨y, hxy⟩ := no_min_order.exists_lt x,
    obtain ⟨n, hn⟩ := tendsto_at_top_at_bot.mp hxs_tendsto y,
    exact ⟨n, (hn n le_rfl).trans_lt hxy⟩, },
  rw [h_Iic, measure_Union_eq_supr, supr_eq_supr_subseq_of_antitone h_mono hxs_tendsto],
  exact monotone.directed_le (λ i j hij, Ioc_subset_Ioc_left (hxs_mono hij)),
end

lemma tendsto_measure_Iic_at_top [semilattice_sup α] [(at_top : filter α).is_countably_generated]
  (μ : measure α) :
  tendsto (λ x, μ (Iic x)) at_top (𝓝 (μ univ)) :=
begin
  casesI is_empty_or_nonempty α,
  { have h1 : ∀ x : α, Iic x = ∅ := λ x, subsingleton.elim _ _,
    have h2 : (univ : set α) = ∅ := subsingleton.elim _ _,
    simp_rw [h1, h2],
    exact tendsto_const_nhds, },
  have h_mono : monotone (λ x, μ (Iic x)) := λ i j hij, measure_mono (Iic_subset_Iic.mpr hij),
  convert tendsto_at_top_supr h_mono,
  obtain ⟨xs, hxs_mono, hxs_tendsto⟩ := exists_seq_monotone_tendsto_at_top_at_top α,
  have h_univ : (univ : set α) = ⋃ n, Iic (xs n),
  { ext1 x,
    simp only [mem_univ, mem_Union, mem_Iic, true_iff],
    obtain ⟨n, hn⟩ := tendsto_at_top_at_top.mp hxs_tendsto x,
    exact ⟨n, hn n le_rfl⟩, },
  rw [h_univ, measure_Union_eq_supr, supr_eq_supr_subseq_of_monotone h_mono hxs_tendsto],
  exact monotone.directed_le (λ i j hij, Iic_subset_Iic.mpr (hxs_mono hij)),
end

lemma tendsto_measure_Ici_at_bot [semilattice_inf α]
  [h : (at_bot : filter α).is_countably_generated] (μ : measure α) :
  tendsto (λ x, μ (Ici x)) at_bot (𝓝 (μ univ)) :=
@tendsto_measure_Iic_at_top αᵒᵈ _ _ h μ

end measure_theory

end move_this


noncomputable theory
open classical set filter function
open ennreal (of_real)
open_locale big_operators ennreal nnreal topology measure_theory

/-! ### Basic properties of Stieltjes functions -/

/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure stieltjes_function :=
(to_fun : ℝ → ℝ)
(mono' : monotone to_fun)
(right_continuous' : ∀ x, continuous_within_at to_fun (Ici x) x)

namespace stieltjes_function

instance : has_coe_to_fun stieltjes_function (λ _, ℝ → ℝ) := ⟨to_fun⟩

initialize_simps_projections stieltjes_function (to_fun → apply)

variable (f : stieltjes_function)

lemma mono : monotone f := f.mono'

lemma right_continuous (x : ℝ) : continuous_within_at f (Ici x) x := f.right_continuous' x

lemma right_lim_eq (f : stieltjes_function) (x : ℝ) :
  function.right_lim f x = f x :=
begin
  rw [← f.mono.continuous_within_at_Ioi_iff_right_lim_eq, continuous_within_at_Ioi_iff_Ici],
  exact f.right_continuous' x,
end

lemma infi_Ioi_eq (f : stieltjes_function) (x : ℝ) :
  (⨅ r : Ioi x, f r) = f x :=
begin
  suffices : function.right_lim f x = ⨅ r : Ioi x, f r,
  { rw [← this, f.right_lim_eq], },
  rw [right_lim_eq_Inf f.mono, Inf_image'],
  rw ← ne_bot_iff,
  apply_instance,
end

lemma infi_rat_gt_eq (f : stieltjes_function) (x : ℝ) :
  (⨅ r : {r' : ℚ // x < r'}, f r) = f x :=
begin
  rw ← infi_Ioi_eq f x,
  refine (infi_Ioi_eq_infi_rat_gt _ _ f.mono).symm,
  refine ⟨f x, λ y, _⟩,
  rintros ⟨y, hy_mem, rfl⟩,
  exact f.mono (le_of_lt hy_mem),
end

/-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
@[simps] protected def id : stieltjes_function :=
{ to_fun := id,
  mono' := λ x y, id,
  right_continuous' := λ x, continuous_within_at_id }

@[simp] lemma id_left_lim (x : ℝ) : left_lim stieltjes_function.id x = x :=
tendsto_nhds_unique (stieltjes_function.id.mono.tendsto_left_lim x) $
  (continuous_at_id).tendsto.mono_left nhds_within_le_nhds

instance : inhabited stieltjes_function := ⟨stieltjes_function.id⟩

/-- If a function `f : ℝ → ℝ` is monotone, then the function mapping `x` to the right limit of `f`
at `x` is a Stieltjes function, i.e., it is monotone and right-continuous. -/
noncomputable def _root_.monotone.stieltjes_function {f : ℝ → ℝ} (hf : monotone f) :
  stieltjes_function :=
{ to_fun := right_lim f,
  mono' := λ x y hxy, hf.right_lim hxy,
  right_continuous' :=
  begin
    assume x s hs,
    obtain ⟨l, u, hlu, lus⟩ : ∃ (l u : ℝ), right_lim f x ∈ Ioo l u ∧ Ioo l u ⊆ s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs,
    obtain ⟨y, xy, h'y⟩ : ∃ (y : ℝ) (H : x < y), Ioc x y ⊆ f ⁻¹' (Ioo l u) :=
      mem_nhds_within_Ioi_iff_exists_Ioc_subset.1
        (hf.tendsto_right_lim x (Ioo_mem_nhds hlu.1 hlu.2)),
    change ∀ᶠ y in 𝓝[≥] x, right_lim f y ∈ s,
    filter_upwards [Ico_mem_nhds_within_Ici ⟨le_refl x, xy⟩] with z hz,
    apply lus,
    refine ⟨hlu.1.trans_le (hf.right_lim hz.1), _⟩,
    obtain ⟨a, za, ay⟩ : ∃ (a : ℝ), z < a ∧ a < y := exists_between hz.2,
    calc right_lim f z ≤ f a : hf.right_lim_le za
                   ... < u   : (h'y ⟨hz.1.trans_lt za, ay.le⟩).2,
  end }

lemma _root_.monotone.stieltjes_function_eq {f : ℝ → ℝ} (hf : monotone f) (x : ℝ) :
  hf.stieltjes_function x = right_lim f x := rfl

lemma countable_left_lim_ne (f : stieltjes_function) :
  set.countable {x | left_lim f x ≠ f x} :=
begin
  apply countable.mono _ (f.mono.countable_not_continuous_at),
  assume x hx h'x,
  apply hx,
  exact tendsto_nhds_unique (f.mono.tendsto_left_lim x) (h'x.tendsto.mono_left nhds_within_le_nhds),
end


/-! ### The outer measure associated to a Stieltjes function -/

/-- Length of an interval. This is the largest monotone function which correctly measures all
intervals. -/
def length (s : set ℝ) : ℝ≥0∞ := ⨅a b (h : s ⊆ Ioc a b), of_real (f b - f a)

@[simp] lemma length_empty : f.length ∅ = 0 :=
nonpos_iff_eq_zero.1 $ infi_le_of_le 0 $ infi_le_of_le 0 $ by simp

@[simp] lemma length_Ioc (a b : ℝ) :
  f.length (Ioc a b) = of_real (f b - f a) :=
begin
  refine le_antisymm (infi_le_of_le a $ infi₂_le b subset.rfl)
    (le_infi $ λ a', le_infi $ λ b', le_infi $ λ h, ennreal.coe_le_coe.2 _),
  cases le_or_lt b a with ab ab,
  { rw real.to_nnreal_of_nonpos (sub_nonpos.2 (f.mono ab)), apply zero_le, },
  cases (Ioc_subset_Ioc_iff ab).1 h with h₁ h₂,
  exact real.to_nnreal_le_to_nnreal (sub_le_sub (f.mono h₁) (f.mono h₂))
end

lemma length_mono {s₁ s₂ : set ℝ} (h : s₁ ⊆ s₂) : f.length s₁ ≤ f.length s₂ :=
infi_mono $ λ a, binfi_mono $ λ b, h.trans

open measure_theory

/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : outer_measure ℝ :=
outer_measure.of_function f.length f.length_empty

lemma outer_le_length (s : set ℝ) : f.outer s ≤ f.length s :=
outer_measure.of_function_le _

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
lemma length_subadditive_Icc_Ioo {a b : ℝ} {c d : ℕ → ℝ}
  (ss : Icc a b ⊆ ⋃ i, Ioo (c i) (d i)) :
  of_real (f b - f a) ≤ ∑' i, of_real (f (d i) - f (c i)) :=
begin
  suffices : ∀ (s:finset ℕ) b
    (cv : Icc a b ⊆ ⋃ i ∈ (↑s:set ℕ), Ioo (c i) (d i)),
    (of_real (f b - f a) : ℝ≥0∞) ≤ ∑ i in s, of_real (f (d i) - f (c i)),
  { rcases is_compact_Icc.elim_finite_subcover_image (λ (i : ℕ) (_ : i ∈ univ),
      @is_open_Ioo _ _ _ _ (c i) (d i)) (by simpa using ss) with ⟨s, su, hf, hs⟩,
    have e : (⋃ i ∈ (↑hf.to_finset:set ℕ), Ioo (c i) (d i)) = (⋃ i ∈ s, Ioo (c i) (d i)),
      by simp only [ext_iff, exists_prop, finset.set_bUnion_coe, mem_Union, forall_const, iff_self,
                    finite.mem_to_finset],
    rw ennreal.tsum_eq_supr_sum,
    refine le_trans _ (le_supr _ hf.to_finset),
    exact this hf.to_finset _ (by simpa only [e]) },
  clear ss b,
  refine λ s, finset.strong_induction_on s (λ s IH b cv, _),
  cases le_total b a with ab ab,
  { rw ennreal.of_real_eq_zero.2 (sub_nonpos.2 (f.mono ab)), exact zero_le _, },
  have := cv ⟨ab, le_rfl⟩, simp at this,
  rcases this with ⟨i, is, cb, bd⟩,
  rw [← finset.insert_erase is] at cv ⊢,
  rw [finset.coe_insert, bUnion_insert] at cv,
  rw [finset.sum_insert (finset.not_mem_erase _ _)],
  refine le_trans _ (add_le_add_left (IH _ (finset.erase_ssubset is) (c i) _) _),
  { refine le_trans (ennreal.of_real_le_of_real _) ennreal.of_real_add_le,
    rw sub_add_sub_cancel,
    exact sub_le_sub_right (f.mono bd.le) _ },
  { rintro x ⟨h₁, h₂⟩,
    refine (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left
      (mt and.left (not_lt_of_le h₂)) }
end

@[simp] lemma outer_Ioc (a b : ℝ) :
  f.outer (Ioc a b) = of_real (f b - f a) :=
begin
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
  by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
  intervals, while we would like to have a compact interval covered by open intervals to use
  compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use the
  right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is still
  covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a` (up to `ε/2`).
  Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
  very close to  that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
  slightly to the right, then the `f`-length will change very little by right continuity, and we
  will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
  of the `f`-length of `s i`. -/
  refine le_antisymm (by { rw ← f.length_Ioc, apply outer_le_length })
    (le_infi₂ $ λ s hs, ennreal.le_of_forall_pos_le_add $ λ ε εpos h, _),
  let δ := ε / 2,
  have δpos : 0 < (δ : ℝ≥0∞), by simpa using εpos.ne',
  rcases ennreal.exists_pos_sum_of_countable δpos.ne' ℕ with ⟨ε', ε'0, hε⟩,
  obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a',
  { have A : continuous_within_at (λ r, f r - f a) (Ioi a) a,
    { refine continuous_within_at.sub _ continuous_within_at_const,
      exact (f.right_continuous a).mono Ioi_subset_Ici_self },
    have B : f a - f a < δ, by rwa [sub_self, nnreal.coe_pos, ← ennreal.coe_pos],
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhds_within).exists },
  have : ∀ i, ∃ p:ℝ×ℝ, s i ⊆ Ioo p.1 p.2 ∧
                        (of_real (f p.2 - f p.1) : ℝ≥0∞) < f.length (s i) + ε' i,
  { intro i,
    have := (ennreal.lt_add_right ((ennreal.le_tsum i).trans_lt h).ne
        (ennreal.coe_ne_zero.2 (ε'0 i).ne')),
    conv at this { to_lhs, rw length },
    simp only [infi_lt_iff, exists_prop] at this,
    rcases this with ⟨p, q', spq, hq'⟩,
    have : continuous_within_at (λ r, of_real (f r - f p)) (Ioi q') q',
    { apply ennreal.continuous_of_real.continuous_at.comp_continuous_within_at,
      refine continuous_within_at.sub _ continuous_within_at_const,
      exact (f.right_continuous q').mono Ioi_subset_Ici_self },
    rcases (((tendsto_order.1 this).2 _ hq').and self_mem_nhds_within).exists with ⟨q, hq, q'q⟩,
    exact ⟨⟨p, q⟩, spq.trans (Ioc_subset_Ioo_right q'q), hq⟩ },
  choose g hg using this,
  have I_subset : Icc a' b ⊆ ⋃ i, Ioo (g i).1 (g i).2 := calc
    Icc a' b ⊆ Ioc a b : λ x hx, ⟨aa'.trans_le hx.1, hx.2⟩
    ... ⊆ ⋃ i, s i : hs
    ... ⊆ ⋃ i, Ioo (g i).1 (g i).2 : Union_mono (λ i, (hg i).1),
  calc of_real (f b - f a)
      = of_real ((f b - f a') + (f a' - f a)) : by rw sub_add_sub_cancel
  ... ≤ of_real (f b - f a') + of_real (f a' - f a) : ennreal.of_real_add_le
  ... ≤ (∑' i, of_real (f (g i).2 - f (g i).1)) + of_real δ :
    add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ennreal.of_real_le_of_real ha'.le)
  ... ≤ (∑' i, (f.length (s i) + ε' i)) + δ :
    add_le_add (ennreal.tsum_le_tsum (λ i, (hg i).2.le))
      (by simp only [ennreal.of_real_coe_nnreal, le_rfl])
  ... = (∑' i, f.length (s i)) + (∑' i, ε' i) + δ : by rw [ennreal.tsum_add]
  ... ≤ (∑' i, f.length (s i)) + δ + δ : add_le_add (add_le_add le_rfl hε.le) le_rfl
  ... = ∑' (i : ℕ), f.length (s i) + ε : by simp [add_assoc, ennreal.add_halves]
end

lemma measurable_set_Ioi {c : ℝ} :
  measurable_set[f.outer.caratheodory] (Ioi c) :=
begin
  apply outer_measure.of_function_caratheodory (λ t, _),
  refine le_infi (λ a, le_infi (λ b, le_infi (λ h, _))),
  refine le_trans (add_le_add
    (f.length_mono $ inter_subset_inter_left _ h)
    (f.length_mono $ diff_subset_diff_left h)) _,
  cases le_total a c with hac hac; cases le_total b c with hbc hbc,
  { simp only [Ioc_inter_Ioi, f.length_Ioc, hac, sup_eq_max, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_diff_Ioi, f.length_empty, zero_add, not_lt] },
  { simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      sup_eq_max, ←ennreal.of_real_add, f.mono hac, f.mono hbc, sub_nonneg, sub_add_sub_cancel,
      le_refl, max_eq_right] },
  { simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_diff_Ioi,
      f.length_empty, zero_add, or_true, le_sup_iff, f.length_Ioc, not_lt] },
  { simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      sup_eq_max, le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt] }
end

theorem outer_trim : f.outer.trim = f.outer :=
begin
  refine le_antisymm (λ s, _) (outer_measure.le_trim _),
  rw outer_measure.trim_eq_infi,
  refine le_infi (λ t, le_infi $ λ ht,
    ennreal.le_of_forall_pos_le_add $ λ ε ε0 h, _),
  rcases ennreal.exists_pos_sum_of_countable
    (ennreal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩,
  refine le_trans _ (add_le_add_left (le_of_lt hε) _),
  rw ← ennreal.tsum_add,
  choose g hg using show
    ∀ i, ∃ s, t i ⊆ s ∧ measurable_set s ∧
      f.outer s ≤ f.length (t i) + of_real (ε' i),
  { intro i,
    have := (ennreal.lt_add_right ((ennreal.le_tsum i).trans_lt h).ne
        (ennreal.coe_pos.2 (ε'0 i)).ne'),
    conv at this {to_lhs, rw length},
    simp only [infi_lt_iff] at this,
    rcases this with ⟨a, b, h₁, h₂⟩,
    rw ← f.outer_Ioc at h₂,
    exact ⟨_, h₁, measurable_set_Ioc, le_of_lt $ by simpa using h₂⟩ },
  simp at hg,
  apply infi_le_of_le (Union g) _,
  apply infi_le_of_le (ht.trans $ Union_mono (λ i, (hg i).1)) _,
  apply infi_le_of_le (measurable_set.Union (λ i, (hg i).2.1)) _,
  exact le_trans (f.outer.Union _) (ennreal.tsum_le_tsum $ λ i, (hg i).2.2)
end

lemma borel_le_measurable : borel ℝ ≤ f.outer.caratheodory :=
begin
  rw borel_eq_generate_from_Ioi,
  refine measurable_space.generate_from_le _,
  simp [f.measurable_set_Ioi] { contextual := tt }
end

/-! ### The measure associated to a Stieltjes function -/

/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. -/
@[irreducible] protected def measure : measure ℝ :=
{ to_outer_measure := f.outer,
  m_Union := λ s hs, f.outer.Union_eq_of_caratheodory $
    λ i, f.borel_le_measurable _ (hs i),
  trimmed := f.outer_trim }

@[simp] lemma measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = of_real (f b - f a) :=
by { rw stieltjes_function.measure, exact f.outer_Ioc a b }

@[simp] lemma measure_singleton (a : ℝ) : f.measure {a} = of_real (f a - left_lim f a) :=
begin
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ : ∃ (u : ℕ → ℝ), strict_mono u ∧ (∀ (n : ℕ), u n < a)
    ∧ tendsto u at_top (𝓝 a) := exists_seq_strict_mono_tendsto a,
  have A : {a} = ⋂ n, Ioc (u n) a,
  { refine subset.antisymm (λ x hx, by simp [mem_singleton_iff.1 hx, u_lt_a]) (λ x hx, _),
    simp at hx,
    have : a ≤ x := le_of_tendsto' u_lim (λ n, (hx n).1.le),
    simp [le_antisymm this (hx 0).2] },
  have L1 : tendsto (λ n, f.measure (Ioc (u n) a)) at_top (𝓝 (f.measure {a})),
  { rw A,
    refine tendsto_measure_Inter (λ n, measurable_set_Ioc) (λ m n hmn, _) _,
    { exact Ioc_subset_Ioc (u_mono.monotone hmn) le_rfl },
    { exact ⟨0, by simpa only [measure_Ioc] using ennreal.of_real_ne_top⟩ } },
  have L2 : tendsto (λ n, f.measure (Ioc (u n) a)) at_top (𝓝 (of_real (f a - left_lim f a))),
  { simp only [measure_Ioc],
    have : tendsto (λ n, f (u n)) at_top (𝓝 (left_lim f a)),
    { apply (f.mono.tendsto_left_lim a).comp,
      exact tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ u_lim
        (eventually_of_forall (λ n, u_lt_a n)) },
    exact ennreal.continuous_of_real.continuous_at.tendsto.comp (tendsto_const_nhds.sub this) },
  exact tendsto_nhds_unique L1 L2
end

@[simp] lemma measure_Icc (a b : ℝ) : f.measure (Icc a b) = of_real (f b - left_lim f a) :=
begin
  rcases le_or_lt a b with hab|hab,
  { have A : disjoint {a} (Ioc a b), by simp,
    simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ennreal.of_real_add,
      f.mono.left_lim_le, measure_union A measurable_set_Ioc, f.mono hab] },
  { simp only [hab, measure_empty, Icc_eq_empty, not_le],
    symmetry,
    simp [ennreal.of_real_eq_zero, f.mono.le_left_lim hab] }
end

@[simp] lemma measure_Ioo {a b : ℝ} : f.measure (Ioo a b) = of_real (left_lim f b - f a) :=
begin
  rcases le_or_lt b a with hab|hab,
  { simp only [hab, measure_empty, Ioo_eq_empty, not_lt],
    symmetry,
    simp [ennreal.of_real_eq_zero, f.mono.left_lim_le hab] },
  { have A : disjoint (Ioo a b) {b}, by simp,
    have D : f b - f a = (f b - left_lim f b) + (left_lim f b - f a), by abel,
    have := f.measure_Ioc a b,
    simp only [←Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
      measure_union A (measurable_set_singleton b), Icc_self] at this,
    rw [D, ennreal.of_real_add, add_comm] at this,
    { simpa only [ennreal.add_right_inj ennreal.of_real_ne_top] },
    { simp only [f.mono.left_lim_le, sub_nonneg] },
    { simp only [f.mono.le_left_lim hab, sub_nonneg] } },
end

@[simp] lemma measure_Ico (a b : ℝ) : f.measure (Ico a b) = of_real (left_lim f b - left_lim f a) :=
begin
  rcases le_or_lt b a with hab|hab,
  { simp only [hab, measure_empty, Ico_eq_empty, not_lt],
    symmetry,
    simp [ennreal.of_real_eq_zero, f.mono.left_lim hab] },
  { have A : disjoint {a} (Ioo a b) := by simp,
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, hab.ne, f.mono.left_lim_le,
      measure_union A measurable_set_Ioo, f.mono.le_left_lim hab, ← ennreal.of_real_add] }
end

lemma measure_Iic {l : ℝ} (hf : tendsto f at_bot (𝓝 l)) (x : ℝ) :
  f.measure (Iic x) = of_real (f x - l) :=
begin
  refine tendsto_nhds_unique (tendsto_measure_Ioc_at_bot _ _) _,
  simp_rw measure_Ioc,
  exact ennreal.tendsto_of_real (tendsto.const_sub _ hf),
end

lemma measure_Ici {l : ℝ} (hf : tendsto f at_top (𝓝 l)) (x : ℝ) :
  f.measure (Ici x) = of_real (l - left_lim f x) :=
begin
  refine tendsto_nhds_unique (tendsto_measure_Ico_at_top _ _) _,
  simp_rw measure_Ico,
  refine ennreal.tendsto_of_real (tendsto.sub_const _ _),
  have h_le1 : ∀ x, f (x - 1) ≤ left_lim f x := λ x, monotone.le_left_lim f.mono (sub_one_lt x),
  have h_le2 : ∀ x, left_lim f x ≤ f x := λ x, monotone.left_lim_le f.mono le_rfl,
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hf.comp _) hf h_le1 h_le2,
  rw tendsto_at_top_at_top,
  exact λ y, ⟨y + 1, λ z hyz, by rwa le_sub_iff_add_le⟩,
end

lemma measure_univ {l u : ℝ} (hfl : tendsto f at_bot (𝓝 l)) (hfu : tendsto f at_top (𝓝 u)) :
  f.measure univ = of_real (u - l) :=
begin
  refine tendsto_nhds_unique (tendsto_measure_Iic_at_top _) _,
  simp_rw measure_Iic f hfl,
  exact ennreal.tendsto_of_real (tendsto.sub_const hfu _),
end

instance : is_locally_finite_measure f.measure :=
⟨λ x, ⟨Ioo (x-1) (x+1), Ioo_mem_nhds (by linarith) (by linarith), by simp⟩⟩

end stieltjes_function
