/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import geometry.manifold.cont_mdiff

/-! # Smooth vector bundles

This file will eventually contain the definition of a smooth vector bundle.  For now, it contains
preliminaries regarding an associated `structure_groupoid`, the groupoid of `smooth_fibrewise_linear`
functions. -/

noncomputable theory

open set topological_space
open_locale manifold topological_space

/-! ### The groupoid of smooth, fibrewise-linear maps -/

variables {𝕜 B F : Type*} [topological_space B]
variables [nontrivially_normed_field 𝕜] [normed_add_comm_group F] [normed_space 𝕜 F]

/-- For `B` a topological space and `F` a `𝕜`-normed space, a map from `U : set B` to `F ≃L[𝕜] F`
determines a local homeomorphism from `B × F` to itself by its action fibrewise. -/
def fiberwise_linear.local_homeomorph (φ : B → F ≃L[𝕜] F) {U : set B} (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U) :
  local_homeomorph (B × F) (B × F) :=
{ to_fun := λ x, (x.1, φ x.1 x.2),
  inv_fun := λ x, (x.1, (φ x.1).symm x.2),
  source := U ×ˢ univ,
  target := U ×ˢ univ,
  map_source' := λ x hx, mk_mem_prod hx.1 (mem_univ _),
  map_target' := λ x hx, mk_mem_prod hx.1 (mem_univ _),
  left_inv' := sorry,
  right_inv' := sorry,
  open_source := hU.prod is_open_univ,
  open_target := hU.prod is_open_univ,
  continuous_to_fun := sorry,
  continuous_inv_fun := sorry }

@[simp] lemma fiberwise_linear.source_local_homeomorph (φ : B → F ≃L[𝕜] F) {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U) (p : B × F) :
  fiberwise_linear.local_homeomorph φ hU hφ h2φ p = (p.1, φ p.1 p.2) :=
rfl

lemma fiberwise_linear.source_trans_local_homeomorph {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U') :
  (fiberwise_linear.local_homeomorph φ hU hφ h2φ ≫ₕ
      fiberwise_linear.local_homeomorph φ' hU' hφ' h2φ').source = (U ∩ U') ×ˢ univ :=
begin
  sorry,
end

lemma fiberwise_linear.trans_local_homeomorph_apply {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U')
  {b : B}
  (hb : b ∈ U ∩ U')
  (v : F) :
  (fiberwise_linear.local_homeomorph φ hU hφ h2φ ≫ₕ
      fiberwise_linear.local_homeomorph φ' hU' hφ' h2φ') ⟨b, v⟩ = ⟨b, φ' b (φ b v)⟩ :=
begin
  sorry,
end

variables {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] {IB : model_with_corners 𝕜 EB HB}
   [charted_space HB B] [smooth_manifold_with_corners IB B]

lemma smooth_fibrewise_linear.locality_aux' (e : local_homeomorph (B × F) (B × F))
  (U : set B) (hU : e.source = U ×ˢ univ)
  (h : ∀ x ∈ U, ∃ (φ : B → (F ≃L[𝕜] F)) (u : set B) (hu : is_open u) (huU : u ⊆ U) (hux : x ∈ u)
    (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x : F →L[𝕜] F)) u)
    (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((φ x).symm : F →L[𝕜] F)) u),
    (e.restr (u ×ˢ univ)).eq_on_source
      (fiberwise_linear.local_homeomorph φ hu hφ.continuous_on h2φ.continuous_on)) :
  ∃ (Φ : B → (F ≃L[𝕜] F)) (U : set B) (hU₀ : is_open U)
    (hΦ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (Φ x : F →L[𝕜] F)) U)
    (h2Φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((Φ x).symm : F →L[𝕜] F)) U),
    e.eq_on_source (fiberwise_linear.local_homeomorph Φ hU₀ hΦ.continuous_on h2Φ.continuous_on) :=
begin
  classical,
  rw set_coe.forall' at h,
  choose! φ u hu huU hux hφ h2φ heφ using h,
  have H₀' : ∀ x : U, eq_on e (λ q, (q.1, φ x q.1 q.2)) (u x ×ˢ univ),
  { intros x p hp,
    refine (heφ x).2 _,
    rw (heφ x).1,
    exact hp },
  have H₁ : ∀ (x x' : U) (y : B) (hyx : y ∈ u x) (hyx' : y ∈ u x'),
    φ x y = φ x' y,
  { intros p p' y hyp hyp',
    ext v,
    have h1 : e (y, v) = (y, φ p y v) := H₀' _ ⟨(id hyp : (y, v).fst ∈ u p), trivial⟩,
    have h2 : e (y, v) = (y, φ p' y v) := H₀' _ ⟨(id hyp' : (y, v).fst ∈ u p'), trivial⟩,
    exact congr_arg prod.snd (h1.symm.trans h2) },
  have H₃ : U = ⋃ i, u i,
  { ext x,
    rw mem_Union,
    refine ⟨λ h, ⟨⟨x, h⟩, hux _⟩, _⟩,
    rintros ⟨x, hx⟩,
    exact huU x hx },
  have hU₀ : is_open U,
  { rw H₃,
    apply is_open_Union hu },
  let Φ₀ : U → F ≃L[𝕜] F := Union_lift u (λ x, (φ x) ∘ coe) H₁ U H₃.le,
  let Φ : B → F ≃L[𝕜] F := λ y, if hy : y ∈ U then Φ₀ ⟨y, hy⟩ else continuous_linear_equiv.refl 𝕜 F,
  have hΦ : ∀ (y) (hy : y ∈ U), Φ y = Φ₀ ⟨y, hy⟩ := λ y hy, dif_pos hy,
  have hΦφ : ∀ x : U, ∀ y ∈ u x, Φ y = φ x y,
  { intros x y hyu,
    refine (hΦ y (huU x hyu)).trans _,
    exact Union_lift_mk ⟨y, hyu⟩ _ },
  have hΦ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ y, (Φ y : F →L[𝕜] F)) U,
  { apply cont_mdiff_on_of_locally_cont_mdiff_on,
    intros x hx,
    refine ⟨u ⟨x, hx⟩, hu ⟨x, hx⟩, hux _, _⟩,
    refine (cont_mdiff_on.congr (hφ ⟨x, hx⟩) _).mono (inter_subset_right _ _),
    intros y hy,
    rw hΦφ ⟨x, hx⟩ y hy },
  have h2Φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ y, ((Φ y).symm : F →L[𝕜] F)) U,
  { sorry },
  have heΦ : e.eq_on_source (fiberwise_linear.local_homeomorph Φ hU₀ hΦ.continuous_on h2Φ.continuous_on),
  { refine ⟨hU, _⟩,
    intros p hp,
    rw [hU] at hp,
    rw H₀' ⟨p.fst, hp.1⟩ ⟨hux _, hp.2⟩,
    congrm (_, _),
    rw hΦφ,
    exact hux _ },
  exact ⟨Φ, U, hU₀, hΦ, h2Φ, heΦ⟩,
end

lemma smooth_fibrewise_linear.locality_aux (e : local_homeomorph (B × F) (B × F))
  (h : ∀ p ∈ e.source, ∃ s : set (B × F), is_open s ∧ p ∈ s ∧
    ∃ (φ : B → (F ≃L[𝕜] F)) (u : set B) (hu : is_open u)
      (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x : F →L[𝕜] F)) u)
      (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((φ x).symm : F →L[𝕜] F)) u),
      (e.restr s).eq_on_source
            (fiberwise_linear.local_homeomorph φ hu hφ.continuous_on h2φ.continuous_on)) :
  ∃ (U : set B) (hU : e.source = U ×ˢ univ),
  ∀ x ∈ U, ∃ (φ : B → (F ≃L[𝕜] F)) (u : set B) (hu : is_open u) (huU : u ⊆ U) (hux : x ∈ u)
    (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x : F →L[𝕜] F)) u)
    (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, ((φ x).symm : F →L[𝕜] F)) u),
    (e.restr (u ×ˢ univ)).eq_on_source
      (fiberwise_linear.local_homeomorph φ hu hφ.continuous_on h2φ.continuous_on) :=
begin
  rw set_coe.forall' at h,
  choose! s hs hsp φ u hu hφ h2φ heφ using h,
  have H₀ : ∀ p : e.source, e.source ∩ s p = u p ×ˢ univ,
  { intros p,
    rw ← e.restr_source' (s _) (hs _),
    exact (heφ p).1 },
  have hesu : ∀ (p) (hp : p ∈ e.source), e.source ∩ s ⟨p, hp⟩ = u ⟨p, hp⟩ ×ˢ univ := λ p hp, H₀ ⟨p, hp⟩,
  have H₀'' : ∀ p : e.source, (p : B × F).fst ∈ u p,
  { intros p,
    suffices : (p : B × F) ∈ (u p : set B) ×ˢ (univ : set F),
    { simpa only [mem_prod, mem_univ, and_true] using this },
    rw ← H₀,
    exact ⟨p.prop, hsp p⟩ },
  have H₂ : ∀ p : e.source, ∀ q : B × F, q.fst ∈ u p → q ∈ e.source,
  { intros p q hq,
    have : q ∈ u p ×ˢ (univ : set F) := ⟨hq, trivial⟩,
    rw ← H₀ p at this,
    exact this.1 },
  have H₁ : e.source = (prod.fst '' e.source) ×ˢ (univ : set F),
  { apply has_subset.subset.antisymm,
    { intros p hp,
      exact ⟨⟨p, hp, rfl⟩, trivial⟩ },
    { rintros ⟨x, v⟩ ⟨⟨p, hp : p ∈ e.source, rfl : p.fst = x⟩, -⟩,
      exact H₂ ⟨p, hp⟩ (p.fst, v) (H₀'' ⟨p, hp⟩) } },
  refine ⟨prod.fst '' e.source, H₁, _⟩,
  rintros x ⟨p, hp, rfl⟩,
  refine ⟨φ ⟨p, hp⟩, u ⟨p, hp⟩, hu ⟨p, hp⟩, _, H₀'' _, hφ ⟨p, hp⟩, h2φ ⟨p, hp⟩, _⟩,
  { intros y hy,
    refine ⟨(y, 0), H₂ ⟨p, hp⟩ _ _, rfl⟩,
    exact hy },
  { rw ← hesu,
    rw e.restr_source_inter,
    exact heφ ⟨p, hp⟩ },
end

variables (F B IB)

/-- For `B` a manifold and `F` a normed space, the groupoid on `B × F` consisting of local
homeomorphisms which are bi-smooth and fibrewise linear. -/
def smooth_fiberwise_linear : structure_groupoid (B × F) :=
{ members := ⋃ (φ : B → F ≃L[𝕜] F) (U : set B) (hU : is_open U)
  (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x).symm : B → F →L[𝕜] F) U),
  {e | e.eq_on_source (fiberwise_linear.local_homeomorph φ hU hφ.continuous_on h2φ.continuous_on)},
  trans' := begin
    simp_rw [mem_Union],
    rintros e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ ⟨φ', U', hU', hφ', h2φ', heφ'⟩,
    refine ⟨λ b, (φ b).trans (φ' b), _, hU.inter hU', _, _, setoid.trans (heφ.trans' heφ') ⟨_, _⟩⟩,
    { sorry },
    { sorry }, -- two smoothness checks
    { apply fiberwise_linear.source_trans_local_homeomorph },
    { rintros ⟨b, v⟩ hb,
      apply fiberwise_linear.trans_local_homeomorph_apply,
      rw fiberwise_linear.source_trans_local_homeomorph at hb,
      simpa [-mem_inter] using hb }
  end,
  symm' := begin
    simp_rw [mem_Union],
    rintros e ⟨φ, U, hU, hφ, h2φ, heφ⟩,
    refine ⟨λ b, (φ b).symm, U, hU, h2φ, _, heφ.symm'⟩,
    simp_rw continuous_linear_equiv.symm_symm,
    exact hφ
  end,
  id_mem' := begin
    simp_rw [mem_Union],
    refine ⟨λ b, continuous_linear_equiv.refl 𝕜 F, univ, is_open_univ, _, _, ⟨_, λ b hb, _⟩⟩,
    { apply cont_mdiff_on_const },
    { apply cont_mdiff_on_const },
    { simp [fiberwise_linear.local_homeomorph] },
    { simp [fiberwise_linear.local_homeomorph] },
  end,
  locality' := begin -- a bit tricky, need to glue together a family of `φ`
    simp_rw [mem_Union],
    intros e he,
    obtain ⟨U, hU, h⟩ := smooth_fibrewise_linear.locality_aux e he,
    exact smooth_fibrewise_linear.locality_aux' e U hU h,
  end,
  eq_on_source' := begin
    simp_rw [mem_Union],
    rintros e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ hee',
    exact ⟨φ, U, hU, hφ, h2φ, setoid.trans hee' heφ⟩,
  end }
