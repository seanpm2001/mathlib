import number_theory.general_bernoullli_number_properties_three
import number_theory.teich_char
import topology.algebra.nonarchimedean.bases

open_locale big_operators
local attribute [instance] zmod.topological_space

open filter
open_locale topological_space

open_locale big_operators

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : weight_space (units (zmod d) × units ℤ_[p]) R)

variable [fact (0 < d)]
variables [complete_space R] [char_zero R]

/-- Gives the equivalence (ℤ/(m * n)ℤ)ˣ ≃* (ℤ/mℤ)ˣ × (ℤ/nℤ)ˣ -/
-- It would be nice to use units.homeomorph.prod_units instead, however no way to identify it as a mul_equiv.
abbreviation units.chinese_remainder {m n : ℕ} (h : m.coprime n) :
  (zmod (m * n))ˣ ≃* (zmod m)ˣ × (zmod n)ˣ :=
mul_equiv.trans (units.map_equiv (zmod.chinese_remainder h).to_mul_equiv) mul_equiv.prod_units

lemma h1 (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :
  filter.tendsto f.comp (nhds ((continuous_map.id (zmod d)ˣ).prod_map
    (continuous_map.id ℤ_[p]ˣ))) (nhds f) :=
begin
  convert_to filter.tendsto f.comp (nhds (continuous_map.id _)) (nhds f),
  { congr, ext a,
    { congr, },
    { simp only [continuous_map.id_apply], rw units.ext_iff, congr, }, },
  { delta filter.tendsto, delta filter.map, rw filter.le_def,
    intros x hx, simp,
    rw mem_nhds_iff at *,
    rcases hx with ⟨s, hs, h1, h2⟩,
    refine ⟨f.comp ⁻¹' s, _, _, _⟩,
    { intros a ha,
      rw set.mem_preimage at *,
      apply hs ha, },
    { refine is_open.preimage _ h1, exact continuous_map.continuous_comp f, },
    { rw set.mem_preimage, rw continuous_map.comp_id, apply h2, }, },
end

open continuous_map

private lemma preimage_gen {α β γ : Type*} [topological_space α] [topological_space β]
  [topological_space γ] (g : C(β, γ)) {s : set α} (hs : is_compact s) {u : set γ} (hu : is_open u) :
  continuous_map.comp g ⁻¹' (compact_open.gen s u) = compact_open.gen s (g ⁻¹' u) :=
begin
  ext ⟨f, _⟩,
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u,
  rw [set.image_comp, set.image_subset_iff]
end

lemma helper_char (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (g : ℕ → C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ))
  (h : filter.tendsto (λ j : ℕ, g j) filter.at_top (nhds (continuous_map.id _))) :
  filter.tendsto (λ j : ℕ, continuous_map.comp f (g j)) filter.at_top (nhds f) :=
begin
  apply topological_space.tendsto_nhds_generate_from,
  simp only [exists_prop, set.mem_set_of_eq, filter.mem_at_top_sets, ge_iff_le, set.mem_preimage, forall_exists_index, and_imp],
  simp_rw [← @set.mem_preimage _ _ f.comp _ _],
  rintros s t compt a opena hs mems,
  simp_rw [hs, preimage_gen _ compt opena],
  rw tendsto_nhds at h, simp only [filter.mem_at_top_sets, ge_iff_le, set.mem_preimage] at h,
  apply h,
  { apply continuous_map.is_open_gen compt (continuous.is_open_preimage (map_continuous _) _ opena), },
  { rw ← preimage_gen _ compt opena, rw set.mem_preimage, rw comp_id, rw ← hs, apply mems, },
end

/-lemma fn_eq_sum_char_fn [normed_algebra ℚ R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) : filter.tendsto
  (λ j : ℕ, ∑ a : (zmod (d * (p^j)))ˣ, (f (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) a)))  : C((zmod d)ˣ × ℤ_[p]ˣ, R)))
  (filter.at_top) (nhds f) := sorry-/
.
lemma integral_loc_const_eval [normed_algebra ℚ R] [norm_one_class R]
  (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  measure.integral (bernoulli_measure' p d R hc hc' hd na) f =
  (bernoulli_measure' p d R hc hc' hd na).val f :=
begin
  delta measure.integral, simp,
  convert dense_inducing.extend_eq (measure.dense_ind_inclusion _ _) (measure.integral_cont _) _,
  apply_instance,
  apply_instance,
  apply_instance,
end

lemma trying [normed_algebra ℚ R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R))
  (i : ℕ → locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)
  (hf : filter.tendsto (λ j : ℕ, (i j : C((zmod d)ˣ × ℤ_[p]ˣ, R))) (filter.at_top) (nhds f)) :
  filter.tendsto (λ j : ℕ, (bernoulli_measure' p d R hc hc' hd na).1 (i j)) (filter.at_top)
  (nhds (measure.integral (bernoulli_measure' p d R hc hc' hd na) f)) :=
begin
  convert filter.tendsto.comp (continuous.tendsto (continuous_linear_map.continuous (measure.integral
     (bernoulli_measure' p d R hc hc' hd na) )) f) hf,
  ext,
  simp,
  rw integral_loc_const_eval, simp,
end

lemma locally_constant.to_continuous_map_smul (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) (r : R) :
  ((r • f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R)) =
  r • (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :=
begin
  ext,
  simp only [locally_constant.coe_continuous_map, locally_constant.coe_smul,
    continuous_map.coe_smul],
end

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]

-- this is the difficult simp
lemma mul_equiv.prod_units.coe_symm_apply {M : Type*} {N : Type*} [monoid M] [monoid N]
  (a : Mˣ) (b : Nˣ) : (mul_equiv.prod_units.symm (a, b) : M × N) = (a, b) :=
by { delta mul_equiv.prod_units, simp }

lemma prod.eq_fst_snd {α β : Type*} (a : α × β) : a = (a.fst, a.snd) := by refine prod.ext rfl rfl

lemma ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun {R S : Type*} [semiring R] [semiring S]
  (h : R ≃+* S) : (h : R ≃* S).inv_fun = h.inv_fun := by { ext, solve_by_elim }

lemma units.chinese_remainder_symm_apply_fst {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm a : zmod (d * (p^n))) : zmod d) =
  (a.fst : zmod d) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime_pow_spl p d n hd)),
  change (zmod.cast_hom (dvd_mul_right d (p^n)) (zmod d))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.fst),
  rw proj_fst',
end

lemma units.chinese_remainder_symm_apply_snd {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm a : zmod (d * (p^n))) : zmod (p^n)) =
  (a.snd : zmod (p^n)) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime_pow_spl p d n hd)),
  change (zmod.cast_hom (dvd_mul_left (p^n) d) (zmod (p^n)))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.snd),
  rw proj_snd',
end

lemma padic_int.is_unit_to_zmod_pow_of_is_unit (n : ℕ) (hn : 1 < n) (x : ℤ_[p])
  (hx : is_unit (padic_int.to_zmod_pow n x)) : is_unit x :=
begin
  rw padic_int.is_unit_iff,
  by_contra h,
  have hx' := lt_of_le_of_ne (padic_int.norm_le_one _) h,
  rw padic_int.norm_lt_one_iff_dvd at hx',
  cases hx' with y hy,
  rw hy at hx,
  rw ring_hom.map_mul at hx,
  rw is_unit.mul_iff at hx,
  simp only [map_nat_cast] at hx,
  have : ¬ is_unit (p : zmod (p^n)),
  { intro h,
    set q : (zmod (p^n))ˣ := is_unit.unit h,
    have := zmod.val_coe_unit_coprime q,
    rw is_unit.unit_spec at this,
    rw nat.coprime_pow_right_iff (lt_trans zero_lt_one hn) at this,
    rw zmod.val_cast_of_lt _ at this,
    simp only [nat.coprime_self] at this,
    apply @nat.prime.ne_one p (fact.out _),
    rw this,
    conv { congr, rw ← pow_one p, },
    rw pow_lt_pow_iff _, apply hn,
    apply nat.prime.one_lt (fact.out _),
    apply_instance, },
  apply this, apply hx.1,
end

lemma helper_289 {n : ℕ} (hn : 1 < n) (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  loc_const_ind_fn R p d (locally_constant.char_fn R (is_clopen_units_clopen_from p d n a)) =
  locally_constant.char_fn R (is_clopen_clopen_from p d n (↑(((units.chinese_remainder
  (nat.coprime_pow_spl p d n hd)).symm) a))) :=
begin
  ext,
  rw loc_const_ind_fn, rw ← locally_constant.to_fun_eq_coe,
  simp only, rw ind_fn, simp only, split_ifs,
  { by_cases hx : x ∈ clopen_from p d n ↑(((units.chinese_remainder
      (nat.coprime_pow_spl p d n hd)).symm) a),
    { rw (locally_constant.char_fn_one R x _).1 hx, rw ← locally_constant.char_fn_one R _ _,
      rw set.mem_prod, rw set.mem_preimage, rw set.mem_singleton_iff, rw set.mem_singleton_iff,
      rw units.ext_iff, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, rw mem_clopen_from at hx, rw hx.1, rw ring_hom.to_monoid_hom_eq_coe,
      rw ring_hom.coe_monoid_hom, rw ← hx.2, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd, refine ⟨rfl, rfl⟩, },
    { rw (locally_constant.char_fn_zero R x _).1 hx, rw ← locally_constant.char_fn_zero R _ _,
      -- this should be a separate lemma mem_units_clopen_from
      rw set.mem_prod, rw set.mem_preimage, rw set.mem_singleton_iff, rw set.mem_singleton_iff,
      rw units.ext_iff, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, intro h', apply hx, rw mem_clopen_from, rw h'.1,
      rw ring_hom.to_monoid_hom_eq_coe at h', rw ring_hom.coe_monoid_hom at h',
      rw h'.2, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd, refine ⟨rfl, rfl⟩, }, },
  rw (locally_constant.char_fn_zero R x _).1 _,
  rw mem_clopen_from, intro h', apply h, rw units.chinese_remainder_symm_apply_fst at h',
  rw units.chinese_remainder_symm_apply_snd at h', split,
  { rw h'.1, apply units.is_unit _, },
  { apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn x.snd, rw ← h'.2, apply units.is_unit _, },
end

variable [fact (0 < d)]

lemma ring_equiv.eq_inv_fun_iff {α β : Type*} [semiring α] [semiring β] (h : α ≃+* β) (x : β) (y : α) :
  y = h.inv_fun x ↔ h y = x := ⟨λ h, by simp only [h, ring_equiv.inv_fun_eq_symm,
    ring_equiv.apply_symm_apply], λ h, by { rw [ring_equiv.inv_fun_eq_symm, ← h,
    ring_equiv.symm_apply_apply], }⟩

lemma proj_fst'' {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : zmod d) = a.fst :=
proj_fst' _ _ _ _ _

lemma proj_snd'' {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
(padic_int.to_zmod_pow n) ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : ℤ_[p]) = a.snd :=
begin
  rw ← zmod.int_cast_cast,
  rw ring_hom.map_int_cast,
  rw zmod.int_cast_cast, convert proj_snd' _ _ _ _ _,
end

lemma bernoulli_measure'_eval_char_fn [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (bernoulli_measure' p d R hc hc' hd na).val (locally_constant.char_fn R
  (is_clopen_units_clopen_from p d n a)) =
  (algebra_map ℚ R (E_c p d hc n ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
  ((a.1 : zmod d), (a.2 : zmod (p^n))))) ) :=
begin
  delta bernoulli_measure', simp only [linear_map.coe_mk, ring_equiv.inv_fun_eq_symm],
  delta bernoulli_distribution, simp only [linear_map.coe_mk],
  rw sequence_limit_eq _ n _,
  { delta g, simp only [algebra.id.smul_eq_mul],
    convert finset.sum_eq_single_of_mem _ _ (λ b memb hb, _),
    swap 2, { refine ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
      ((a.1 : zmod d), (a.2 : zmod (p^n)))), },
    { conv_lhs { rw ← one_mul ((algebra_map ℚ R)
        (E_c p d hc n (((zmod.chinese_remainder _).symm) (↑(a.fst), ↑(a.snd))))), },
      congr,
      rw loc_const_ind_fn, simp only [ring_equiv.inv_fun_eq_symm, locally_constant.coe_mk],
      rw ind_fn, simp only, rw dif_pos _,
      { symmetry, rw ← locally_constant.char_fn_one, rw set.mem_prod,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, set.mem_singleton_iff,
          ring_hom.to_monoid_hom_eq_coe, set.mem_preimage],
        rw units.ext_iff, rw units.ext_iff,
        rw is_unit.unit_spec, rw units.coe_map, rw is_unit.unit_spec,
        rw ← ring_equiv.inv_fun_eq_symm,
        rw proj_fst'', rw ring_hom.coe_monoid_hom (@padic_int.to_zmod_pow p _ n),
        rw proj_snd'', simp only [eq_self_iff_true, and_self], },
      { rw ← ring_equiv.inv_fun_eq_symm,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast],
        split,
        { rw proj_fst'', apply units.is_unit, },
        { apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn,
          rw proj_snd'', apply units.is_unit, }, }, },
    { delta zmod', apply finset.mem_univ, },
    { rw mul_eq_zero_of_left _, rw helper_289 p d R hd hn a,
      rw ← locally_constant.char_fn_zero R _ _, rw mem_clopen_from, intro h, apply hb,
      rw units.chinese_remainder_symm_apply_snd at h,
      rw units.chinese_remainder_symm_apply_fst at h,
      rw h.2, rw ← h.1,
      rw ring_equiv.eq_inv_fun_iff, rw ← ring_equiv.coe_to_equiv,
      change (zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).to_equiv b = _,
      rw prod.ext_iff, rw inv_fst', rw inv_snd',
      simp only [prod.fst_zmod_cast, eq_self_iff_true, prod.snd_zmod_cast, true_and],
      conv_rhs { rw ← zmod.int_cast_cast, }, rw ring_hom.map_int_cast,
      rw zmod.int_cast_cast, }, },
  { convert seq_lim_g_char_fn p d R n
      ((units.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm a : zmod (d * p^n)) hc hc' hd _,
    { apply helper_289 p d R hd hn a, },
    { apply fact.out _, apply_instance, }, },
end

lemma nat_spec' (p : ℕ → Prop) (h : ({n : ℕ | ∀ (x : ℕ), x ≥ n → p x}).nonempty) (x : ℕ)
  (hx : x ≥ Inf {n : ℕ | ∀ (x : ℕ) (hx : x ≥ n), p x}) : p x := nat.Inf_mem h x hx

noncomputable def U_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
  ∑ (x : (zmod (d * p ^ k))ˣ),
  ((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) x : R) *
  ((((x : zmod (d * p^k))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (int.fract (↑x / (↑d * ↑p ^ k)))
-- Idea 1 : replacing k by m + k so we can remove (hk : m ≤ k)
-- Idea 2 : Use `asso_dirichlet_character` instead to get rid of hk, since coercion on non-units
-- can be anywhere

lemma finset.sum_equiv' {s t α : Type*} [fintype s] [fintype t] [add_comm_monoid α] (h : s ≃ t)
  (f : t → α) : ∑ (x : t), f x = ∑ (x : s), f (h x) :=
begin
  apply finset.sum_bij,
  swap 5, { rintros, refine h.inv_fun a, },
  { rintros, apply finset.mem_univ _, },
  { simp only [equiv.inv_fun_as_coe, equiv.apply_symm_apply, eq_self_iff_true, implies_true_iff], },
  { simp only [equiv.inv_fun_as_coe, embedding_like.apply_eq_iff_eq, imp_self, forall_2_true_iff], },
  { refine λ a ha, ⟨h a, finset.mem_univ _, _⟩,
    simp only [equiv.inv_fun_as_coe, equiv.symm_apply_apply], },
end

lemma finset.sum_equiv {s t α : Type*} [fintype s] [fintype t] [add_comm_monoid α] (h : s ≃ t)
  (f : s → α) : ∑ (x : s), f x = ∑ (x : t), f (h.inv_fun x) :=
begin
  rw finset.sum_equiv' h, simp,
end

noncomputable def units.equiv_is_unit {α : Type*} [monoid α] : units α ≃ {x : α // is_unit x} :=
{ to_fun := λ u, ⟨u, units.is_unit u⟩,
  inv_fun := λ ⟨u, hu⟩, is_unit.unit hu,
  left_inv := λ x, units.ext_iff.2 (is_unit.unit_spec _),
  right_inv := λ x, by { apply subtype.ext_val, tidy, }, }

/-noncomputable def zmod.units_equiv_coprime' {n : ℕ} [fact (0 < n)] :
  units (zmod n) ≃ {x : ℕ // x < n ∧ x.coprime n} :=
{ to_fun := λ u, ⟨(u : zmod n).val, ⟨zmod.val_lt _, zmod.val_coe_unit_coprime _⟩ ⟩,
  inv_fun := λ x, zmod.unit_of_coprime _ x.2.2,
  left_inv := begin rw function.left_inverse, sorry, end,
  right_inv := sorry, }-/

instance zmod.units_fintype (n : ℕ) : fintype (zmod n)ˣ :=
begin
  by_cases n = 0,
  { rw h, refine units_int.fintype, },
  { haveI : fact (0 < n),
    { apply fact_iff.2, apply nat.pos_of_ne_zero h, },
    apply_instance, },
end

-- not needed?
lemma set.finite_of_finite_inter {α : Type*} (s : finset α) (t : set α) :
  set.finite ((s : set α) ∩ t : set α) := set.finite.inter_of_left (finset.finite_to_set s) t

lemma sum_units_eq {x : ℕ} (hx : 0 < x) (f : ℕ → R) :
  ∑ (i : units (zmod (d * p^x))), f (i : zmod (d * p^x)).val =
  ∑ i in set.finite.to_finset (set.finite_of_finite_inter (finset.range (d * p^x))
  ({x | x.coprime d} ∩ {x | x.coprime p})), f i :=
begin
  apply finset.sum_bij,
  swap 5, { refine λ a ha, (a : zmod (d * p^x)).val, },
  { intros a ha,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq],
    refine ⟨zmod.val_lt _, _⟩,
    set b := zmod.units_equiv_coprime a,
    have := nat.coprime_mul_iff_right.1 b.2,
    rw nat.coprime_pow_right_iff hx at this,
    apply this, },
  { intros a ha, refl, },
  { intros a₁ a₂ ha₁ ha₂ h,
    haveI : fact (0 < d * p^x) := imp p d x,
    rw units.ext_iff, rw zmod.val_injective _ h, },
  { intros b hb,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at hb,
    refine ⟨zmod.units_equiv_coprime.inv_fun ⟨b, (zmod.val_cast_of_lt hb.1).symm ▸
      (nat.coprime.mul_right hb.2.1 (nat.coprime.pow_right _ hb.2.2)) ⟩, finset.mem_univ _, _⟩,
    rw zmod.units_equiv_coprime,
    simp only [zmod.coe_unit_of_coprime, zmod.nat_cast_val, zmod.cast_nat_cast'],
    rw zmod.val_cast_of_lt hb.1, },
end

lemma dirichlet_character.mul_eq_mul {n : ℕ} (χ ψ : dirichlet_character R n) {a : ℕ}
  (ha : is_unit (a : zmod n)) :
  asso_dirichlet_character (χ.mul ψ) a = asso_dirichlet_character (χ * ψ) a :=
begin
  delta dirichlet_character.mul,
  have lcm_eq_self : lcm n n = n := nat.lcm_self n,
  have h1 := classical.some_spec ((χ.change_level (dvd_lcm_left n n) * ψ.change_level
    (dvd_lcm_right n n)).factors_through_conductor).ind_char,
  have h2 := congr_arg asso_dirichlet_character h1,
  rw monoid_hom.ext_iff at h2, specialize h2 a,
  have h : is_unit (a : zmod (lcm n n)),
  { convert ha, }, -- lcm_eq_self ▸ ha does not work
  rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ _ h at h2,
  rw zmod.cast_nat_cast (dirichlet_character.conductor_dvd ((χ.change_level (dvd_lcm_left n n) *
    ψ.change_level (dvd_lcm_right n n)))) at h2,
  delta dirichlet_character.asso_primitive_character,
  rw ← h2,
  rw dirichlet_character.asso_dirichlet_character_mul,
  rw dirichlet_character.asso_dirichlet_character_mul, rw monoid_hom.mul_apply,
  rw monoid_hom.mul_apply,
  rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ _ h,
  rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ _ h,
  rw zmod.cast_nat_cast (dvd_lcm_left n n) a,
  any_goals { refine zmod.char_p _, },
end

lemma nat.prime_dvd_of_not_coprime {n : ℕ} (h : ¬ n.coprime p) : p ∣ n :=
begin
  have := @nat.coprime_or_dvd_of_prime p (fact.out _) n,
  cases this,
  { exfalso, apply h this.symm, },
  { assumption, },
end

lemma helper_U_3' [normed_algebra ℚ R] [norm_one_class R] {n : ℕ} (hn : 1 < n) (x : ℕ) :
  ∑ (x_1 : ℕ) in finset.range (d * p ^ x), (1 / ↑(d * p ^ x : ℕ) : ℚ) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) (↑p * ↑x_1) *
  (↑p ^ (n - 1) * ↑x_1 ^ n)) = ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) :=
begin
  symmetry,
  apply finset.sum_bij,
  swap 5, { refine λ a ha, _,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at ha,
    refine classical.some (nat.prime_dvd_of_not_coprime p ha.2), },
  { intros a ha,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at ha,
    simp only [finset.mem_range],
    apply lt_of_mul_lt_mul_right', swap, { exact p, },
    rw mul_assoc, rw ← pow_succ', rw mul_comm,
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2), apply ha.1, },
  { intros a ha,
    have h1 : ∀ x : ℕ, ((d * p^x : ℕ) : ℚ) ≠ 0 := λ x, nat.cast_ne_zero.2 (ne_zero_of_lt (mul_prime_pow_pos p d x)),
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at ha,
    simp_rw [← nat.cast_pow, ← nat.cast_mul],
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2),
    rw ← mul_smul_comm, rw smul_eq_mul, rw mul_assoc, congr,
    rw ← algebra_map_smul R, rw smul_eq_mul,
    conv_rhs { congr, skip, congr, congr, skip, rw ← nat.succ_pred_eq_of_pos
      (lt_trans zero_lt_one hn), rw pow_succ', },
    rw ← mul_assoc (p ^ (n - 1)) _ _, rw nat.pred_eq_sub_one, rw ← mul_pow,
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2), rw nat.cast_mul (a ^ (n - 1)) _,
    rw mul_comm ((algebra_map ℚ R) (1 / ↑(d * p ^ x))) _,
    rw mul_assoc, congr, rw ← map_nat_cast (algebra_map ℚ R), rw ← ring_hom.map_mul,
    apply congr_arg, rw mul_one_div, rw div_eq_div_iff (h1 _) (h1 _), norm_cast,
    rw mul_comm _ (d * p^x.succ),
    conv_rhs { congr, congr, skip, rw nat.succ_eq_add_one x, rw pow_succ' p x, },
    rw ← mul_assoc d _ _, rw mul_assoc (d * p^x) _ _,
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2), rw mul_comm _ a,
    { apply_instance, }, },
  { intros a b ha hb h,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at ha,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at hb,
    have h2 : p * (classical.some (nat.prime_dvd_of_not_coprime p ha.2)) =
      p * (classical.some (nat.prime_dvd_of_not_coprime p hb.2)),
    { congr, apply h, },
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2) at h2,
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p hb.2) at h2, rw h2, },
  { intros b hb, refine ⟨p * b, _, _⟩,
    { simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
        set.mem_set_of_eq], split,
      { rw mul_comm p, rw pow_succ', rw ← mul_assoc,
        apply nat.mul_lt_mul (finset.mem_range.1 hb) le_rfl (nat.prime.pos (fact.out _)),
        apply_instance, },
      { rw nat.prime.not_coprime_iff_dvd, refine ⟨p, fact.out _, dvd_mul_right p b, dvd_rfl⟩, }, },
    { apply nat.eq_of_mul_eq_mul_left (nat.prime.pos (fact.out _)) _,
      { exact p, },
      { apply_instance, },
      { rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p _), }, }, },
end

lemma helper_U_2' [no_zero_divisors R] [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1)) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))) :=
begin
  conv { congr, funext, rw ← helper_U_3' p d R m χ hn, },
  apply (tendsto_congr _).1 (tendsto.const_mul ((asso_dirichlet_character
    (dirichlet_character.mul χ ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1)))
    (lim_even_character d p m χ na hn hχ hp)),
  intro x, rw mul_smul_comm, rw finset.mul_sum, rw finset.smul_sum,
  apply finset.sum_congr rfl,
  intros x hx, rw monoid_hom.map_mul, apply congr_arg, ring,
end

lemma helper_U_1' [no_zero_divisors R] [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))) :=
begin
  have h1 := helper_U_2' p d R m χ n hn hχ hp na,
  have h2 : tendsto nat.pred at_top at_top,
  { rw tendsto_at_top, intro b, simp, refine ⟨b.succ, λ c hc, _⟩,
    rw nat.pred_eq_sub_one,
    apply (nat.add_le_to_le_sub _ _).1 _,
    { apply le_trans (nat.one_le_iff_ne_zero.2 (nat.succ_ne_zero _)) hc, },
    { apply hc, }, },
  have h3 : function.comp (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) ) nat.pred =ᶠ[at_top] (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) ),
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨1, λ x hx, _⟩, rw function.comp_apply,
    rw nat.succ_pred_eq_of_pos (nat.succ_le_iff.1 hx), },
  apply (tendsto_congr' h3).1 _, clear h3,
  apply tendsto.comp h1 h2,
end

lemma ring_equiv.coe_eq_to_equiv {S T : Type*} [semiring S] [semiring T] (f : S ≃+* T) :
  f.to_equiv = f := by { ext, simp }

lemma inv_fst (m n : ℕ) (x : zmod (m * n)) (cop : m.coprime n) :
  (((zmod.chinese_remainder cop).to_equiv) x).fst = (x : zmod m) :=
begin
  rw ←zmod.cast_hom_apply x,
  swap 3, { apply zmod.char_p _, },
  swap, { apply dvd_mul_right, },
  { conv_rhs { rw ←(zmod.chinese_remainder cop).left_inv x, },
    change _ = (zmod.cast_hom _ (zmod m)) ((zmod.chinese_remainder cop).inv_fun
      (((zmod.chinese_remainder cop).to_fun x).fst, ((zmod.chinese_remainder cop).to_fun x).snd)),
    rw proj_fst',
    congr, },
end

lemma inv_snd (m n : ℕ) (x : zmod (m * n)) (cop : m.coprime n) :
  (((zmod.chinese_remainder cop).to_equiv) x).snd = (x : zmod n) :=
begin
  rw ←zmod.cast_hom_apply x,
  swap 3, { apply zmod.char_p _, },
  swap, { apply dvd_mul_left, },
  { conv_rhs { rw ←(zmod.chinese_remainder cop).left_inv x, },
    change _ = (zmod.cast_hom _ (zmod n)) ((zmod.chinese_remainder cop).inv_fun
      (((zmod.chinese_remainder cop).to_fun x).fst, ((zmod.chinese_remainder cop).to_fun x).snd)),
    rw proj_snd',
    congr, },
end

lemma chinese_remainder_comp_prod_units {m n x : ℕ} (χ : dirichlet_character R (m * n))
  (h : m.coprime n) (h1 : is_unit (x : zmod m)) (h2 : is_unit (x : zmod n)) :
  (x : zmod (m * n)) = ((zmod.chinese_remainder h).symm.to_monoid_hom)
    (((mul_equiv.symm (@mul_equiv.prod_units _ _ _ _))) (h1.unit, h2.unit)) :=
--  ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm.to_monoid_hom)
--  (((@mul_equiv.prod_units (zmod d) (zmod (p^n)) _ _).symm.to_monoid_hom) (h1.unit, h2.unit)  : zmod (d * p^n)) :=
  --(((@mul_equiv.prod_units (zmod d) (zmod (p^n)) _ _).symm.to_monoid_hom) (h1.unit, h2.unit) : zmod (d * p^n)) :=
begin
  delta mul_equiv.prod_units, simp, -- wont squeeze
  rw is_unit.unit_spec, rw is_unit.unit_spec,
  delta ring_equiv.to_monoid_hom, rw ring_hom.to_monoid_hom_eq_coe,
  rw ring_equiv.to_ring_hom_eq_coe, rw ring_hom.coe_monoid_hom, rw ring_equiv.coe_to_ring_hom,
  rw ← ring_equiv.symm_apply_apply (zmod.chinese_remainder h) (x : zmod (m * n)),
  apply congr_arg, rw ← ring_equiv.coe_to_equiv, rw ← ring_equiv.coe_eq_to_equiv, apply prod.ext _ _,
  { rw inv_fst, rw zmod.cast_nat_cast (dvd_mul_right m n), refine zmod.char_p _, },
  { rw inv_snd, rw zmod.cast_nat_cast (dvd_mul_left n m), refine zmod.char_p _, },
end
.

lemma chinese_remainder_comp_prod_units' {n x : ℕ} (χ : dirichlet_character R (d * p^n))
  (h : d.coprime (p^n)) (h1 : is_unit (x : zmod d)) (h2 : is_unit (x : zmod (p^n))) :
  (x : zmod (d * p^n)) = ((zmod.chinese_remainder h).symm.to_monoid_hom)
    (((mul_equiv.symm (@mul_equiv.prod_units _ _ _ _))) (h1.unit, h2.unit)) :=
--  ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm.to_monoid_hom)
--  (((@mul_equiv.prod_units (zmod d) (zmod (p^n)) _ _).symm.to_monoid_hom) (h1.unit, h2.unit)  : zmod (d * p^n)) :=
  --(((@mul_equiv.prod_units (zmod d) (zmod (p^n)) _ _).symm.to_monoid_hom) (h1.unit, h2.unit) : zmod (d * p^n)) :=
begin
  delta mul_equiv.prod_units, simp, -- wont squeeze
  rw is_unit.unit_spec, rw is_unit.unit_spec,
  delta ring_equiv.to_monoid_hom, rw ring_hom.to_monoid_hom_eq_coe,
  rw ring_equiv.to_ring_hom_eq_coe, rw ring_hom.coe_monoid_hom, rw ring_equiv.coe_to_ring_hom,
  rw ← ring_equiv.symm_apply_apply (zmod.chinese_remainder h) (x : zmod (d * p^n)),
  apply congr_arg, rw ← ring_equiv.coe_to_equiv, rw ← ring_equiv.coe_eq_to_equiv, apply prod.ext _ _,
  { rw inv_fst', rw zmod.cast_nat_cast (dvd_mul_right d (p^n)), refine zmod.char_p _, },
  { rw inv_snd', rw zmod.cast_nat_cast (dvd_mul_left (p^n) d), refine zmod.char_p _, },
end

lemma is_unit_of_is_unit_mul {m n : ℕ} (x : ℕ) (hx : is_unit (x : zmod (m * n))) :
  is_unit (x : zmod m) :=
begin
  rw is_unit_iff_dvd_one at *,
  cases hx with k hk,
  refine ⟨(k : zmod m), _⟩,
  rw ← zmod.cast_nat_cast (dvd_mul_right m n),
  rw ← zmod.cast_mul (dvd_mul_right m n),
  rw ← hk, rw zmod.cast_one (dvd_mul_right m n),
  any_goals { refine zmod.char_p _, },
end

lemma is_unit_of_is_unit_mul' {m n : ℕ} (x : ℕ) (hx : is_unit (x : zmod (m * n))) :
  is_unit (x : zmod n) :=
begin
  rw mul_comm at hx,
  apply is_unit_of_is_unit_mul x hx,
end

lemma is_coprime_of_is_unit {n x : ℕ} (hx : is_unit (x : zmod n)) : x.coprime n :=
begin
  exact not_is_unit_of_not_coprime hx,
end

lemma is_unit_of_is_unit_mul_iff {m n : ℕ} (x : ℕ) : is_unit (x : zmod (m * n)) ↔
  is_unit (x : zmod m) ∧ is_unit (x : zmod n) :=
  ⟨λ h, ⟨is_unit_of_is_unit_mul x h, is_unit_of_is_unit_mul' x h⟩,
  begin
    rintros ⟨h1, h2⟩,
    apply units.is_unit (zmod.unit_of_coprime x (nat.coprime.mul_right
      (not_is_unit_of_not_coprime h1) (not_is_unit_of_not_coprime h2))),
  end ⟩ -- solve_by_elim gives a funny error

lemma not_is_unit_of_not_is_unit_mul {m n x : ℕ} (hx : ¬ is_unit (x : zmod (m * n))) :
  ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) :=
begin
  rw ← not_and_distrib,
  contrapose hx,
  rw not_not at *,
  rw is_unit_of_is_unit_mul_iff, refine ⟨hx.1, hx.2⟩,
end

lemma not_is_unit_of_not_is_unit_mul' {m n : ℕ} [fact (0 < m * n)] (x : zmod (m * n))
  (hx : ¬ is_unit x) : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) :=
begin
  rw ← zmod.cast_id _ x at hx,
  rw ← zmod.nat_cast_val at hx,
  rw ← zmod.nat_cast_val, rw ← zmod.nat_cast_val,
  apply not_is_unit_of_not_is_unit_mul hx,
end

lemma dirichlet_character.eq_mul_of_coprime_lev --[normed_comm_ring R] [complete_space R] [char_zero R] [normed_algebra ℚ_[p] R]
  {m n : ℕ} (χ : dirichlet_character R (m * n)) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  ∀ x : ℕ, asso_dirichlet_character χ x =
  asso_dirichlet_character χ₁ x * asso_dirichlet_character χ₂ x :=
begin
--  have h : d.coprime (p^n) := nat.coprime_pow_spl p d n hd,
  refine ⟨monoid_hom.comp χ ((units.map (zmod.chinese_remainder hcop).symm.to_monoid_hom).comp
    (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (zmod m) (zmod n) _ _).symm)
    (monoid_hom.prod (monoid_hom.id _) 1))),
    monoid_hom.comp χ ((units.map (zmod.chinese_remainder hcop).symm.to_monoid_hom).comp
    (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (zmod m) (zmod n) _ _).symm)
    (monoid_hom.prod 1 (monoid_hom.id _)))), λ x, _⟩,
  { by_cases h' : is_unit (x : zmod (m * n)),
    { rw asso_dirichlet_character_eq_char' _ h',
      have h1 : is_unit (x : zmod m) := is_unit_of_is_unit_mul _ h',
      have h2 : is_unit (x : zmod n) := is_unit_of_is_unit_mul' _ h',
      rw asso_dirichlet_character_eq_char' _ h1,
      rw asso_dirichlet_character_eq_char' _ h2,
      simp,
      rw ← units.coe_mul, simp_rw [← mul_equiv.coe_to_monoid_hom, ← monoid_hom.map_mul,
        prod.mul_def, mul_one, one_mul],
      congr, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw mul_equiv.coe_to_monoid_hom,
      rw chinese_remainder_comp_prod_units R χ hcop h1 h2, },
    { rw asso_dirichlet_character_eq_zero _ h',
      -- make this a separate lemma
      have : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) := not_is_unit_of_not_is_unit_mul h',
      cases this,
      { rw asso_dirichlet_character_eq_zero _ this, rw zero_mul, },
      { rw asso_dirichlet_character_eq_zero _ this, rw mul_zero, }, }, },
end

lemma dirichlet_character.eq_mul_of_coprime_lev'
  {m n : ℕ} [fact (0 < m * n)] (χ : dirichlet_character R (m * n)) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  χ = χ₁.change_level (dvd_mul_right m n) * χ₂.change_level (dvd_mul_left n m) :=
begin
  obtain ⟨χ₁, χ₂, h⟩ := dirichlet_character.eq_mul_of_coprime_lev R χ hcop,
  refine ⟨χ₁, χ₂, _⟩,
  rw asso_dirichlet_character_eq_iff,
  ext, rw dirichlet_character.asso_dirichlet_character_mul,
  rw monoid_hom.mul_apply, specialize h (x.val),
  simp_rw zmod.nat_cast_val at h, simp_rw zmod.cast_id at h,
  rw h,
  by_cases h' : is_unit x,
  { rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ (dvd_mul_right m n) h',
    rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ (dvd_mul_left n m) h', },
  { have : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) := not_is_unit_of_not_is_unit_mul' x h',
    cases this,
    any_goals { rw asso_dirichlet_character_eq_zero _ h', rw zero_mul,
      rw asso_dirichlet_character_eq_zero _ h' at h, rw h.symm, }, },
end

open dirichlet_character

/-lemma dirichlet_character.eq_mul_primitive_of_coprime_lev_dvd
  {m n : ℕ} [fact (0 < m * n)] (χ : dirichlet_character R (m * n)) (hcop : m.coprime n) (hχ : m ∣ χ.conductor) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  χ₁.is_primitive ∧ χ = χ₁.change_level (dvd_mul_right m n) * χ₂.change_level (dvd_mul_left n m) :=
begin
  set χ₁ : dirichlet_character R m := monoid_hom.comp χ ((units.map (zmod.chinese_remainder hcop).symm.to_monoid_hom).comp
    (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (zmod m) (zmod n) _ _).symm)
    (monoid_hom.prod (monoid_hom.id _) 1))),
  set χ₂ : dirichlet_character R n := monoid_hom.comp χ ((units.map (zmod.chinese_remainder hcop).symm.to_monoid_hom).comp
    (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (zmod m) (zmod n) _ _).symm)
    (monoid_hom.prod 1 (monoid_hom.id _)))),
  refine ⟨χ₁, χ₂, _, _⟩,
  { cases hχ with k hk, rw is_primitive_def,
    have : χ.factors_through (χ₁.conductor * lev χ₂),
    sorry, },
  { ext,

    by_cases h' : is_unit (x : zmod (m * n)),
    { rw asso_dirichlet_character_eq_char' _ h',
      have h1 : is_unit (x : zmod m) := is_unit_of_is_unit_mul _ h',
      have h2 : is_unit (x : zmod n) := is_unit_of_is_unit_mul' _ h',
      rw asso_dirichlet_character_eq_char' _ h1,
      rw asso_dirichlet_character_eq_char' _ h2,
      simp,
      rw ← units.coe_mul, simp_rw [← mul_equiv.coe_to_monoid_hom, ← monoid_hom.map_mul,
        prod.mul_def, mul_one, one_mul],
      congr, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw mul_equiv.coe_to_monoid_hom,
      rw chinese_remainder_comp_prod_units R χ hcop h1 h2, },
    { rw asso_dirichlet_character_eq_zero _ h',
      -- make this a separate lemma
      have : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) := not_is_unit_of_not_is_unit_mul h',
      cases this,
      { rw asso_dirichlet_character_eq_zero _ this, rw zero_mul, },
      { rw asso_dirichlet_character_eq_zero _ this, rw mul_zero, }, }, },
end-/

lemma mul_change_level {n m : ℕ} (χ ψ : dirichlet_character R n) (h : n ∣ m) :
  (χ * ψ).change_level h = χ.change_level h * ψ.change_level h :=
begin
  simp_rw change_level, rw monoid_hom.mul_comp,
end
.
variable (hd)

lemma dirichlet_character.change_level_one {n : ℕ} :
  (1 : dirichlet_character R 1).change_level (one_dvd n) = 1 :=
begin
  ext, simp only [monoid_hom.one_apply, units.coe_one, units.coe_eq_one],
  rw change_level, simp,
end

lemma units.chinese_remainder_symm_apply_fst' {m n : ℕ} (hd : m.coprime n) (a : (zmod m)ˣ × (zmod n)ˣ) :
  (((units.chinese_remainder hd).symm a : zmod (m * n)) : zmod m) =
  (a.fst : zmod m) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder hd),
  change (zmod.cast_hom (dvd_mul_right m n) (zmod m))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.fst),
  rw proj_fst',
end

lemma units.chinese_remainder_symm_apply_snd' {m n : ℕ} (hd : m.coprime n) (a : (zmod m)ˣ × (zmod n)ˣ) :
  (((units.chinese_remainder hd).symm a : zmod (m * n)) : zmod n) =
  (a.snd : zmod n) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder hd),
  change (zmod.cast_hom (dvd_mul_left n m) (zmod n))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.snd),
  rw proj_snd',
end

lemma mul_change_level_eq_of_coprime {m n : ℕ} (hd : m.coprime n) {χ χ' : dirichlet_character R m}
  {ψ ψ' : dirichlet_character R n}
  (h : χ.change_level (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m) =
    χ'.change_level (dvd_mul_right m n) * ψ'.change_level (dvd_mul_left n m)) : χ = χ' ∧ ψ = ψ' :=
begin
  split,
  { ext, rw monoid_hom.ext_iff at h, simp_rw monoid_hom.mul_apply at h,
    simp_rw units.ext_iff at h, simp_rw change_level at h,
    specialize h ((units.chinese_remainder hd).symm (x, 1)),
    simp_rw monoid_hom.comp_apply at h, simp_rw units.coe_mul at h,
    rw ← asso_dirichlet_character_eq_char χ at h, rw ← asso_dirichlet_character_eq_char χ' at h,
    rw ← asso_dirichlet_character_eq_char ψ at h, rw ← asso_dirichlet_character_eq_char ψ' at h,
    simp_rw [units.coe_map, ring_hom.coe_monoid_hom, zmod.cast_hom_apply] at h,
    rw units.chinese_remainder_symm_apply_fst' at h,
    rw units.chinese_remainder_symm_apply_snd' at h,
    simp_rw asso_dirichlet_character_eq_char at h, simp_rw monoid_hom.map_one at h,
    rw units.coe_one at h, simp_rw mul_one at h, rw h, },
  { ext, rw monoid_hom.ext_iff at h, simp_rw monoid_hom.mul_apply at h,
    simp_rw units.ext_iff at h, simp_rw change_level at h,
    specialize h ((units.chinese_remainder hd).symm (1, x)),
    simp_rw monoid_hom.comp_apply at h, simp_rw units.coe_mul at h,
    rw ← asso_dirichlet_character_eq_char χ at h, rw ← asso_dirichlet_character_eq_char χ' at h,
    rw ← asso_dirichlet_character_eq_char ψ at h, rw ← asso_dirichlet_character_eq_char ψ' at h,
    simp_rw [units.coe_map, ring_hom.coe_monoid_hom, zmod.cast_hom_apply] at h,
    rw units.chinese_remainder_symm_apply_fst' at h,
    rw units.chinese_remainder_symm_apply_snd' at h,
    simp_rw asso_dirichlet_character_eq_char at h, simp_rw monoid_hom.map_one at h,
    rw units.coe_one at h, simp_rw one_mul at h, rw h, },
end

lemma lev_eq_of_primitive {m n : ℕ} [fact (0 < n)] (h : m ∣ n) {χ : dirichlet_character R n}
  {χ' : dirichlet_character R m} (hχ : χ.is_primitive) (h_change : χ'.change_level h = χ) : m = n :=
begin
  by_contra h',
  rw is_primitive_def at hχ,
  have m_lt_n := lt_of_le_of_ne (nat.le_of_dvd (fact.out _) h) h',
  rw ← hχ at m_lt_n,
  have ft : χ.factors_through m := ⟨h, χ', h_change.symm⟩,
  rw ← mem_conductor_set_iff at ft,
  have := cInf_le' ft,
  apply not_le_of_gt m_lt_n this,
end

-- hopefully not needed?
lemma nat.eq_zero_of_not_pos {n : ℕ} (hn : ¬ 0 < n) : n = 0 := by linarith

lemma exists_mul_of_dvd {m n : ℕ} (h : m.coprime n) (χ : dirichlet_character R m) (ψ : dirichlet_character R n) :
  ∃ (x y : ℕ), x ∣ m ∧ y ∣ n ∧ (χ.mul ψ).conductor = x * y :=
begin
  rw (is_primitive_def _).1 (is_primitive_mul χ ψ),
  have : lcm m n = m * n,
  { rw lcm_eq_nat_lcm,
    rw nat.coprime.lcm_eq_mul h, },
  obtain ⟨x, hx, y, hy, h'⟩ := exists_dvd_and_dvd_of_dvd_mul (conductor_dvd (χ.change_level
    (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m))),
  refine ⟨x, y, hx, hy, _⟩, rw ← h',
  congr',
end

lemma nat.coprime_of_dvd_of_coprime {m n x y : ℕ} (h : m.coprime n) (hx : x ∣ m) (hy : y ∣ n) :
  x.coprime y :=
begin
  have : x.coprime n,
  { rw ← nat.is_coprime_iff_coprime,
    apply is_coprime.of_coprime_of_dvd_left (nat.is_coprime_iff_coprime.2 h) _,
    norm_cast, assumption, },
  rw ← nat.is_coprime_iff_coprime,
--  rw is_coprime_comm,
  apply is_coprime.of_coprime_of_dvd_right (nat.is_coprime_iff_coprime.2 this) _,
  norm_cast, assumption,
end

lemma helper_0 {m n : ℕ} (x y : ℕ) [fact (0 < m)] [fact (0 < n)] (hd : m.coprime n)
  {χ : dirichlet_character R m} {ψ : dirichlet_character R n} (hχ : χ.is_primitive)
  (hψ : ψ.is_primitive) (hx : x ∣ m) (hy : y ∣ n) (h' : (χ.change_level _ * ψ.change_level _).conductor = x * y)
  [fact (0 < x * y)] :
  let η : dirichlet_character R (x * y) := (equiv h') (χ.mul ψ)
  in --η = χ₁.change_level _ * ψ₁.change_level _ →
     η.change_level (mul_dvd_mul hx hy) = χ.change_level (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m) :=
begin
  intro η,
--  change ((dirichlet_character.equiv h') (χ.mul ψ)).change_level _ = _,

  admit,
end

lemma conductor_mul_eq_mul_conductor_of_primitive {m n : ℕ} [fact (0 < m)] [fact (0 < n)]
  (hd : m.coprime n) {χ : dirichlet_character R m} {ψ : dirichlet_character R n}
  (hχ : χ.is_primitive) (hψ : ψ.is_primitive) :
  dirichlet_character.conductor (χ.mul ψ) = χ.conductor * ψ.conductor :=
begin
  rw (is_primitive_def _).1 hχ,
  rw (is_primitive_def _).1 hψ,
  rw (is_primitive_def _).1 (is_primitive_mul χ ψ),
  --have : ∃ (x y : ℕ), x ∣ m ∧ y ∣ n ∧ (χ.mul ψ).conductor = x * y,
  obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd R hd χ ψ,
  rw (is_primitive_def _).1 (is_primitive_mul χ ψ) at h',
--  rcases this with ⟨x, y, hx, hy, h'⟩,
  --obtain ⟨x, hx, y, hy, h'⟩ := exists_dvd_and_dvd_of_dvd_mul (conductor_dvd (χ.change_level
  --  (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m))),
  set η := dirichlet_character.equiv h' (χ.mul ψ),
  haveI : fact (0 < x * y),
  { apply fact_iff.2, by_contra hzero,
    have eq_zero : x * y = 0 := nat.eq_zero_of_not_pos hzero,
    rw eq_zero at h', rw conductor_eq_zero_iff_level_eq_zero at h', rw lcm_eq_zero_iff at h',
    cases h' with h₁ h₁,
    all_goals { apply ne_zero_of_lt (fact.out _) h₁, exact 0, apply_instance, }, },
  obtain ⟨χ₁, ψ₁, hη⟩ := dirichlet_character.eq_mul_of_coprime_lev' R η
    (nat.coprime_of_dvd_of_coprime hd hx hy),
  rw h',
  suffices suff : x = m ∧ y = n,
  { rw suff.1, rw suff.2, },
  { have : η.change_level (mul_dvd_mul hx hy) = χ.change_level (dvd_mul_right m n) *
      ψ.change_level (dvd_mul_left n m),
    { refine helper_0 R x y hd hχ hψ hx hy h', },
    rw hη at this, rw mul_change_level at this,
    rw ← change_level_dvd at this, rw ← change_level_dvd at this,
    rw change_level_dvd _ hx (dvd_mul_right m n) at this,
    rw change_level_dvd _ hy (dvd_mul_left n m) at this,
    have req := mul_change_level_eq_of_coprime R hd this,
    refine ⟨lev_eq_of_primitive R hx hχ req.1, lev_eq_of_primitive R hy hψ req.2⟩, },
end

lemma pow_change_level {m n k : ℕ} (h : n ∣ m) (χ : dirichlet_character R n) :
  (χ.change_level h)^k = (χ^k).change_level h :=
begin
  ext, simp_rw change_level,
  simp only [monoid_hom.coe_comp, function.comp_app],
  refl,
end

lemma eq_asso_primitive_character_change_level {m n : ℕ} (h : m ∣ n) (χ : dirichlet_character R m) :
  χ.change_level h = χ.asso_primitive_character.change_level
    (dvd_trans (conductor_dvd _) h) :=
begin
  rw asso_primitive_character,
  conv_lhs { rw factors_through_spec χ (mem_conductor_set_factors_through _ (mem_conductor _)), },
  rw ← change_level_dvd,
end

lemma conductor_mul_eq_conductor_mul_of_coprime {n m : ℕ} {χ : dirichlet_character R m} {ψ : dirichlet_character R n} (h : m.coprime n) :
  (χ.mul ψ).conductor = (χ.change_level (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m)).conductor :=
begin
  rw (is_primitive_def _).1 (is_primitive_mul _ _),
  have : lcm m n = m * n,
  { rw lcm_eq_nat_lcm, rw nat.coprime.lcm_eq_mul h, },
  congr',
end

/-example {n m : ℕ} {χ : dirichlet_character R m} {ψ : dirichlet_character R n}
  (h : ∀ x : ℕ, asso_dirichlet_character χ x = asso_dirichlet_character ψ x) :
  χ.conductor = ψ.conductor :=
begin
  revert m χ ψ h,
  apply nat.strong_induction_on n,
  intros x hd y χ ψ h,
  have h1 : ψ.conductor ∈ χ.conductor_set,
  { rw mem_conductor_set_iff, constructor, },
end

lemma change_level_conductor_eq_conductor {n m : ℕ} (h : n ∣ m) {χ : dirichlet_character R n} (hχ : χ.is_primitive) :
  (χ.change_level h).conductor = χ.conductor :=
begin
  have p1 : (χ.change_level h).factors_through n, sorry,
  have p2 := mem_conductor_set_eq_conductor _ ((mem_conductor_set_iff _).2 p1),
  apply le_antisymm _ _,
  { apply_instance, },
  { convert p2,
    have := factors_through_spec _ p1,  },
  rw ← (is_primitive_def _).1 (asso_primitive_character_is_primitive χ),

end

lemma conductor_mul_eq_mul_conductor {m n : ℕ} [fact (0 < m)] [fact (0 < n)]
  (hd : m.coprime n) (χ : dirichlet_character R m) (ψ : dirichlet_character R n) :
  dirichlet_character.conductor (χ.mul ψ) = lcm χ.conductor ψ.conductor :=
begin
  haveI : fact (0 < χ.conductor), sorry,
  haveI : fact (0 < ψ.conductor), sorry,
  rw conductor_mul_eq_conductor_mul_of_coprime R hd,
  rw eq_asso_primitive_character_change_level, rw eq_asso_primitive_character_change_level R _ ψ,
  have h1 : lcm χ.conductor ψ.conductor = χ.conductor * ψ.conductor,
  { sorry, },
  have h2 : χ.conductor.coprime ψ.conductor := sorry,
  rw h1,
  have := conductor_mul_eq_mul_conductor_of_primitive R h2 (asso_primitive_character_is_primitive χ)
    (asso_primitive_character_is_primitive ψ),
  simp_rw (is_primitive_def _).1 (asso_primitive_character_is_primitive _) at this,
  rw ← this,
end-/

lemma mul_def {n m : ℕ} {χ : dirichlet_character R n} {ψ : dirichlet_character R m} :
  χ.mul ψ = (χ.change_level _ * ψ.change_level _).asso_primitive_character := rfl

lemma mul_conductor_eq_mul_conductor (n : ℕ) :
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)).conductor =
  (χ * (teichmuller_character_mod_p_change_level p d R m ^ n)).conductor :=
begin
  rw (is_primitive_def _).1 (is_primitive_mul _ _),
  have : lcm (d * p^m) (d * p^m) = d * p^m,
  { simp only [lcm_same, normalize_eq], },
  conv_rhs { congr, rw ← change_level_self χ,
    rw ← change_level_self (teichmuller_character_mod_p_change_level p d R m ^ n), },
  congr',
end

lemma exists_mul_of_dvd' (n : ℕ) (hd : d.coprime p) :
  ∃ (x y : ℕ), x ∣ d ∧ y ∣ p^m ∧ (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)).conductor = x * y :=
begin
  simp_rw mul_conductor_eq_mul_conductor p d R m χ n,
  obtain ⟨χ₁, χ₂, h⟩ := dirichlet_character.eq_mul_of_coprime_lev' R χ (nat.coprime_pow_spl p d m hd),
  rw h, rw mul_assoc, delta teichmuller_character_mod_p_change_level,
  rw pow_change_level,
  have hm : m ≠ 0,
  { apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
  rw change_level_dvd _ (dvd_pow_self p hm) (dvd_mul_left (p^m) d), rw ← mul_change_level,
  obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd R (nat.coprime_pow_spl p d m hd) χ₁
    (χ₂ * ((((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
    (teichmuller_character_mod_p p) : dirichlet_character _ p)⁻¹)^n : dirichlet_character _ _).change_level (dvd_pow_self p hm)),
  refine ⟨x, y, hx, hy, _⟩,
  rw ← h',
  rw (is_primitive_def _).1 (is_primitive_mul _ _),
  have : d * p^m = lcm d (p^m),
  { rw lcm_eq_nat_lcm, rw nat.coprime.lcm_eq_mul (nat.coprime_pow_spl p d _ hd), },
  congr',
end

lemma eq_of_mul_eq_mul_of_coprime_of_dvd {x y m n : ℕ} (hcop : m.coprime n) (hx : x ∣ m) (hy : y ∣ n) (h : x * y = m * n) :
  x = m ∧ y = n :=
begin
  have p1 : m ∣ x := sorry,
  have p2 : n ∣ y := sorry,
  refine ⟨nat.dvd_antisymm hx p1, nat.dvd_antisymm hy p2⟩,
end

lemma dirichlet_character.eq_mul_primitive_of_coprime {m n : ℕ} [fact (0 < m * n)]
  (χ : dirichlet_character R (m * n)) (hχ : χ.is_primitive) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  χ₁.is_primitive ∧ χ₂.is_primitive ∧
  χ = χ₁.change_level (dvd_mul_right m n) * χ₂.change_level (dvd_mul_left n m) :=
begin
  obtain ⟨χ₁, χ₂, h⟩ := dirichlet_character.eq_mul_of_coprime_lev' R χ hcop,
  simp_rw ← and_assoc,
  refine ⟨χ₁, χ₂, _, h⟩,
  rw eq_asso_primitive_character_change_level at h,
  rw eq_asso_primitive_character_change_level R _ χ₂ at h,
  have p1 : χ₁.conductor * χ₂.conductor ∣ m * n := mul_dvd_mul (conductor_dvd _) (conductor_dvd _),
  rw change_level_dvd χ₁.asso_primitive_character (dvd_mul_right _ _) p1 at h,
  rw change_level_dvd _ (dvd_mul_left _ _) p1 at h,
  rw ← mul_change_level at h,
  have p2 := lev_eq_of_primitive R _ hχ h.symm,
  rw is_primitive_def, rw is_primitive_def,
  apply eq_of_mul_eq_mul_of_coprime_of_dvd hcop (conductor_dvd _) (conductor_dvd _) p2,
end

lemma dirichlet_character.eq_mul_of_coprime_of_dvd_conductor {m n : ℕ} [fact (0 < m * n)]
  (χ : dirichlet_character R (m * n)) (hχ : m ∣ χ.conductor) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  χ₁.is_primitive ∧ χ = χ₁.change_level (dvd_mul_right m n) * χ₂.change_level (dvd_mul_left n m) :=
begin
  obtain ⟨χ₁, χ₂, h⟩ := dirichlet_character.eq_mul_of_coprime_lev' R χ hcop,
  refine ⟨χ₁, χ₂, _, h⟩,
  cases hχ with k hk,
  set η' := dirichlet_character.equiv hk χ.asso_primitive_character,
  haveI : fact (0 < m * k), sorry,
  have hcop' : m.coprime k, sorry,
  obtain ⟨χ₁', χ₂', h'⟩ := dirichlet_character.eq_mul_primitive_of_coprime R η' _ hcop',
  { have dv : k ∣ n, sorry,
    have p1 : η'.change_level (mul_dvd_mul_left m dv) = χ, sorry,
    rw h at p1, rw h'.2.2 at p1, rw mul_change_level at p1,
    rw ← change_level_dvd at p1, rw ← change_level_dvd at p1,
    rw change_level_dvd χ₂' dv (dvd_mul_left n m) at p1,
    have req := mul_change_level_eq_of_coprime R hcop p1,
    rw ← req.1, apply h'.1, },
  sorry,
end

lemma dvd_mul_of_dvd_conductor (n : ℕ) (hd : d.coprime p) (hχ : d ∣ χ.conductor) :
  d ∣ (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)).conductor :=
begin
  have hm : m ≠ 0,
  { apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
  obtain ⟨χ₁, χ₂, hχ₁, h⟩ := dirichlet_character.eq_mul_of_coprime_of_dvd_conductor R χ hχ
    (nat.coprime_pow_spl p d m hd),
  set ψ := (χ₂ * ((((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
    (teichmuller_character_mod_p p) : dirichlet_character _ p)⁻¹)^n : dirichlet_character _ _).change_level (dvd_pow_self p hm)),
  { obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd' p d R m χ n hd,
    rw h', apply dvd_mul_of_dvd_left,
    rw h at h',
    rw mul_conductor_eq_mul_conductor at h',
    delta teichmuller_character_mod_p_change_level at h',
    rw pow_change_level at h',
    rw change_level_dvd _ (dvd_pow_self p hm) (dvd_mul_left (p^m) d) at h',
    rw mul_assoc at h', rw ← mul_change_level at h',
    have h'' : (χ₁.mul ψ).conductor = x * y,
    { rw ← h', rw (is_primitive_def _).1 (is_primitive_mul _ _),
      have : lcm d (p^m) = d * p^m,
      { rw lcm_eq_nat_lcm, rw nat.coprime.lcm_eq_mul (nat.coprime_pow_spl p d _ hd), },
      congr', },
    rw (is_primitive_def _).1 (is_primitive_mul _ _) at h'',
    set η := dirichlet_character.equiv h'' (χ₁.mul ψ),
    haveI : fact (0 < x * y),
    { apply fact_iff.2, by_contra hzero,
      have eq_zero : x * y = 0 := nat.eq_zero_of_not_pos hzero,
      rw eq_zero at h', rw conductor_eq_zero_iff_level_eq_zero at h',
      apply ne_zero_of_lt (fact_iff.1 (imp p d m)) h', },
    obtain ⟨χ₁', ψ₁', hη⟩ := dirichlet_character.eq_mul_of_coprime_lev' R η
      (nat.coprime_of_dvd_of_coprime (nat.coprime_pow_spl p d m hd) hx hy),
    have : η.change_level (mul_dvd_mul hx hy) = χ₁.change_level (dvd_mul_right d (p^m)) *
      ψ.change_level (dvd_mul_left (p^m) d),
    { have : (χ₁.mul ψ).change_level ( dvd_trans (conductor_dvd _) (nat.lcm_dvd_mul _ _)) =
        χ₁.change_level (dvd_mul_right d (p^m)) * ψ.change_level (dvd_mul_left (p^m) d), sorry,
      rw ← this,
      have p2 : x * y = (χ₁.change_level (dvd_mul_right d (p^m)) *
        ψ.change_level (dvd_mul_left (p^m) d)).conductor, sorry,
      have h'' := h'.symm,
      congr',
      rw p2, sorry,
      sorry, },
    rw hη at this, rw mul_change_level at this,
    rw ← change_level_dvd at this, rw ← change_level_dvd at this,
    rw change_level_dvd _ hx (dvd_mul_right d (p^m)) at this,
    rw change_level_dvd _ hy (dvd_mul_left (p^m) d) at this,
    have req := mul_change_level_eq_of_coprime R (nat.coprime_pow_spl p d m hd) this,
    have := lev_eq_of_primitive R hx hχ₁ req.1,
    rw this, },
end

lemma helper_U_2 [no_zero_divisors R] [normed_algebra ℚ R] [norm_one_class R] (n : ℕ)
  (hd : d.coprime p) (hχ : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x))) at_top (nhds 0) :=
begin
  apply (tendsto_congr _).2 (tendsto_const_nhds),
  intro x,
  apply finset.sum_eq_zero,
  intros y hy,
  rw smul_eq_mul,
  rw mul_eq_zero, left,
  rw mul_eq_zero, left,
  simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
    set.mem_set_of_eq] at hy,
  cases hy with h1 h2,
  rw asso_dirichlet_character_eq_zero,
  contrapose h2, rw not_not at *, apply not_is_unit_of_not_coprime,
  obtain ⟨k, hk⟩ := dvd_mul_of_dvd_conductor p d R m χ n hd hχ,
  rw (is_primitive_def _).1 (is_primitive_mul _ _) at hk,
  rw hk at h2,
  apply is_unit_of_is_unit_mul y h2,
end

lemma helper_U_3 (x : ℕ) : finset.range (d * p^x) = set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})) ∪ ((set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p}))) ∪ set.finite.to_finset (set.finite_of_finite_inter (finset.range (d * p^x))
  ({x | x.coprime d} ∩ {x | x.coprime p}))) :=
begin
  ext,
  simp only [finset.mem_range, finset.mem_union, set.finite.mem_to_finset, set.mem_inter_eq,
    finset.mem_coe, set.mem_set_of_eq],
  split, -- better way to do this?
  { intro h,
    by_cases h' : a.coprime d ∧ a.coprime p, { right, right, refine ⟨h, h'⟩, },
    { rw not_and_distrib at h', cases h',
      { left, refine ⟨h, h'⟩, },
      { right, left, refine ⟨h, h'⟩, }, }, },
  { intro h, cases h, apply h.1,
    cases h, apply h.1, apply h.1, },
end

lemma zmod.is_unit_val_of_unit {n k : ℕ} [fact (0 < n)] (hk : k ∣ n) (u : (zmod n)ˣ) :
  is_unit ((u : zmod n).val : zmod k) :=
by { sorry, }

lemma helper_U_4 [normed_algebra ℚ R] [no_zero_divisors R] (hd : d.coprime p) (hχ : d ∣ χ.conductor) (n x : ℕ) : ∑ (x_1 : ℕ) in (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime d}).to_finset ∩ (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime p}).to_finset,
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑x_1 *
  ↑x_1 ^ (n - 1)) • (algebra_map ℚ R) (↑x_1 / (↑d * ↑p ^ x)) = 0 :=
begin
  apply finset.sum_eq_zero, intros y hy,
  simp only [finset.mem_inter, set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe,
    finset.mem_range, set.mem_set_of_eq] at hy,
  convert zero_smul R _, rw mul_eq_zero, left,
  rw asso_dirichlet_character_eq_zero,
  cases hy with p1 p3,
  cases p1 with p1 p2,
  cases p3 with p3 p4,
  contrapose p2, rw not_not at *, apply not_is_unit_of_not_coprime,
  obtain ⟨k, hk⟩ := dvd_mul_of_dvd_conductor p d R m χ n hd hχ,
  rw (is_primitive_def _).1 (is_primitive_mul _ _) at hk,
  rw hk at p2,
  apply is_unit_of_is_unit_mul y p2,
end

lemma U [normed_algebra ℚ R] [norm_one_class R] [no_zero_divisors R] (hd : d.coprime p) (n : ℕ)
  (hn : 1 < n) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ j : ℕ, U_def p d R m χ n j)
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n)) ) :=
begin
  delta U_def,
  convert (tendsto_congr' _).2 (filter.tendsto.sub (filter.tendsto.sub
    (lim_even_character d p m χ na hn hχ hp) (helper_U_2 p d R m χ n hd hχ')) (helper_U_1' p d R m χ n hn hχ hp na)), -- might need a tendsto_congr' here
  { rw sub_zero, rw ← one_sub_mul, },
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨m, λ x hx, _⟩,
    simp only,
    haveI : fact (0 < d * p^x) := imp p d x,
    have h1 : d * p^m ∣ d * p^x := mul_dvd_mul_left d (pow_dvd_pow p hx),
    rw finset.smul_sum,
    conv_lhs { apply_congr, skip, rw coe_coe, rw coe_coe,
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw fract_eq_self (zero_le_and_lt_one p d _ _).1 (zero_le_and_lt_one p d _ _).2,
      conv { congr, rw ← dirichlet_character.mul_eq_mul R χ
        (teichmuller_character_mod_p_change_level p d R m ^ n) (zmod.is_unit_val_of_unit h1 x_1), }, },
    convert sum_units_eq p d R _ (λ (y : ℕ), ((asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑y * ↑y ^ (n - 1)) •
      (algebra_map ℚ R) (((y : ℚ) / (↑d * ↑p ^ x)))),
    rw sub_sub, rw ← finset.sum_union_inter, rw add_comm,
    apply sub_eq_of_eq_add', rw add_assoc, rw ← finset.sum_union _,
    rw helper_U_4 p d R m χ hd hχ', rw zero_add,
--    apply sub_eq_of_eq_add', rw ← finset.sum_union _,
    { apply finset.sum_congr,
      { rw finset.union_assoc, rw ← helper_U_3, },
      { intros y hy, rw ← algebra_map_smul R (1 / ↑(d * p ^ x : ℕ) : ℚ), rw smul_eq_mul, rw smul_eq_mul,
        { rw mul_comm, rw ← mul_one (y : ℚ), rw ← mul_div, rw ring_hom.map_mul, rw map_nat_cast,
          rw ← mul_assoc, rw [nat.cast_mul d _, nat.cast_pow p], apply congr_arg2 _ _ rfl,
          rw mul_assoc, apply congr_arg2 _ rfl _, rw ← pow_succ', rw nat.sub_add_cancel (le_of_lt hn), },
        { apply_instance, }, }, },
    { rw finset.disjoint_union_left, simp_rw finset.disjoint_iff_inter_eq_empty,
      refine ⟨_, _⟩,
      { ext,
        simp only [finset.mem_inter, set.finite.mem_to_finset, set.mem_inter_eq,
          finset.mem_coe, finset.mem_range, set.mem_set_of_eq, finset.not_mem_empty, iff_false,
          not_and, and_imp],
        intros p1 p2 p3 p4 p5,
        apply p2 p4, },
      { ext,
        simp only [finset.mem_inter, set.finite.mem_to_finset, set.mem_inter_eq,
          finset.mem_coe, finset.mem_range, set.mem_set_of_eq, finset.not_mem_empty, iff_false,
          not_and, and_imp],
        intros p1 p2 p3 p4 p5,
        apply p2 p5, }, },
    { apply lt_of_lt_of_le (fact.out _) hx, apply_instance, }, },
end
