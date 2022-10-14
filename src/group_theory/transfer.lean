/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.complement
import group_theory.sylow
import topology.algebra.continuous_monoid_hom

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
- `transfer_center_pow`: The transfer homomorphism `G →*  center G`.
-/

open_locale big_operators

variables {G : Type*} [group G] {H : subgroup G} {A : Type*} [comm_group A] (ϕ : H →* A)

namespace subgroup

namespace left_transversals

open finset mul_action

open_locale pointwise

variables (R S T : left_transversals (H : set G)) [fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α := mem_left_transversals.to_equiv S.2, β := mem_left_transversals.to_equiv T.2 in
∏ q, ϕ ⟨(α q)⁻¹ * β q, quotient_group.left_rel_apply.mp $
  quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive] lemma diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
prod_mul_distrib.symm.trans (prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans (congr_arg ϕ
  (by simp_rw [subtype.ext_iff, coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left]))))

@[to_additive] lemma diff_self : diff ϕ T T = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive] lemma diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
inv_eq_of_mul_eq_one_right $ (diff_mul_diff ϕ S T S).trans $ diff_self ϕ S

@[to_additive] lemma smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
prod_bij' (λ q _, g⁻¹ • q) (λ _ _, mem_univ _) (λ _ _, congr_arg ϕ (by simp_rw [coe_mk,
  smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]))
  (λ q _, g • q) (λ _ _, mem_univ _) (λ q _, smul_inv_smul g q) (λ q _, inv_smul_smul g q)

end left_transversals

end subgroup

namespace monoid_hom

open mul_action subgroup subgroup.left_transversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`."]
noncomputable def transfer [fintype (G ⧸ H)] : G →* A :=
let T : left_transversals (H : set G) := inhabited.default in
{ to_fun := λ g, diff ϕ T (g • T),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

variables (T : left_transversals (H : set G))

@[to_additive] lemma transfer_def [fintype (G ⧸ H)] (g : G) : transfer ϕ g = diff ϕ T (g • T) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

/-- Explicit computation of the transfer homomorphism. -/
lemma transfer_eq_prod_quotient_orbit_rel_zpowers_quot [fintype (G ⧸ H)]
  (g : G) [fintype (quotient (orbit_rel (zpowers g) (G ⧸ H)))] :
  transfer ϕ g = ∏ (q : quotient (orbit_rel (zpowers g) (G ⧸ H))),
    ϕ ⟨q.out'.out'⁻¹ * g ^ function.minimal_period ((•) g) q.out' * q.out'.out',
      quotient_group.out'_conj_pow_minimal_period_mem H g q.out'⟩ :=
begin
  classical,
  calc transfer ϕ g = ∏ (q : G ⧸ H), _ : transfer_def ϕ (transfer_transversal H g) g
  ... = _ : ((quotient_equiv_sigma_zmod H g).symm.prod_comp _).symm
  ... = _ : finset.prod_sigma _ _ _
  ... = _ : fintype.prod_congr _ _ (λ q, _),
  simp only [quotient_equiv_sigma_zmod_symm_apply,
    transfer_transversal_apply', transfer_transversal_apply''],
  rw fintype.prod_eq_single (0 : zmod (function.minimal_period ((•) g) q.out')) (λ k hk, _),
  { simp only [if_pos, zmod.cast_zero, zpow_zero, one_mul, mul_assoc] },
  { simp only [if_neg hk, inv_mul_self],
    exact map_one ϕ },
end

/-- Auxillary lemma in order to state `transfer_eq_pow`. -/
lemma transfer_eq_pow_aux (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  g ^ H.index ∈ H :=
begin
  by_cases hH : H.index = 0,
  { rw [hH, pow_zero],
    exact H.one_mem },
  haveI := fintype_of_index_ne_zero hH,
  classical,
  replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H :=
  λ k g₀ hk, (_root_.congr_arg (∈ H) (key k g₀ hk)).mp hk,
  replace key : ∀ q : G ⧸ H, g ^ function.minimal_period ((•) g) q ∈ H :=
  λ q, key (function.minimal_period ((•) g) q) q.out'
    (quotient_group.out'_conj_pow_minimal_period_mem H g q),
  let f : quotient (orbit_rel (zpowers g) (G ⧸ H)) → zpowers g :=
  λ q, (⟨g, mem_zpowers g⟩ : zpowers g) ^ function.minimal_period ((•) g) q.out',
  have hf : ∀ q, f q ∈ H.subgroup_of (zpowers g) := λ q, key q.out',
  replace key := subgroup.prod_mem (H.subgroup_of (zpowers g)) (λ q (hq : q ∈ finset.univ), hf q),
  simpa only [minimal_period_eq_card, finset.prod_pow_eq_pow_sum, fintype.card_sigma,
    fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)), index_eq_card] using key,
end

lemma transfer_eq_pow [fintype (G ⧸ H)] (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g key⟩ :=
begin
  classical,
  change ∀ k g₀ (hk : g₀⁻¹ * g ^ k * g₀ ∈ H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key,
  rw [transfer_eq_prod_quotient_orbit_rel_zpowers_quot, ←finset.prod_to_list, list.prod_map_hom],
  refine congr_arg ϕ (subtype.coe_injective _),
  rw [H.coe_mk, ←(zpowers g).coe_mk g (mem_zpowers g), ←(zpowers g).coe_pow, (zpowers g).coe_mk,
      index_eq_card, fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)),
      fintype.card_sigma, ←finset.prod_pow_eq_pow_sum, ←finset.prod_to_list],
  simp only [coe_list_prod, list.map_map, ←minimal_period_eq_card],
  congr' 2,
  funext,
  apply key,
end

lemma transfer_center_eq_pow [fintype (G ⧸ center G)] (g : G) :
  transfer (monoid_hom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
transfer_eq_pow (id (center G)) g (λ k _ hk, by rw [←mul_right_inj, hk, mul_inv_cancel_right])

/-- The transfer homomorphism `G →* center G`. -/
noncomputable def transfer_center_pow [fintype (G ⧸ center G)] : G →* center G :=
{ to_fun := λ g, ⟨g ^ (center G).index, (center G).pow_index_mem g⟩,
  map_one' := subtype.ext (one_pow (center G).index),
  map_mul' := λ a b, by simp_rw [←show ∀ g, (_ : center G) = _,
    from transfer_center_eq_pow, map_mul] }

@[simp] lemma transfer_center_pow_apply [fintype (G ⧸ center G)] (g : G) :
  ↑(transfer_center_pow g) = g ^ (center G).index :=
rfl

/-- The transfer homomorphism `G →* center G`. -/
noncomputable def transfer_center_pow' (h : (center G).index ≠ 0) : G →* center G :=
@transfer_center_pow G _ (fintype_of_index_ne_zero h)

@[simp] lemma transfer_center_pow'_apply (h : (center G).index ≠ 0) (g : G) :
  ↑(transfer_center_pow' h g) = g ^ (center G).index :=
rfl

open_locale pointwise

-- PRed
lemma _root_.subgroup.mul_injective_of_disjoint {H₁ H₂ : subgroup G} (h : disjoint H₁ H₂) :
  function.injective (λ g, g.1 * g.2 : H₁ × H₂ → G) :=
begin
  intros x y hxy,
  rw [←inv_mul_eq_iff_eq_mul, ←mul_assoc, ←mul_inv_eq_one, mul_assoc] at hxy,
  replace hxy := disjoint_iff_mul_eq_one.mp h (y.1⁻¹ * x.1).prop (x.2 * y.2⁻¹).prop hxy,
  rwa [coe_mul, coe_mul, coe_inv, coe_inv, inv_mul_eq_one, mul_inv_eq_one,
    ←subtype.ext_iff, ←subtype.ext_iff, eq_comm, ←prod.ext_iff] at hxy,
end

-- PRed
lemma is_complement'_of_disjoint_and_mul_eq_univ {H K : subgroup G}
  (h1 : disjoint H K) (h2 : ↑H * ↑K = (set.univ : set G)) : is_complement' H K :=
begin
  refine ⟨subgroup.mul_injective_of_disjoint h1, λ g, _⟩,
  obtain ⟨h, k, hh, hk, hg⟩ := set.eq_univ_iff_forall.mp h2 g,
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hg⟩,
end

lemma restrict_ker {G K : Type*} [group G] [group K] (H : subgroup G) (f : G →* K) :
  (f.restrict H).ker = f.ker.subgroup_of H :=
rfl

lemma restrict_range {G K : Type*} [group G] [group K] (H : subgroup G) (f : G →* K) :
  (f.restrict H).range = H.map f :=
begin
  simp_rw [set_like.ext_iff, mem_range, mem_map, restrict_apply, set_like.exists, subtype.coe_mk,
    iff_self, forall_const],
end

lemma _root_.is_p_group.pow_bijective' {p : ℕ} {G : Type*} [group G] (h : is_p_group p G)
  {n : ℕ} (hn : nat.coprime p n) : function.bijective ((^ n) : G → G) :=
begin
  by_cases hn1 : n = 1,
  { simp_rw [hn1, pow_one],
    exact function.bijective_id },
  haveI : Π g : G, fintype (zpowers g),
  { refine λ g, @fintype.of_finite (zpowers g) (nat.finite_of_card_ne_zero _),
    rw ← order_eq_card_zpowers',
    obtain ⟨k, hk⟩ := h g,
    refine ne_zero_of_dvd_ne_zero (pow_ne_zero k (λ hp, hn1 _)) (order_of_dvd_of_pow_eq_one hk),
    rwa [hp, nat.coprime_zero_left] at hn },
  have : ∀ g : G, (fintype.card (zpowers g)).coprime n,
  { intro g,
    rw [←nat.card_eq_fintype_card, ←order_eq_card_zpowers'],
    obtain ⟨k, hk⟩ := h g,
    exact (hn.pow_left k).coprime_dvd_left (order_of_dvd_of_pow_eq_one hk) },
  refine function.bijective_iff_has_inverse.mpr
    ⟨λ g, (pow_coprime (this g)).symm ⟨g, mem_zpowers g⟩, _, _⟩,
  { refine λ g, subtype.ext_iff.mp ((pow_coprime (this (g ^ n))).left_inv ⟨g, _⟩),
    exact ⟨_, subtype.ext_iff.mp ((pow_coprime (this g)).left_inv ⟨g, mem_zpowers g⟩)⟩ },
  { exact λ g, subtype.ext_iff.mp ((pow_coprime (this g)).right_inv ⟨g, mem_zpowers g⟩) },
end

lemma _root_.is_p_group.pow_bijective {p : ℕ} [fact p.prime] {G : Type*} [group G] (h : is_p_group p G)
  {n : ℕ} (hn : ¬ p ∣ n) : function.bijective ((^ n) : G → G) :=
h.pow_bijective' ((fact.out p.prime).coprime_iff_not_dvd.mpr hn)

lemma index_eq_zero_of_relindex_eq_zero {G : Type*} [group G] {H K : subgroup G}
  (h : H.relindex K = 0) : H.index = 0 :=
H.relindex_top_right.symm.trans (relindex_eq_zero_of_le_right le_top h)

section burnside_transfer

open_locale pointwise

variables {p : ℕ} (P : sylow p G) (hP : (P : subgroup G).normalizer ≤ (P : subgroup G).centralizer)

include hP

/-- The homomorphism `G →* P` in Burnside's transfer theorem. -/
noncomputable def transfer_sylow [finite (G ⧸ (P : subgroup G))] : G →* (P : subgroup G) :=
@transfer G _ P P (@subgroup.is_commutative.comm_group G _ P
  ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩) (monoid_hom.id P) (fintype.of_finite _)

variables [fact p.prime] [finite (sylow p G)]

/-- Auxillary lemma in order to state `transfer_sylow_eq_pow`. -/
lemma transfer_sylow_eq_pow_aux (g : G) (hg : g ∈ P) (k : ℕ) (g₀ : G) (h : g₀⁻¹ * g ^ k * g₀ ∈ P) :
  g₀⁻¹ * g ^ k * g₀ = g ^ k :=
begin
  haveI : (P : subgroup G).is_commutative := ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩,
  replace hg := (P : subgroup G).pow_mem hg k,
  obtain ⟨n, hn, h⟩ := P.conj_eq_normalizer_conj_of_mem (g ^ k) g₀ hg h,
  exact h.trans (commute.inv_mul_cancel (hP hn (g ^ k) hg).symm),
end

variables [fintype (G ⧸ (P : subgroup G))]

lemma transfer_sylow_eq_pow (g : G) (hg : g ∈ P) : transfer_sylow P hP g =
  ⟨g ^ (P : subgroup G).index, transfer_eq_pow_aux g (transfer_sylow_eq_pow_aux P hP g hg)⟩ :=
by apply transfer_eq_pow

/-- Burnside's normal p-complement theorem: If `N(P) ≤ C(P)`, then `P` has a normal complement. -/
lemma ker_transfer_sylow_is_complement : is_complement' (transfer_sylow P hP).ker P :=
begin
  have hf0 : ⇑((transfer_sylow P hP).restrict (P : subgroup G)) = (^ (P : subgroup G).index) :=
  funext (λ g, transfer_sylow_eq_pow P hP g g.2),
  have hf1 : function.bijective ((transfer_sylow P hP).restrict (P : subgroup G)) :=
  hf0.symm ▸ P.2.pow_bijective (not_dvd_index_sylow P
    (mt index_eq_zero_of_relindex_eq_zero index_ne_zero_of_finite)),
  rw [function.bijective, ←range_top_iff_surjective, restrict_range] at hf1,
  have : function.surjective (transfer_sylow P hP),
  { rw [←range_top_iff_surjective, eq_top_iff],
    exact hf1.2.symm.le.trans (map_le_range (transfer_sylow P hP) P) },
  rw [←(comap_injective this).eq_iff, comap_top, comap_map_eq, sup_comm, set_like.ext'_iff,
      normal_mul, ←ker_eq_bot_iff, ←(map_injective (P : subgroup G).subtype_injective).eq_iff,
      restrict_ker, subgroup_of_map_subtype, subgroup.map_bot, coe_top] at hf1,
  exact is_complement'_of_disjoint_and_mul_eq_univ hf1.1.le hf1.2,
end

/-
TODO: Prove that `(transfer_sylow P hP).ker` is finite of order indivisible by `p`
TODO: Deduce disjointness for free!
-/

lemma ker_transfer_sylow_disjoint : disjoint (transfer_sylow P hP).ker ↑P :=
begin
  exact (ker_transfer_sylow_is_complement P hP).disjoint,
end

lemma ker_transfer_sylow_disjoint' (Q : sylow p G) : disjoint (transfer_sylow P hP).ker ↑Q :=
begin
  obtain ⟨g, hg⟩ := exists_smul_eq G Q P,
  rw [disjoint_iff, ←smul_left_cancel_iff (mul_aut.conj g), smul_bot, smul_inf, smul_normal,
    ←sylow.coe_subgroup_smul, hg, ←disjoint_iff],
  exact ker_transfer_sylow_disjoint P hP,
end

lemma ker_transfer_sylow_disjoint'' (Q : subgroup G) (hQ : is_p_group p Q) :
  disjoint (transfer_sylow P hP).ker Q :=
let ⟨R, hR⟩ := hQ.exists_le_sylow in (ker_transfer_sylow_disjoint' P hP R).mono_right hR

end burnside_transfer

end monoid_hom
