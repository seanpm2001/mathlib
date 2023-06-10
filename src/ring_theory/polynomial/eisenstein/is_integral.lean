/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import data.nat.choose.dvd
import ring_theory.integrally_closed
import ring_theory.norm
import ring_theory.polynomial.cyclotomic.expand

/-!
# Eisenstein polynomials
In this file we gather more miscellaneous results about Eisenstein polynomials

## Main results
* `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at`: let `K` be the field of fraction
  of an integrally closed domain `R` and let `L` be a separable extension of `K`, generated by an
  integral power basis `B` such that the minimal polynomial of `B.gen` is Eisenstein at `p`. Given
  `z : L` integral over `R`, if `p ^ n • z ∈ adjoin R {B.gen}`, then `z ∈ adjoin R {B.gen}`.
  Together with `algebra.discr_mul_is_integral_mem_adjoin` this result often allows to compute the
  ring of integers of `L`.

-/

universes u v w z

variables {R : Type u}

open ideal algebra finset

open_locale big_operators polynomial

section cyclotomic

variables (p : ℕ)

local notation `𝓟` := submodule.span ℤ {p}

open polynomial

lemma cyclotomic_comp_X_add_one_is_eisenstein_at [hp : fact p.prime] :
  ((cyclotomic p ℤ).comp (X + 1)).is_eisenstein_at 𝓟 :=
begin
  refine monic.is_eisenstein_at_of_mem_of_not_mem _
    (ideal.is_prime.ne_top $(ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).2 $
    nat.prime_iff_prime_int.1 hp.out) (λ i hi, _) _,
  { rw [show (X + 1 : ℤ[X]) = X + C 1, by simp],
    refine ((cyclotomic.monic p ℤ).comp (monic_X_add_C 1) (λ h, _)),
    rw [nat_degree_X_add_C] at h,
    exact zero_ne_one h.symm },
  { rw [cyclotomic_prime, geom_sum_X_comp_X_add_one_eq_sum, ← lcoeff_apply,
      linear_map.map_sum],
    conv { congr, congr, skip, funext,
      rw [lcoeff_apply, ← C_eq_nat_cast, C_mul_X_pow_eq_monomial, coeff_monomial] },
    rw [nat_degree_comp, show (X + 1 : ℤ[X]) = X + C 1, by simp, nat_degree_X_add_C, mul_one,
      nat_degree_cyclotomic, nat.totient_prime hp.out] at hi,
    simp only [hi.trans_le (nat.sub_le _ _), sum_ite_eq', mem_range, if_true,
      ideal.submodule_span_eq, ideal.mem_span_singleton, int.coe_nat_dvd],
    exact hp.out.dvd_choose_self i.succ_ne_zero (lt_tsub_iff_right.1 hi) },
  { rw [coeff_zero_eq_eval_zero, eval_comp, cyclotomic_prime, eval_add, eval_X,
      eval_one, zero_add, eval_geom_sum, one_geom_sum,
      ideal.submodule_span_eq, ideal.span_singleton_pow, ideal.mem_span_singleton],
    intro h,
    obtain ⟨k, hk⟩ := int.coe_nat_dvd.1 h,
    rw [← mul_assoc, mul_one, mul_assoc] at hk,
    nth_rewrite 0 [← nat.mul_one p] at hk,
    rw [mul_right_inj' hp.out.ne_zero] at hk,
    exact nat.prime.not_dvd_one hp.out (dvd.intro k (hk.symm)) }
end

lemma cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at [hp : fact p.prime] (n : ℕ) :
  ((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).is_eisenstein_at 𝓟 :=
begin
  refine monic.is_eisenstein_at_of_mem_of_not_mem _
    (ideal.is_prime.ne_top $(ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).2 $
    nat.prime_iff_prime_int.1 hp.out) _ _,
  { rw [show (X + 1 : ℤ[X]) = X + C 1, by simp],
    refine ((cyclotomic.monic _ ℤ).comp (monic_X_add_C 1) (λ h, _)),
    rw [nat_degree_X_add_C] at h,
    exact zero_ne_one h.symm },
  { induction n with n hn,
    { intros i hi,
      rw [zero_add, pow_one] at hi ⊢,
      exact (cyclotomic_comp_X_add_one_is_eisenstein_at p).mem hi },
    { intros i hi,
      rw [ideal.submodule_span_eq, ideal.mem_span_singleton, ← zmod.int_coe_zmod_eq_zero_iff_dvd,
        ← int.coe_cast_ring_hom, ← coeff_map, map_comp, map_cyclotomic, polynomial.map_add, map_X,
        polynomial.map_one, pow_add, pow_one, cyclotomic_mul_prime_dvd_eq_pow, pow_comp,
        ← zmod.expand_card, coeff_expand hp.out.pos],
      { simp only [ite_eq_right_iff],
        rintro ⟨k, hk⟩,
        rw [nat_degree_comp, show (X + 1 : ℤ[X]) = X + C 1, by simp, nat_degree_X_add_C,
          mul_one, nat_degree_cyclotomic, nat.totient_prime_pow hp.out (nat.succ_pos _),
          nat.succ_sub_one] at hn hi,
        rw [hk, pow_succ, mul_assoc] at hi,
        rw [hk, mul_comm, nat.mul_div_cancel _ hp.out.pos],
        replace hn := hn (lt_of_mul_lt_mul_left' hi),
        rw [ideal.submodule_span_eq, ideal.mem_span_singleton,
          ← zmod.int_coe_zmod_eq_zero_iff_dvd, ← int.coe_cast_ring_hom, ← coeff_map] at hn,
        simpa [map_comp] using hn },
      { exact ⟨p ^ n, by rw [pow_succ]⟩ } } },
  { rw [coeff_zero_eq_eval_zero, eval_comp, cyclotomic_prime_pow_eq_geom_sum hp.out, eval_add,
      eval_X, eval_one, zero_add, eval_finset_sum],
    simp only [eval_pow, eval_X, one_pow, sum_const, card_range, nat.smul_one_eq_coe,
      submodule_span_eq, ideal.submodule_span_eq,
      ideal.span_singleton_pow, ideal.mem_span_singleton],
    intro h,
    obtain ⟨k, hk⟩ := int.coe_nat_dvd.1 h,
    rw [← mul_assoc, mul_one, mul_assoc] at hk,
    nth_rewrite 0 [← nat.mul_one p] at hk,
    rw [mul_right_inj' hp.out.ne_zero] at hk,
    exact nat.prime.not_dvd_one hp.out (dvd.intro k (hk.symm)) }
end

end cyclotomic

section is_integral

variables {K : Type v} {L : Type z} {p : R} [comm_ring R] [field K] [field L]
variables [algebra K L] [algebra R L] [algebra R K] [is_scalar_tower R K L] [is_separable K L]
variables [is_domain R] [is_fraction_ring R K] [is_integrally_closed R]

local notation `𝓟` := submodule.span R {p}

open is_integrally_closed power_basis nat polynomial is_scalar_tower

/-- Let `K` be the field of fraction of an integrally closed domain `R` and let `L` be a separable
extension of `K`, generated by an integral power basis `B` such that the minimal polynomial of
`B.gen` is Eisenstein at `p`. Given `z : L` integral over `R`, if `Q : R[X]` is such that
`aeval B.gen Q = p • z`, then `p ∣ Q.coeff 0`. -/
lemma dvd_coeff_zero_of_aeval_eq_prime_smul_of_minpoly_is_eiseinstein_at {B : power_basis K L}
  (hp : prime p) (hBint : is_integral R B.gen) {z : L} {Q : R[X]}
  (hQ : aeval B.gen Q = p • z) (hzint : is_integral R z)
  (hei : (minpoly R B.gen).is_eisenstein_at 𝓟) : p ∣ Q.coeff 0 :=
begin
  -- First define some abbreviations.
  letI := B.finite_dimensional,
  let P := minpoly R B.gen,
  obtain ⟨n , hn⟩ := nat.exists_eq_succ_of_ne_zero B.dim_pos.ne',
  have finrank_K_L : finite_dimensional.finrank K L = B.dim := B.finrank,
  have deg_K_P : (minpoly K B.gen).nat_degree = B.dim := B.nat_degree_minpoly,
  have deg_R_P : P.nat_degree = B.dim,
  { rw [← deg_K_P, minpoly.is_integrally_closed_eq_field_fractions' K hBint,
        (minpoly.monic hBint).nat_degree_map (algebra_map R K)] },
  choose! f hf using hei.is_weakly_eisenstein_at.exists_mem_adjoin_mul_eq_pow_nat_degree_le
    (minpoly.aeval R B.gen) (minpoly.monic hBint),
  simp only [(minpoly.monic hBint).nat_degree_map, deg_R_P] at hf,

  -- The Eisenstein condition shows that `p` divides `Q.coeff 0`
  -- if `p^n.succ` divides the following multiple of `Q.coeff 0^n.succ`:
  suffices : p ^ n.succ ∣
    (Q.coeff 0 ^ n.succ * ((-1) ^ (n.succ * n) * (minpoly R B.gen).coeff 0 ^ n)),
  { have hndiv : ¬ p ^ 2 ∣ ((minpoly R B.gen)).coeff 0 := λ h,
      hei.not_mem ((span_singleton_pow p 2).symm ▸ (ideal.mem_span_singleton.2 h)),
    refine prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd hp ((_ : _ ^ n.succ ∣ _)) hndiv,
    convert (is_unit.dvd_mul_right ⟨(-1) ^ (n.succ * n), rfl⟩).mpr this using 1,
    push_cast,
    ring_nf, simp [pow_right_comm _ _ 2] },

  -- We claim the quotient of `Q^n * _` by `p^n` is the following `r`:
  have aux : ∀ i ∈ (range (Q.nat_degree + 1)).erase 0, B.dim ≤ i + n,
  { intros i hi,
    simp only [mem_range, mem_erase] at hi,
    rw [hn],
    exact le_add_pred_of_pos _ hi.1 },
  have hintsum : is_integral R (z * B.gen ^ n -
    ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0, Q.coeff x • f (x + n)),
  { refine is_integral_sub (is_integral_mul hzint (is_integral.pow hBint _))
      (is_integral.sum _ (λ i hi, (is_integral_smul _ _))),
    exact adjoin_le_integral_closure hBint (hf _ (aux i hi)).1 },
  obtain ⟨r, hr⟩ := is_integral_iff.1 (is_integral_norm K hintsum),
  use r,

  -- Do the computation in `K` so we can work in terms of `z` instead of `r`.
  apply is_fraction_ring.injective R K,
  simp only [_root_.map_mul, _root_.map_pow, _root_.map_neg, _root_.map_one],
  -- Both sides are actually norms:
  calc _ = norm K (Q.coeff 0 • B.gen ^ n) : _
  ... = norm K (p • (z * B.gen ^ n) - ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0,
          p • Q.coeff x • f (x + n))
    : congr_arg (norm K) (eq_sub_of_add_eq _)
  ... = _ : _,
  { simp only [algebra.smul_def, algebra_map_apply R K L, algebra.norm_algebra_map, _root_.map_mul,
      _root_.map_pow, finrank_K_L, power_basis.norm_gen_eq_coeff_zero_minpoly,
      minpoly.is_integrally_closed_eq_field_fractions' K hBint, coeff_map, ← hn],
    ring_exp },
  swap, { simp_rw [← smul_sum, ← smul_sub, algebra.smul_def p, algebra_map_apply R K L,
      _root_.map_mul, algebra.norm_algebra_map, finrank_K_L, hr, ← hn] },

  calc _ = (Q.coeff 0 • 1 + ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0,
              Q.coeff x • B.gen ^ x) * B.gen ^ n : _
  ... = (Q.coeff 0 • B.gen ^ 0 + ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0,
              Q.coeff x • B.gen ^ x) * B.gen ^ n : by rw pow_zero
  ... = (aeval B.gen Q) * B.gen ^ n : _
  ... = _ : by rw [hQ, algebra.smul_mul_assoc],
  { have : ∀ i ∈ (range (Q.nat_degree + 1)).erase 0,
      Q.coeff i • (B.gen ^ i * B.gen ^ n) =
      p • Q.coeff i • f (i + n),
    { intros i hi,
      rw [←pow_add, ←(hf _ (aux i hi)).2, ←algebra.smul_def, smul_smul, mul_comm _ p, smul_smul] },
    simp only [add_mul, smul_mul_assoc, one_mul, sum_mul, sum_congr rfl this] },
  { rw [aeval_eq_sum_range,
        finset.add_sum_erase (range (Q.nat_degree + 1)) (λ i, Q.coeff i • B.gen ^ i)],
    simp },
end

lemma mem_adjoin_of_dvd_coeff_of_dvd_aeval {A B : Type*} [comm_semiring A] [comm_ring B]
  [algebra A B] [no_zero_smul_divisors A B] {Q : A[X]} {p : A} {x z : B} (hp : p ≠ 0)
  (hQ : ∀ i ∈ range (Q.nat_degree + 1), p ∣ Q.coeff i) (hz : aeval x Q = p • z) :
  z ∈ adjoin A ({x} : set B) :=
begin
  choose! f hf using hQ,
  rw [aeval_eq_sum_range, sum_range] at hz,
  conv_lhs at hz { congr, skip, funext,
    rw [hf i (mem_range.2 (fin.is_lt i)), ← smul_smul] },
  rw [← smul_sum] at hz,
  rw [← smul_right_injective _ hp hz],
  exact subalgebra.sum_mem _ (λ _ _, subalgebra.smul_mem _
    (subalgebra.pow_mem _ (subset_adjoin (set.mem_singleton _)) _) _)
end

/-- Let `K` be the field of fraction of an integrally closed domain `R` and let `L` be a separable
extension of `K`, generated by an integral power basis `B` such that the minimal polynomial of
`B.gen` is Eisenstein at `p`. Given `z : L` integral over `R`, if `p • z ∈ adjoin R {B.gen}`, then
`z ∈ adjoin R {B.gen}`. -/
lemma mem_adjoin_of_smul_prime_smul_of_minpoly_is_eiseinstein_at {B : power_basis K L}
  (hp : prime p) (hBint : is_integral R B.gen) {z : L} (hzint : is_integral R z)
  (hz : p • z ∈ adjoin R ({B.gen} : set L)) (hei : (minpoly R B.gen).is_eisenstein_at 𝓟) :
  z ∈ adjoin R ({B.gen} : set L) :=
begin
  -- First define some abbreviations.
  have hndiv : ¬ p ^ 2 ∣ ((minpoly R B.gen)).coeff 0 := λ h,
    hei.not_mem ((span_singleton_pow p 2).symm ▸ (ideal.mem_span_singleton.2 h)),
  letI := finite_dimensional B,
  set P := minpoly R B.gen with hP,
  obtain ⟨n , hn⟩ := nat.exists_eq_succ_of_ne_zero B.dim_pos.ne',
  haveI : no_zero_smul_divisors R L := no_zero_smul_divisors.trans R K L,
  let P₁ := P.map (algebra_map R L),

  -- There is a polynomial `Q` such that `p • z = aeval B.gen Q`. We can assume that
  -- `Q.degree < P.degree` and `Q ≠ 0`.
  rw [adjoin_singleton_eq_range_aeval] at hz,
  obtain ⟨Q₁, hQ⟩ := hz,
  set Q := Q₁ %ₘ P with hQ₁,
  replace hQ : aeval B.gen Q = p • z,
  { rw [← mod_by_monic_add_div Q₁ (minpoly.monic hBint)] at hQ,
    simpa using hQ },
  by_cases hQzero : Q = 0,
  { simp only [hQzero, algebra.smul_def, zero_eq_mul, aeval_zero] at hQ,
    cases hQ with H H₁,
    { have : function.injective (algebra_map R L),
      { rw [algebra_map_eq R K L],
        exact (algebra_map K L).injective.comp (is_fraction_ring.injective R K) },      exfalso,
      exact hp.ne_zero ((injective_iff_map_eq_zero _).1 this _ H) },
    { rw [H₁],
      exact subalgebra.zero_mem _ } },

  -- It is enough to prove that all coefficients of `Q` are divisible by `p`, by induction.
  -- The base case is `dvd_coeff_zero_of_aeval_eq_prime_smul_of_minpoly_is_eiseinstein_at`.
  refine mem_adjoin_of_dvd_coeff_of_dvd_aeval hp.ne_zero (λ i, _) hQ,
  refine nat.case_strong_induction_on i _ (λ j hind, _),
  { intro H,
    exact dvd_coeff_zero_of_aeval_eq_prime_smul_of_minpoly_is_eiseinstein_at
      hp hBint hQ hzint hei },
  { intro hj,
    refine hp.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd _ hndiv,
    exact n,

    -- Two technical results we will need about `P.nat_degree` and `Q.nat_degree`.
    have H := degree_mod_by_monic_lt Q₁ (minpoly.monic hBint),
    rw [← hQ₁, ← hP] at H,
    replace H:= nat.lt_iff_add_one_le.1 (lt_of_lt_of_le (lt_of_le_of_lt
      (nat.lt_iff_add_one_le.1 (nat.lt_of_succ_lt_succ (mem_range.1 hj))) (lt_succ_self _))
      (nat.lt_iff_add_one_le.1 (((nat_degree_lt_nat_degree_iff hQzero).2 H)))),
    rw [add_assoc] at H,
    have Hj : Q.nat_degree + 1 = j + 1 + (Q.nat_degree - j),
    { rw [← add_comm 1, ← add_comm 1, add_assoc, add_right_inj, ← nat.add_sub_assoc
        (nat.lt_of_succ_lt_succ (mem_range.1 hj)).le, add_comm, nat.add_sub_cancel] },

    -- By induction hypothesis we can find `g : ℕ → R` such that
    -- `k ∈ range (j + 1) → Q.coeff k • B.gen ^ k = (algebra_map R L) p * g k • B.gen ^ k`-
    choose! g hg using hind,
    replace hg : ∀ k ∈ range (j + 1), Q.coeff k • B.gen ^ k =
      (algebra_map R L p) * (g k • B.gen ^ k),
    { intros k hk,
      rw [hg k (mem_range_succ_iff.1 hk) (mem_range_succ_iff.2 (le_trans (mem_range_succ_iff.1 hk)
        (succ_le_iff.1 (mem_range_succ_iff.1 hj)).le)), algebra.smul_def, algebra.smul_def,
        ring_hom.map_mul, mul_assoc] },

    -- Since `minpoly R B.gen` is Eiseinstein, we can find `f : ℕ → L` such that
    -- `(map (algebra_map R L) (minpoly R B.gen)).nat_degree ≤ i` implies `f i ∈ adjoin R {B.gen}`
    -- and `(algebra_map R L) p * f i = B.gen ^ i`. We will also need `hf₁`, a reformulation of this
    -- property.
    choose! f hf using (is_weakly_eisenstein_at.exists_mem_adjoin_mul_eq_pow_nat_degree_le
    (minpoly.aeval R B.gen) (minpoly.monic hBint) hei.is_weakly_eisenstein_at),
    have hf₁ : ∀ k ∈ (range (Q.nat_degree - j)).erase 0,
      Q.coeff (j + 1 + k) • B.gen ^ (j + 1 + k) * B.gen ^ (P.nat_degree - (j + 2)) =
      (algebra_map R L) p * Q.coeff (j + 1 + k) • f (k + P.nat_degree - 1),
    { intros k hk,
      rw [smul_mul_assoc, ← pow_add, ← nat.add_sub_assoc H, ← add_assoc j 1 1,
        add_comm (j + 1) 1, add_assoc (j + 1), add_comm _ (k + P.nat_degree),
        nat.add_sub_add_right, ← (hf (k + P.nat_degree - 1) _).2, mul_smul_comm],
      rw [(minpoly.monic hBint).nat_degree_map, add_comm, nat.add_sub_assoc,
        le_add_iff_nonneg_right],
      { exact nat.zero_le _ },
      { refine one_le_iff_ne_zero.2 (λ h, _),
        rw [h] at hk,
        simpa using hk },
      { apply_instance } },

  -- The Eisenstein condition shows that `p` divides `Q.coeff j`
  -- if `p^n.succ` divides the following multiple of `Q.coeff (succ j)^n.succ`:
   suffices : p ^ n.succ ∣
    Q.coeff (succ j) ^ n.succ * (minpoly R B.gen).coeff 0 ^ (succ j + (P.nat_degree - (j + 2))),
  { convert this,
    rw [nat.succ_eq_add_one, add_assoc, ← nat.add_sub_assoc H, ← add_assoc, add_comm (j + 1),
      nat.add_sub_add_left, ← nat.add_sub_assoc, nat.add_sub_add_left, hP,
      ← (minpoly.monic hBint).nat_degree_map  (algebra_map R K),
      ← minpoly.is_integrally_closed_eq_field_fractions' K hBint, nat_degree_minpoly, hn,
        nat.sub_one, nat.pred_succ],
    linarith },

  -- Using `hQ : aeval B.gen Q = p • z`, we write `p • z` as a sum of terms of degree less than
  -- `j+1`, that are multiples of `p` by induction, and terms of degree at least `j+1`.
  rw [aeval_eq_sum_range, Hj, range_add, sum_union (disjoint_range_add_left_embedding _ _),
      sum_congr rfl hg, add_comm] at hQ,
  -- We multiply this equality by `B.gen ^ (P.nat_degree-(j+2))`, so we can use `hf₁` on the terms
  -- we didn't know were multiples of `p`, and we take the norm on both sides.
  replace hQ := congr_arg (λ x, x * B.gen ^ (P.nat_degree - (j + 2))) hQ,
  simp_rw [sum_map, add_left_embedding_apply, add_mul, sum_mul, mul_assoc] at hQ,
  rw [← insert_erase (mem_range.2 (tsub_pos_iff_lt.2 $ nat.lt_of_succ_lt_succ $ mem_range.1 hj)),
      sum_insert (not_mem_erase 0 _), add_zero, sum_congr rfl hf₁, ← mul_sum, ← mul_sum,
      add_assoc, ← mul_add, smul_mul_assoc, ← pow_add, algebra.smul_def] at hQ,
  replace hQ := congr_arg (norm K) (eq_sub_of_add_eq hQ),

  -- We obtain an equality of elements of `K`, but everything is integral, so we can move to `R`
  -- and simplify `hQ`.
  have hintsum : is_integral R (z * B.gen ^ (P.nat_degree - (j + 2)) -
      (∑ (x : ℕ) in (range (Q.nat_degree - j)).erase 0, Q.coeff (j + 1 + x) •
        f (x + P.nat_degree - 1) +
      ∑ (x : ℕ) in range (j + 1), g x • B.gen ^ x * B.gen ^ (P.nat_degree - (j + 2)))),
    { refine is_integral_sub (is_integral_mul hzint (is_integral.pow hBint _))
        (is_integral_add (is_integral.sum _ (λ k hk, is_integral_smul _ _))
        (is_integral.sum _ (λ k hk, is_integral_mul (is_integral_smul _ (is_integral.pow hBint _))
        ((is_integral.pow hBint _))))),
      refine adjoin_le_integral_closure hBint (hf _ _).1,
      rw [(minpoly.monic hBint).nat_degree_map (algebra_map R L)],
      rw [add_comm, nat.add_sub_assoc, le_add_iff_nonneg_right],
      { exact zero_le _ },
      { refine one_le_iff_ne_zero.2 (λ h, _),
        rw [h] at hk,
        simpa using hk } },
    obtain ⟨r, hr⟩ := is_integral_iff.1 (is_integral_norm K hintsum),
    rw [algebra.smul_def, mul_assoc, ← mul_sub, _root_.map_mul, algebra_map_apply R K L, map_pow,
      algebra.norm_algebra_map, _root_.map_mul, algebra_map_apply R K L, algebra.norm_algebra_map,
      finrank B, ← hr, power_basis.norm_gen_eq_coeff_zero_minpoly,
      minpoly.is_integrally_closed_eq_field_fractions' K hBint,
      coeff_map, show (-1 : K) = algebra_map R K (-1), by simp, ← map_pow, ← map_pow,
      ← _root_.map_mul, ← map_pow, ← _root_.map_mul, ← map_pow, ← _root_.map_mul] at hQ,

    -- We can now finish the proof.
    have hppdiv : p ^ B.dim ∣ p ^ B.dim * r := dvd_mul_of_dvd_left dvd_rfl _,
    rwa [← is_fraction_ring.injective R K hQ, mul_comm, ← units.coe_neg_one, mul_pow,
      ← units.coe_pow, ← units.coe_pow, mul_assoc, is_unit.dvd_mul_left _ _ _ ⟨_, rfl⟩, mul_comm,
      ← nat.succ_eq_add_one, hn] at hppdiv }
end

/-- Let `K` be the field of fraction of an integrally closed domain `R` and let `L` be a separable
extension of `K`, generated by an integral power basis `B` such that the minimal polynomial of
`B.gen` is Eisenstein at `p`. Given `z : L` integral over `R`, if `p ^ n • z ∈ adjoin R {B.gen}`,
then `z ∈ adjoin R {B.gen}`. Together with `algebra.discr_mul_is_integral_mem_adjoin` this result
often allows to compute the ring of integers of `L`. -/
lemma mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at {B : power_basis K L}
  (hp : prime p) (hBint : is_integral R B.gen) {n : ℕ} {z : L} (hzint : is_integral R z)
  (hz : p ^ n • z ∈ adjoin R ({B.gen} : set L)) (hei : (minpoly R B.gen).is_eisenstein_at 𝓟) :
  z ∈ adjoin R ({B.gen} : set L) :=
begin
  induction n with n hn,
  { simpa using hz },
  { rw [pow_succ, mul_smul] at hz,
    exact hn (mem_adjoin_of_smul_prime_smul_of_minpoly_is_eiseinstein_at
      hp hBint (is_integral_smul _ hzint) hz hei) }
end

end is_integral
