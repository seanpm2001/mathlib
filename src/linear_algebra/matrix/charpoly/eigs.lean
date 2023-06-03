/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import data.polynomial.basic
import field_theory.is_alg_closed.basic

/-!
# Eigenvalues are characteristic polynomial roots.

In fields we show that:

* `matrix.det_eq_prod_roots_charpoly_of_splits`: the determinant (in the field of the matrix)
  is the product of the roots of the characteristic polynomial if the polynomial splits in the field
  of the matrix.
* `matrix.trace_eq_sum_roots_charpoly_of_splits`: the trace is the sum of the roots of the
  characteristic polynomial if the polynomial splits in the field of the matrix.

In an algebraically closed field we show that:

* `matrix.det_eq_prod_roots_charpoly`: the determinant is the product of the roots of the
  characteristic polynomial.
* `matrix.trace_eq_sum_roots_charpoly`: the trace is the sum of the roots of the
  characteristic polynomial.

Note that over other fields such as `ℝ`, these results can be used by using
`A.map (algebra_map ℝ ℂ)` as the matrix, and then applying `ring_hom.map_det`.

The two lemmas `matrix.det_eq_prod_roots_charpoly` and `matrix.trace_eq_sum_roots_charpoly` are more
commonly stated as trace is the sum of eigenvalues and determinant is the product of eigenvalues.
Mathlib has already defined eigenvalues in `linear_algebra.eigenspace` as the roots of the minimal
polynomial of a linear endomorphism. These do not have correct multiplicity and cannot be used in
the theorems above. Hence we express these theorems in terms of the roots of the characteristic
polynomial directly.

## TODO

The proofs of `det_eq_prod_roots_charpoly_of_splits` and
`trace_eq_sum_roots_charpoly_of_splits` closely resemble
`norm_gen_eq_prod_roots` and `trace_gen_eq_sum_roots` respectively, but the
dependencies are not general enough to unify them. We should refactor
`polynomial.prod_roots_eq_coeff_zero_of_monic_of_split` and
`polynomial.sum_roots_eq_next_coeff_of_monic_of_split` to assume splitting over an arbitrary map.
-/
variables {n : Type*} [fintype n] [decidable_eq n]
variables {R : Type*} [field R]
variables {A : matrix n n R}

open matrix polynomial
open_locale matrix big_operators

namespace matrix

lemma det_eq_prod_roots_charpoly_of_splits (hAps : A.charpoly.splits (ring_hom.id R)) :
  A.det = (matrix.charpoly A).roots.prod :=
begin
  rw [det_eq_sign_charpoly_coeff, ← (charpoly_nat_degree_eq_dim A),
    polynomial.prod_roots_eq_coeff_zero_of_monic_of_split A.charpoly_monic (hAps),
    ← mul_assoc, ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul],
end

lemma trace_eq_sum_roots_charpoly_of_splits (hAps : A.charpoly.splits (ring_hom.id R)) :
  A.trace = (matrix.charpoly A).roots.sum :=
begin
  casesI is_empty_or_nonempty n,
  { rw [matrix.trace, fintype.sum_empty, matrix.charpoly,
      det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 h), polynomial.roots_one,
      multiset.empty_eq_zero, multiset.sum_zero], },
  { rw [trace_eq_neg_charpoly_coeff, neg_eq_iff_eq_neg,
      ← polynomial.sum_roots_eq_next_coeff_of_monic_of_split A.charpoly_monic (hAps),
      next_coeff, charpoly_nat_degree_eq_dim,
      if_neg (fintype.card_ne_zero : fintype.card n ≠ 0)], },
end
variables (A)

lemma det_eq_prod_roots_charpoly [is_alg_closed R] : A.det = (matrix.charpoly A).roots.prod :=
det_eq_prod_roots_charpoly_of_splits (is_alg_closed.splits A.charpoly)

lemma trace_eq_sum_roots_charpoly [is_alg_closed R] : A.trace = (matrix.charpoly A).roots.sum :=
trace_eq_sum_roots_charpoly_of_splits (is_alg_closed.splits A.charpoly)

end matrix
