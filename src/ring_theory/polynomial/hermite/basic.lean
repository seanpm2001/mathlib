/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/

import data.polynomial.derivative
import data.nat.parity
import data.nat.factorial.double_factorial
/-!
# Hermite polynomials

This file defines `polynomial.hermite n`, the nth probabilist's Hermite polynomial.

## Main definitions

* `polynomial.hermite n`: the `n`th probabilist's Hermite polynomial,
  defined recursively as a `polynomial ℤ`

## Results

* `polynomial.hermite_succ`: the recursion `hermite (n+1) = (x - d/dx) (hermite n)`
* `polynomial.coeff_hermite_explicit`: a closed formula for (nonvanishing) coefficients in terms
  of binomial coefficients and double factorials.
* `polynomial.coeff_hermite_of_odd_add`: for `n`,`k` where `n+k` is odd, `(hermite n).coeff k` is
  zero.
* `polynomial.coeff_hermite_of_even_add`: a closed formula for `(hermite n).coeff k` when `n+k` is
  even, equivalent to `polynomial.coeff_hermite_explicit`.
* `polynomial.monic_hermite`: for all `n`, `hermite n` is monic.
* `polynomial.degree_hermite`: for all `n`, `hermite n` has degree `n`.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

noncomputable theory
open polynomial

namespace polynomial

/-- the nth probabilist's Hermite polynomial -/
noncomputable def hermite : ℕ → polynomial ℤ
| 0     := 1
| (n+1) := X * (hermite n) - (hermite n).derivative

/-- The recursion `hermite (n+1) = (x - d/dx) (hermite n)` -/
@[simp] lemma hermite_succ (n : ℕ) : hermite (n+1) = X * (hermite n) - (hermite n).derivative :=
by rw hermite

lemma hermite_eq_iterate (n : ℕ) : hermite n = ((λ p, X*p - p.derivative)^[n] 1) :=
begin
  induction n with n ih,
  { refl },
  { rw [function.iterate_succ_apply', ← ih, hermite_succ] }
end

@[simp] lemma hermite_zero : hermite 0 = C 1 := rfl

@[simp] lemma hermite_one : hermite 1 = X :=
begin
  rw [hermite_succ, hermite_zero],
  simp only [map_one, mul_one, derivative_one, sub_zero]
end

/-! ### Lemmas about `polynomial.coeff` -/

section coeff

lemma coeff_hermite_succ_zero (n : ℕ) :
  coeff (hermite (n + 1)) 0 = -(coeff (hermite n) 1) := by simp [coeff_derivative]

lemma coeff_hermite_succ_succ (n k : ℕ) :
  coeff (hermite (n + 1)) (k + 1) = coeff (hermite n) k - (k + 2) * (coeff (hermite n) (k + 2)) :=
begin
  rw [hermite_succ, coeff_sub, coeff_X_mul, coeff_derivative, mul_comm],
  norm_cast
end

lemma coeff_hermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (hermite n) k = 0 :=
begin
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hnk,
  clear hnk,
  induction n with n ih generalizing k,
  { apply coeff_C },
  { have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring,
    rw [nat.succ_eq_add_one, coeff_hermite_succ_succ, add_right_comm, this, ih k, ih (k + 2),
      mul_zero, sub_zero] }
end

@[simp] lemma coeff_hermite_self (n : ℕ) : coeff (hermite n) n = 1 :=
begin
  induction n with n ih,
  { apply coeff_C },
  { rw [coeff_hermite_succ_succ, ih, coeff_hermite_of_lt, mul_zero, sub_zero],
    simp }
end

@[simp] lemma degree_hermite (n : ℕ) : (hermite n).degree = n :=
begin
  rw degree_eq_of_le_of_coeff_ne_zero,
  simp_rw [degree_le_iff_coeff_zero, with_bot.coe_lt_coe],
  { intro m,
    exact coeff_hermite_of_lt },
  { simp [coeff_hermite_self n] }
end

@[simp] lemma nat_degree_hermite {n : ℕ} : (hermite n).nat_degree = n :=
nat_degree_eq_of_degree_eq_some (degree_hermite n)

@[simp] lemma leading_coeff_hermite (n : ℕ) : (hermite n).leading_coeff = 1 :=
begin
  rw [← coeff_nat_degree, nat_degree_hermite, coeff_hermite_self],
end

lemma hermite_monic (n : ℕ) : (hermite n).monic := leading_coeff_hermite n

lemma coeff_hermite_of_odd_add {n k : ℕ} (hnk : odd (n + k)) : coeff (hermite n) k = 0 :=
begin
  induction n with n ih generalizing k,
  { rw zero_add at hnk,
    exact coeff_hermite_of_lt hnk.pos },
  { cases k,
    { rw nat.succ_add_eq_succ_add at hnk,
      rw [coeff_hermite_succ_zero, ih hnk, neg_zero] },
    { rw [coeff_hermite_succ_succ, ih, ih, mul_zero, sub_zero],
      { rwa [nat.succ_add_eq_succ_add] at hnk },
      { rw (by rw [nat.succ_add, nat.add_succ] : n.succ + k.succ = n + k + 2) at hnk,
        exact (nat.odd_add.mp hnk).mpr even_two }}}
end

end coeff

section coeff_explicit

open_locale nat

/-- Because of `coeff_hermite_of_odd_add`, every nonzero coefficient is described as follows. -/
lemma coeff_hermite_explicit :
  ∀ (n k : ℕ), coeff (hermite (2 * n + k)) k = (-1)^n * (2 * n - 1)‼ * nat.choose (2 * n + k) k
| 0 _ := by simp
| (n + 1) 0 := begin
  convert coeff_hermite_succ_zero (2 * n + 1) using 1,
  rw [coeff_hermite_explicit n 1,
      (by ring_nf : 2 * (n + 1) - 1 = 2 * n + 1), nat.double_factorial_add_one,
      nat.choose_zero_right, nat.choose_one_right, pow_succ],
  push_cast,
  ring,
end
| (n + 1) (k + 1) := begin
  let hermite_explicit : ℕ → ℕ → ℤ :=
      λ n k, (-1)^n * (2*n-1)‼ * nat.choose (2*n+k) k,
  have hermite_explicit_recur :
      ∀ (n k : ℕ),
        hermite_explicit (n + 1) (k + 1) =
        hermite_explicit (n + 1) k - (k + 2) * hermite_explicit n (k + 2) :=
    begin
      intros n k,
      simp only [hermite_explicit],
      -- Factor out (-1)'s.
      rw [mul_comm (↑k + _), sub_eq_add_neg],
      nth_rewrite 2 neg_eq_neg_one_mul,
      simp only [mul_assoc, ← mul_add, pow_succ],
      congr' 2,
      -- Factor out double factorials.
      norm_cast,
      rw [(by ring_nf : 2 * (n + 1) - 1 = 2 * n + 1),
          nat.double_factorial_add_one, mul_comm (2 * n + 1)],
      simp only [mul_assoc, ← mul_add],
      congr' 1,
      -- Match up binomial coefficients using `nat.choose_succ_right_eq`.
      rw [(by ring : 2 * (n + 1) + (k + 1) = (2 * n + 1) + (k + 1) + 1),
          (by ring : 2 * (n + 1) + k = (2 * n + 1) + (k + 1)),
          (by ring : 2 * n + (k + 2) = (2 * n + 1) + (k + 1))],
      rw [nat.choose, nat.choose_succ_right_eq ((2 * n + 1) + (k + 1)) (k + 1),
          nat.add_sub_cancel],
      ring,
    end,
  change _ = hermite_explicit _ _,
  rw [← add_assoc, coeff_hermite_succ_succ, hermite_explicit_recur],
  congr,
  { rw coeff_hermite_explicit (n + 1) k },
  { rw [(by ring : 2 * (n + 1) + k = 2 * n + (k + 2)), coeff_hermite_explicit n (k + 2)] },
end

lemma coeff_hermite_of_even_add {n k : ℕ} (hnk : even (n + k)) :
  coeff (hermite n) k = (-1)^((n - k) / 2) * (n - k - 1)‼ * nat.choose n k :=
begin
  cases le_or_lt k n with h_le h_lt,
  { rw [nat.even_add, ← (nat.even_sub h_le)] at hnk,
    obtain ⟨m, hm⟩ := hnk,
    rw [(by linarith : n = 2 * m + k), nat.add_sub_cancel,
        nat.mul_div_cancel_left _ (nat.succ_pos 1), coeff_hermite_explicit] },
  { simp [nat.choose_eq_zero_of_lt h_lt, coeff_hermite_of_lt h_lt] },
end

lemma coeff_hermite (n k : ℕ) :
  coeff (hermite n) k =
  if even (n + k) then (-1)^((n - k) / 2) * (n - k - 1)‼ * nat.choose n k else 0 :=
begin
  split_ifs with h,
  exact coeff_hermite_of_even_add h,
  exact coeff_hermite_of_odd_add (nat.odd_iff_not_even.mpr h),
end

end coeff_explicit

end polynomial
