/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
import topology.algebra.order.monotone_continuity
import topology.instances.nnreal
import tactic.norm_cast
import tactic.ring_exp

/-!
# Square root of a real number

In this file we define

* `nnreal.sqrt` to be the square root of a nonnegative real number.
* `real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.

Then we prove some basic properties of these functions.

## Implementation notes

We define `nnreal.sqrt` as the noncomputable inverse to the function `x ↦ x * x`. We use general
theory of inverses of strictly monotone functions to prove that `nnreal.sqrt x` exists. As a side
effect, `nnreal.sqrt` is a bundled `order_iso`, so for `nnreal` numbers we get continuity as well as
theorems like `sqrt x ≤ y ↔ x * x ≤ y` for free.

Then we define `real.sqrt x` to be `nnreal.sqrt (real.to_nnreal x)`. We also define a Cauchy
sequence `real.sqrt_aux (f : cau_seq ℚ abs)` which converges to `sqrt (mk f)` but do not prove (yet)
that this sequence actually converges to `sqrt (mk f)`.

## Tags

square root
-/

open set filter
open_locale filter nnreal topological_space

namespace nnreal

variables {x y : ℝ≥0}

/-- Square root of a nonnegative real number. -/
@[pp_nodot] noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
order_iso.symm $ strict_mono.order_iso_of_surjective (λ x, x * x)
  (λ x y h, mul_self_lt_mul_self x.2 h) $
  (continuous_id.mul continuous_id).surjective tendsto_mul_self_at_top $
    by simp [order_bot.at_bot_eq]

lemma sqrt_le_sqrt_iff : sqrt x ≤ sqrt y ↔ x ≤ y :=
sqrt.le_iff_le

lemma sqrt_lt_sqrt_iff : sqrt x < sqrt y ↔ x < y :=
sqrt.lt_iff_lt

lemma sqrt_eq_iff_sq_eq : sqrt x = y ↔ y * y = x :=
sqrt.to_equiv.apply_eq_iff_eq_symm_apply.trans eq_comm

lemma sqrt_le_iff : sqrt x ≤ y ↔ x ≤ y * y :=
sqrt.to_galois_connection _ _

lemma le_sqrt_iff : x ≤ sqrt y ↔ x * x ≤ y :=
(sqrt.symm.to_galois_connection _ _).symm

@[simp] lemma sqrt_eq_zero : sqrt x = 0 ↔ x = 0 :=
sqrt_eq_iff_sq_eq.trans $ by rw [eq_comm, zero_mul]

@[simp] lemma sqrt_zero : sqrt 0 = 0 := sqrt_eq_zero.2 rfl

@[simp] lemma sqrt_one : sqrt 1 = 1 := sqrt_eq_iff_sq_eq.2 $ mul_one 1

@[simp] lemma mul_self_sqrt (x : ℝ≥0) : sqrt x * sqrt x = x :=
sqrt.symm_apply_apply x

@[simp] lemma sqrt_mul_self (x : ℝ≥0) : sqrt (x * x) = x := sqrt.apply_symm_apply x

@[simp] lemma sq_sqrt (x : ℝ≥0) : (sqrt x)^2 = x :=
by rw [sq, mul_self_sqrt x]

@[simp] lemma sqrt_sq (x : ℝ≥0) : sqrt (x^2) = x :=
by rw [sq, sqrt_mul_self x]

lemma sqrt_mul (x y : ℝ≥0) : sqrt (x * y) = sqrt x * sqrt y :=
by rw [sqrt_eq_iff_sq_eq, mul_mul_mul_comm, mul_self_sqrt, mul_self_sqrt]

/-- `nnreal.sqrt` as a `monoid_with_zero_hom`. -/
noncomputable def sqrt_hom : ℝ≥0 →*₀ ℝ≥0 := ⟨sqrt, sqrt_zero, sqrt_one, sqrt_mul⟩

lemma sqrt_inv (x : ℝ≥0) : sqrt (x⁻¹) = (sqrt x)⁻¹ := sqrt_hom.map_inv x

lemma sqrt_div (x y : ℝ≥0) : sqrt (x / y) = sqrt x / sqrt y := sqrt_hom.map_div x y

lemma continuous_sqrt : continuous sqrt := sqrt.continuous

end nnreal

namespace real

/-- An auxiliary sequence of rational numbers that converges to `real.sqrt (mk f)`.
This is Heron's method for computing square roots.
Currently this sequence is not used in `mathlib`.  -/
def sqrt_aux (f : cau_seq ℚ abs) : ℕ → ℚ
| 0       := max 1 (f 0)
| (n + 1) := let s := sqrt_aux n in (s + (max 0 (f (n+1))) / s) / 2

@[simp]
lemma sqrt_aux_zero (f : cau_seq ℚ abs) : sqrt_aux f 0 = max 1 (f 0) :=
by unfold sqrt_aux

theorem sqrt_aux_nonneg (f : cau_seq ℚ abs) (i : ℕ): 0 ≤ sqrt_aux f i :=
begin
  induction i with i hyp,
  { rw sqrt_aux_zero f,
    have r : 1 ≤ max 1 (f 0) := le_max_left 1 _,
    linarith, },
  { unfold sqrt_aux,
    simp, cancel_denoms,
    have t : 0 ≤ max 0 (f (i + 1)) / sqrt_aux f i := div_nonneg (le_max_left 0 _) hyp,
    exact add_nonneg hyp t, },
end

theorem sqrt_aux_ne_zero_step (f : cau_seq ℚ abs) (i : ℕ) (h : sqrt_aux f i ≠ 0) :
  sqrt_aux f (i + 1) ≠ 0 :=
begin
  unfold sqrt_aux,
  simp only [ne.def, div_eq_zero_iff, bit0_eq_zero, one_ne_zero, or_false],
  apply ne_of_gt,
  have t : 0 ≤ (max 0 (f (i + 1))) / sqrt_aux f i,
  { rw div_nonneg_iff,
    left,
    exact ⟨le_max_left 0 _, sqrt_aux_nonneg f i⟩, },
  have u : 0 < sqrt_aux f i := (ne.symm h).le_iff_lt.mp (sqrt_aux_nonneg f i),
  exact lt_add_of_pos_of_le u t
end

theorem sqrt_aux_eq_zero_iff_step (f : cau_seq ℚ abs) (i : ℕ) :
  sqrt_aux f (i + 1) = 0 ↔ sqrt_aux f i = 0 :=
begin
  split,
  { intros hyp,
    { by_contradiction,
      exact sqrt_aux_ne_zero_step f i h hyp, }, },
  { intro prev_zero,
    unfold sqrt_aux, rw [prev_zero], simp, },
end

@[simp]
theorem sqrt_aux_ne_zero (f : cau_seq ℚ abs) (i : ℕ) : sqrt_aux f i ≠ 0 :=
begin
  induction i with i hyp,
  { rw sqrt_aux,
    norm_num,
    have r : 1 ≤ max 1 (f 0) := le_max_left 1 _,
    linarith, },
  { intros h, rw sqrt_aux_eq_zero_iff_step f i at h, exact hyp h, },
end

theorem sqrt_aux_pos (f : cau_seq ℚ abs) (i : ℕ) : 0 < sqrt_aux f i :=
(sqrt_aux_ne_zero f i).symm.le_iff_lt.mp (sqrt_aux_nonneg f i)

lemma foo (a : ℚ) {b: ℚ} (b_nonneg : b ≠ 0) : a * b / b = a :=
begin
  exact (div_eq_iff b_nonneg).mpr rfl
end

lemma div_le_div_right' (a b c : ℚ) (c_pos : 0 < c) (h : a ≤ b) : a / c ≤ b / c :=
begin
  exact (div_le_div_right c_pos).mpr h
end

theorem bound (q : ℚ) : 2 * q - q * q ≤ 1 :=
begin
  suffices pr : 0 ≤ q * q - 2 * q + 1,
  { linarith, },
  calc 0 ≤ (q - 1) ^ 2 : sq_nonneg _
  ... = q * q - 2 * q + 1 : by ring,
end

/--
If f > 1, and we pick `N` such that `f i` is always greater than 1 from `N` onwards,
and at some point past `N` we find sqrt_aux gets above `1`, then it will stay above `1` forever.
This theorem is the inductive step of that assertion.
-/
theorem sqrt_aux_ge_one_step (f : cau_seq ℚ abs) (i : ℕ) (f_large : 1 ≤ f (i + 1))
  : 1 ≤ sqrt_aux f (i + 1) :=
begin
  unfold sqrt_aux, simp,
  cancel_denoms,
  have t : 0 ≤ f (i + 1) := by linarith,
  rw max_eq_right t,
  have pos: 0 < sqrt_aux f i := sqrt_aux_pos f i,
  suffices pr : 2 * sqrt_aux f i ≤ sqrt_aux f i * sqrt_aux f i + f (i + 1),
  { calc 2 = 2 * sqrt_aux f i / sqrt_aux f i : by rw foo 2 (sqrt_aux_ne_zero f i)
    ... ≤ (sqrt_aux f i * sqrt_aux f i + f (i + 1)) / sqrt_aux f i : (div_le_div_right (sqrt_aux_pos f i)).2 pr
    ... = (sqrt_aux f i * sqrt_aux f i / sqrt_aux f i + f (i + 1) / sqrt_aux f i) : by ring
    ... = (sqrt_aux f i + f (i + 1) / sqrt_aux f i) : by rw foo (sqrt_aux f i) (sqrt_aux_ne_zero f i), },
  suffices pr : 2 * sqrt_aux f i - sqrt_aux f i * sqrt_aux f i ≤ f (i + 1),
  { linarith, },
  calc 2 * sqrt_aux f i - sqrt_aux f i * sqrt_aux f i ≤ 1 : bound (sqrt_aux f i)
    ... ≤ f (i + 1) : f_large,
end

theorem sqrt_aux_ge_one (f : cau_seq ℚ abs) (N : ℕ) (f_gt_1 : ∀ i ≥ N, 1 ≤ f i) :
  ∀ (k ≥ N), 1 ≤ sqrt_aux f k
| 0 pr :=
begin
  rw sqrt_aux_zero f,
  exact le_max_left 1 _
end
| (k + 1) pr := sqrt_aux_ge_one_step f k (f_gt_1 (k + 1) pr)

/-- A simplified version of the AM-GM inequality on a two-element set, which we prove separately to
reduce the import graph. -/
theorem rat.am_gm (a b : ℚ) : 4 * a * b ≤ (a + b) ^ 2 :=
begin
  suffices pos: 0 ≤ (a + b) ^ 2 - 4 * a * b, exact sub_nonneg.mp pos,
  calc 0 ≤ (a - b) ^ 2 : sq_nonneg (a - b)
    ... = (a + b) ^ 2 - 4 * a * b : by ring,
end

lemma sq_div_self {a : ℚ} (a_nonzero : a ≠ 0) : a ^ 2 / a = a :=
by rw [pow_two, div_eq_iff a_nonzero]

theorem sqrt_aux_overestimate (f : cau_seq ℚ abs) (i : ℕ) :
  f i ≤ (sqrt_aux f i) ^ 2 :=
begin
  cases i,
  { rw sqrt_aux_zero,
    by_cases 1 ≤ f 0,
    { rw max_eq_right h,
      nlinarith, },
    { simp at h,
      rw max_eq_left_of_lt h,
      simp, exact (le_of_lt h), }, },
  { unfold sqrt_aux,
    simp,
    norm_num,
    cases le_or_gt (f (i + 1)) 0,
    { rw max_eq_left h,
      simp,
      calc f (i + 1) ≤ 0 : h
        ... ≤ sqrt_aux f i ^ 2 / 4 : div_nonneg (sq_nonneg _) (by norm_num), },
    { rw max_eq_right_of_lt h,
      { cancel_denoms,
        have u : _ := rat.am_gm (sqrt_aux f i ^ 2) (f (i + 1)),
        have v := by
          calc 4 * f (i + 1) = 4 * f (i + 1) * 1 : by ring
          ... = 4 * f (i + 1) * (sqrt_aux f i ^ 2 / sqrt_aux f i ^ 2) : by rw div_self (pow_ne_zero 2 (sqrt_aux_ne_zero f _))
          ... = (4 * sqrt_aux f i ^ 2 * f (i + 1)) / sqrt_aux f i ^ 2 : by ring,
        rw v,
        calc 4 * sqrt_aux f i ^ 2 * f (i + 1) / sqrt_aux f i ^ 2
          ≤ (sqrt_aux f i ^ 2 + f (i + 1)) ^ 2 / sqrt_aux f i ^ 2 : div_le_div_of_le (sq_nonneg _) u
          ... = ((sqrt_aux f i ^ 2 + f (i + 1)) / sqrt_aux f i) ^ 2 : by simp
          ... = (sqrt_aux f i ^ 2 / sqrt_aux f i + f (i + 1) / sqrt_aux f i) ^ 2 : by ring
          ... = (sqrt_aux f i + f (i + 1) / sqrt_aux f i) ^ 2 : by rw sq_div_self (sqrt_aux_ne_zero f _), }, }, },
end

theorem sqrt_aux_overestimate' (f : cau_seq ℚ abs) (i : ℕ) :
  0 ≤ (sqrt_aux f i) ^ 2 - f i :=
sub_nonneg.mpr (sqrt_aux_overestimate f i)

lemma nonneg_three_add {a x y : ℚ} (h : 0 ≤ a) (t : 0 ≤ x) (u : 0 ≤ y) : 0 ≤ a + x + y :=
by linarith

lemma nonneg_three_mul {a x y : ℚ} (h : 0 ≤ a) (t : 0 ≤ x) (u : 0 ≤ y) : 0 ≤ a * x * y :=
mul_nonneg (mul_nonneg h t) u

lemma bl (a b : ℚ) : a / b = 4 * (a / (4 * b)) :=
begin
  have four_nonzero : (4 : ℚ) ≠ 0 := by norm_num,
  calc a / b = (4 * a) / (4 * b) :
    begin
      by_cases b = 0,
      { subst h,
        simp, },
      { rw eq_div_iff (mul_ne_zero four_nonzero h),
        field_simp, ring, }
    end
  ... = 4 * (a / (4 * b)) : mul_div_assoc 4 a (4 * b)
end

lemma eeee (a b : ℚ) (h : 0 < a) (h2 : 1 ≤ a / b) : a ≤ a ^ 2 / b :=
begin
  calc a = a * 1 : by ring
    ... ≤ a * (a / b) : (mul_le_mul_left h).mpr h2
    ... = a ^ 2 / b : by ring
end

lemma ff (a b : ℚ) (h2 : 0 < b) (h : b ≤ a) : 1 ≤ a / b :=
begin
  exact (one_le_div h2).mpr h
end

-- With sqrt_aux_ge_one, we should be able to prove the following: if sqrt_aux gets within ε,
-- then it stays within ε.
-- In fact, convergence is much faster.
theorem converges_eventually_if_near_step (f : cau_seq ℚ abs) (N : ℕ) (f_ge_0 : ∀ i ≥ N, 0 ≤ f i)
  (ε : ℚ) (ε_pos : 0 < ε) (f_near : ∀ i ≥ N, ∀ j ≥ N, abs (f i - f j) ≤ ε)
  (k : ℕ) (k_large : N ≤ k) (δ : ℚ) (δ_pos : 0 < δ) (converged : sqrt_aux f k ^ 2 - f k ≤ δ) :
  sqrt_aux f (k + 1) ^ 2 - f (k + 1) ≤ (δ + ε) ^ 2 / (4 * sqrt_aux f k ^ 2) :=
begin
  let s := sqrt_aux f k,
  by_cases t : f (k + 1) = 0,
  { specialize f_near k k_large (k + 1) (by linarith),
    unfold sqrt_aux,
    rw t at *,
    simp at *,
    have: 0 < (4 : ℚ) := by norm_num,
    cancel_denoms,
    cancel_denoms,
    rw ←bl,
    have lem : s ^ 2 ≤ δ + ε := le_trans converged (add_le_add rfl.le (le_of_abs_le f_near)),
    calc s ^ 2 ≤ δ + ε : lem
      ... ≤ (δ + ε) ^ 2 / s ^ 2 : begin
        have r : 0 < δ + ε := add_pos δ_pos ε_pos,
        refine eeee _ _ (add_pos δ_pos ε_pos) _,
        exact (one_le_div (pow_pos (sqrt_aux_pos f _) 2)).mpr lem,
      end
   },

  --have t := f_gt_0 (k + 1) (by linarith),
  --simp at t,
  have t : 0 < f (k + 1) := (ne.symm t).le_iff_lt.mp (f_ge_0 (k + 1) (le_add_right k_large)),

  --have r : 1 ≤ sqrt_aux f k ^ 2 := one_le_pow_of_one_le (sqrt_aux_ge_one f N f_gt_1 k k_large) 2,
  --have g : 0 < (4 : ℚ) := by norm_num,
  --have ineq : 4 ≤ 4 * sqrt_aux f k ^ 2 := by simpa using mul_le_mul_of_nonneg_left r g.le,

  unfold sqrt_aux,
  rw max_eq_right_of_lt t,

  have weaker : 0 < 4 * s ^ 2 := by linarith [pow_pos (sqrt_aux_pos f k) 2],

  calc ((s + f (k + 1) / s) / 2) ^ 2 - f (k + 1)
    = (4 * s ^ 2 * ((s + f (k + 1) / s) / 2) ^ 2 - 4 * s ^ 2 * f (k + 1)) / (4 * s ^ 2) :
      begin
        sorry
      end
    ... = (4 * s ^ 2 * ((s + f (k + 1) / s) / 2) ^ 2 - 4 * s ^ 2 * f (k + 1)) / (4 * s ^ 2) :
      begin
        sorry
      end
    ... = ((s ^ 2 - f k) ^ 2 + (f k - f (k + 1)) ^ 2 + 2 * (f k - f (k + 1)) * (s ^ 2 - f k)) / (4 * s ^ 2) :
      begin
       sorry
      end
    ... ≤ ((s ^ 2 - f k) ^ 2 + (f k - f (k + 1)) ^ 2 + 2 * (abs (f k - f (k + 1))) * (s ^ 2 - f k)) / (4 * s ^ 2) :
      begin
        refine bar _ _ _ weaker _,
        have r : f k - f (k + 1) ≤ abs (f k - f (k + 1)) := le_abs_self _,
        refine add_le_add rfl.le _,
        by_cases is_exact : s ^ 2 - f k = 0,
        { rw is_exact, simp, },
        { have greater : 0 < s ^ 2 - f k := (ne.symm is_exact).le_iff_lt.mp (sqrt_aux_overestimate' f _),
          refine (mul_le_mul_right greater).2 _,
          linarith [r], },
      end
    --... ≤ _ / 4 : by begin
    --  refine div_le_div_of_le_left _ g ineq,
    --  refine nonneg_three_add (sq_nonneg _) (sq_nonneg _) _,
    --  exact nonneg_three_mul (by norm_num) (abs_nonneg _) (sqrt_aux_overestimate' f _),
    --end
    ... ≤ (δ ^ 2 + (f k - f (k + 1)) ^ 2 + 2 * (abs (f k - f (k + 1))) * (s ^ 2 - f k)) / _ :
      begin
        refine div_le_div_of_le (le_of_lt weaker) _,
        refine add_le_add _ rfl.le,
        refine add_le_add _ rfl.le,
        refine sq_le_sq _,
        rw abs_eq_self.mpr (sqrt_aux_overestimate' f _),
        rw abs_eq_self.mpr (le_of_lt δ_pos),
        exact converged,
      end
    ... ≤ (δ ^ 2 + ε ^ 2 + 2 * (abs (f k - f (k + 1))) * (s ^ 2 - f k)) / _ :
      begin
        refine div_le_div_of_le (le_of_lt weaker) _,
        refine add_le_add _ rfl.le,
        refine add_le_add rfl.le _,
        refine sq_le_sq _,
        rw abs_eq_self.mpr (le_of_lt ε_pos),
        exact f_near k k_large (k + 1) (by linarith),
      end
    ... ≤ (δ ^ 2 + ε ^ 2 + 2 * ε * (s ^ 2 - f k)) / _ :
      begin
        refine div_le_div_of_le (le_of_lt weaker) _,
        refine add_le_add rfl.le _,
        refine mul_le_mul_of_nonneg_right _ (sqrt_aux_overestimate' f _),
        refine mul_le_mul_of_nonneg_left _ (by norm_num),
        exact f_near k k_large (k + 1) (by linarith),
      end
    ... ≤ (δ ^ 2 + ε ^ 2 + 2 * ε * δ) / _ :
      begin
        refine div_le_div_of_le (le_of_lt weaker) _,
        refine add_le_add rfl.le _,
        refine mul_le_mul_of_nonneg_left _ (by linarith),
        have u := sqrt_aux_overestimate f k,
        linarith,
      end
    ... = (δ + ε) ^ 2 / (4 * s ^ 2) : by ring
end

lemma eek (a b : ℚ) : a + b / a = (a ^ 2 + b) / a :=
begin
  ring_nf,
  rw [sq a, ←mul_assoc],
  simp,
end

theorem eventually_gets_near (f : cau_seq ℚ abs) (N : ℕ) (f_ge_0 : ∀ i ≥ N, 0 ≤ f i)
  (ε : ℚ) (ε_pos : 0 < ε) (ε_small : ε < 1) (f_near : ∀ i ≥ N, ∀ j ≥ N, abs (f i - f j) ≤ ε) :
  sqrt_aux f (N + 1) ^ 2 - f (N + 1) ≤ 37 :=
begin
  by_cases δ_pos : sqrt_aux f N ^ 2 - f N = 0,
  { unfold sqrt_aux,
    have v : max 0 (f (N + 1)) = f (N + 1) := max_eq_right (f_ge_0 (N + 1) (nat.le_succ N)),
    have eq : sqrt_aux f N ^ 2 = f N := sub_eq_zero.mp δ_pos,
    rw [v, div_pow _ _ 2, eek _ _, div_pow _ _ 2, eq],
    have r : f N ≠ 0,
    { intros h,
      rw [h, sub_zero, sq_zero_iff] at δ_pos,
      exact sqrt_aux_ne_zero f N δ_pos, },
    by_cases r' : f (N + 1) = 0,
    { rw r' at *,
      simp at *,
      rw sq_div_self r,
      norm_num,
      cancel_denoms,
      have h := f_near N (le_of_eq rfl) (N + 1) (nat.le_succ N),
      rw [r', sub_zero, abs_eq_self.2 (f_ge_0 N (le_of_eq rfl))] at h,
      calc f N ≤ ε : h
      ... ≤ _ : sorry, },

    have g : (f N - f (N + 1)) ^ 2 ≤ ε ^ 2,
    { have r := f_near N (le_of_eq rfl) (N + 1) (nat.le_succ N),
      rw ←abs_eq_self.2 (le_of_lt ε_pos) at r,
      exact sq_le_sq r, },
    have f_pos : 0 < f N := (ne.symm r).le_iff_lt.mp (f_ge_0 N (le_of_eq rfl)),
    have gg : 0 < f N * 4,
    { rw mul_pos_iff,
      left, exact ⟨f_pos, by norm_num⟩, },
    calc (f N + f (N + 1)) ^ 2 / f N / 2 ^ 2 - f (N + 1)
          = (f N + f (N + 1)) ^ 2 / f N / 4 - f (N + 1) : by norm_num
      ... = (f N + f (N + 1)) ^ 2 / f N / 4 - (4 * f (N + 1)) / 4 : by simp [mul_comm 4 (f (N + 1)), mul_div_cancel_left 4 r']
      ... = ((f N + f (N + 1)) ^ 2 / f N - 4 * f (N + 1)) / 4 : by ring
      ... = ((f N + f (N + 1)) ^ 2 / f N - 4 * f (N + 1) * f N / f N) / 4 :
        by simp [mul_comm (4 * f (N + 1)) (f N), mul_div_cancel_left (4 * f (N + 1)) r]
      ... = (((f N + f (N + 1)) ^ 2) - 4 * f (N + 1) * f N) / f N / 4 : by ring
      ... = (((f N + f (N + 1)) ^ 2) - 4 * f (N + 1) * f N) / (f N * 4) : div_div_eq_div_mul _ (f N) 4
      ... = ((f N ^ 2 + 2 * f N * f (N + 1) + f (N + 1) ^ 2) - 4 * f (N + 1) * f N) / (f N * 4) : by rw add_sq (f N) (f (N + 1))
      ... = ((f N ^ 2 - 2 * f N * f (N + 1) + f (N + 1) ^ 2)) / (f N * 4) : by ring
      ... = (((f N - f (N + 1)) ^ 2)) / (f N * 4) : by rw sub_sq (f N) (f (N + 1))
      ... ≤ ε ^ 2 / (f N * 4) : bar _ _ _ gg g
      ... ≤ _ : sorry
   },
  have δ_pos : 0 < sqrt_aux f N ^ 2 - f N := (ne.symm δ_pos).le_iff_lt.mp (sqrt_aux_overestimate' f _),
  have r : sqrt_aux f N ^ 2 - f N ≤ sqrt_aux f N ^ 2 := sub_le_self _ (f_ge_0 N (le_of_eq rfl)),
  let u := converges_eventually_if_near_step f N f_ge_0 ε ε_pos f_near N (le_of_eq rfl) (sqrt_aux f N ^ 2 - f N) δ_pos (le_of_eq rfl),

  calc sqrt_aux f (N + 1) ^ 2 - f (N + 1)
        ≤ (sqrt_aux f N ^ 2 - f N + ε) ^ 2 / (4 * sqrt_aux f N ^ 2) : u
    ... ≤ _ : sorry,
    --... ≤ (sqrt_aux f N ^ 2 + ε) ^ 2 / (4 * sqrt_aux f N ^ 2) : sorry
    --... = ((sqrt_aux f N ^ 2 + ε) / (2 * sqrt_aux f N)) ^ 2 : sorry
    --... = ((sqrt_aux f N + (ε / sqrt_aux f N)) / 2) ^ 2 : sorry
    --... ≤ ε : minimize (sqrt_aux f N) ε ε_pos,
end


theorem converges_eventually (f : cau_seq ℚ abs) (N : ℕ) (f_gt_1 : ∀ i ≥ N, 1 ≤ f i)
  (n : ℕ) : sqrt_aux f n ^ 2 - f n ≤ 1 :=
begin
  induction n with n hyp,
  { simp,
    by_cases (1 < f 0),
    { rw max_eq_right_of_lt h,
      simp,
     },
    { sorry, },
  }
end

lemma eee (e : ℚ) (bit : e ≤ 1) (pos : 0 < e) : e ^ 2 ≤ e :=
begin
  calc e ^ 2 = e * e : by ring
    ... ≤ 1 * e : (mul_le_mul_right pos).mpr bit
    ... = e : one_mul e,
end

theorem converges_eventually_if_near (f : cau_seq ℚ abs) (N : ℕ) (f_gt_1 : ∀ i ≥ N, 1 ≤ f i)
  (ε : ℚ) (ε_pos : 0 < ε) (ε_small : ε ≤ 1) (f_near : ∀ i ≥ N, ∀ j ≥ N, abs (f i - f j) ≤ ε)
  (k : ℕ) (k_large : N ≤ k) (δ : ℚ) (δ_pos : 0 < δ) (converged : sqrt_aux f k ^ 2 - f k ≤ δ) :
  ∀ (j ≥ k), sqrt_aux f j ^ 2 - f j ≤ (δ + ε) ^ 2 / 4
| 0 pr :=
begin
  simp at pr,
  rw pr at converged,
  sorry,
  --simpa using converged,
end
| (j + 1) pr :=
begin
  by_cases k = j + 1,
  { rw h at converged,
    sorry, },
    --simpa using converged, },
  { have k_le_j : k ≤ j := nat.lt_succ_iff.mp ((ne.le_iff_lt h).mp pr),
    have j_big : N ≤ j := by linarith,
    have v := converges_eventually_if_near j k_le_j,
    have u := converges_eventually_if_near_step f N f_gt_1 ε ε_pos f_near j j_big δ δ_pos v,
    have x : ε ^ 2 ≤ ε := eee ε ε_small ε_pos,
    linarith, },
end


/- TODO(Mario): finish the proof
theorem sqrt_aux_converges (f : cau_seq ℚ abs) : ∃ h x, 0 ≤ x ∧ x * x = max 0 (mk f) ∧
  mk ⟨sqrt_aux f, h⟩ = x :=
begin
  rcases sqrt_exists (le_max_left 0 (mk f)) with ⟨x, x0, hx⟩,
  suffices : ∃ h, mk ⟨sqrt_aux f, h⟩ = x,
  { exact this.imp (λ h e, ⟨x, x0, hx, e⟩) },
  apply of_near,

  suffices : ∃ δ > 0, ∀ i, abs (↑(sqrt_aux f i) - x) < δ / 2 ^ i,
  { rcases this with ⟨δ, δ0, hδ⟩,
    intros }
end -/

/-- The square root of a real number. This returns 0 for negative inputs. -/
@[pp_nodot] noncomputable def sqrt (x : ℝ) : ℝ :=
nnreal.sqrt (real.to_nnreal x)
/-quotient.lift_on x
  (λ f, mk ⟨sqrt_aux f, (sqrt_aux_converges f).fst⟩)
  (λ f g e, begin
    rcases sqrt_aux_converges f with ⟨hf, x, x0, xf, xs⟩,
    rcases sqrt_aux_converges g with ⟨hg, y, y0, yg, ys⟩,
    refine xs.trans (eq.trans _ ys.symm),
    rw [← @mul_self_inj_of_nonneg ℝ _ x y x0 y0, xf, yg],
    congr' 1, exact quotient.sound e
  end)-/

variables {x y : ℝ}

@[simp, norm_cast] lemma coe_sqrt {x : ℝ≥0} : (nnreal.sqrt x : ℝ) = real.sqrt x :=
by rw [real.sqrt, real.to_nnreal_coe]

@[continuity]
lemma continuous_sqrt : continuous sqrt :=
nnreal.continuous_coe.comp $ nnreal.sqrt.continuous.comp continuous_real_to_nnreal

theorem sqrt_eq_zero_of_nonpos (h : x ≤ 0) : sqrt x = 0 :=
by simp [sqrt, real.to_nnreal_eq_zero.2 h]

theorem sqrt_nonneg (x : ℝ) : 0 ≤ sqrt x := nnreal.coe_nonneg _

@[simp] theorem mul_self_sqrt (h : 0 ≤ x) : sqrt x * sqrt x = x :=
by rw [sqrt, ← nnreal.coe_mul, nnreal.mul_self_sqrt, real.coe_to_nnreal _ h]

@[simp] theorem sqrt_mul_self (h : 0 ≤ x) : sqrt (x * x) = x :=
(mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))

theorem sqrt_eq_cases : sqrt x = y ↔ y * y = x ∧ 0 ≤ y ∨ x < 0 ∧ y = 0 :=
begin
  split,
  { rintro rfl,
    cases le_or_lt 0 x with hle hlt,
    { exact or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩ },
    { exact or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩ } },
  { rintro (⟨rfl, hy⟩|⟨hx, rfl⟩),
    exacts [sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le] }
end

theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) :
  sqrt x = y ↔ y * y = x :=
⟨λ h, by rw [← h, mul_self_sqrt hx], λ h, by rw [← h, sqrt_mul_self hy]⟩

theorem sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) :
  sqrt x = y ↔ y * y = x :=
by simp [sqrt_eq_cases, h.ne', h.le]

@[simp] lemma sqrt_eq_one : sqrt x = 1 ↔ x = 1 :=
calc sqrt x = 1 ↔ 1 * 1 = x :
  sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
... ↔ x = 1 : by rw [eq_comm, mul_one]

@[simp] theorem sq_sqrt (h : 0 ≤ x) : (sqrt x)^2 = x :=
by rw [sq, mul_self_sqrt h]

@[simp] theorem sqrt_sq (h : 0 ≤ x) : sqrt (x ^ 2) = x :=
by rw [sq, sqrt_mul_self h]

theorem sqrt_eq_iff_sq_eq (hx : 0 ≤ x) (hy : 0 ≤ y) :
  sqrt x = y ↔ y ^ 2 = x :=
by rw [sq, sqrt_eq_iff_mul_self_eq hx hy]

theorem sqrt_mul_self_eq_abs (x : ℝ) : sqrt (x * x) = |x| :=
by rw [← abs_mul_abs_self x, sqrt_mul_self (abs_nonneg _)]

theorem sqrt_sq_eq_abs (x : ℝ) : sqrt (x ^ 2) = |x| :=
by rw [sq, sqrt_mul_self_eq_abs]

@[simp] theorem sqrt_zero : sqrt 0 = 0 := by simp [sqrt]

@[simp] theorem sqrt_one : sqrt 1 = 1 := by simp [sqrt]

@[simp] theorem sqrt_le_sqrt_iff (hy : 0 ≤ y) : sqrt x ≤ sqrt y ↔ x ≤ y :=
by rw [sqrt, sqrt, nnreal.coe_le_coe, nnreal.sqrt_le_sqrt_iff, real.to_nnreal_le_to_nnreal_iff hy]

@[simp] theorem sqrt_lt_sqrt_iff (hx : 0 ≤ x) : sqrt x < sqrt y ↔ x < y :=
lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)

theorem sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : sqrt x < sqrt y ↔ x < y :=
by rw [sqrt, sqrt, nnreal.coe_lt_coe, nnreal.sqrt_lt_sqrt_iff, to_nnreal_lt_to_nnreal_iff hy]

theorem sqrt_le_sqrt (h : x ≤ y) : sqrt x ≤ sqrt y :=
by { rw [sqrt, sqrt, nnreal.coe_le_coe, nnreal.sqrt_le_sqrt_iff], exact to_nnreal_le_to_nnreal h }

theorem sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y) : sqrt x < sqrt y :=
(sqrt_lt_sqrt_iff hx).2 h

theorem sqrt_le_left (hy : 0 ≤ y) : sqrt x ≤ y ↔ x ≤ y ^ 2 :=
by rw [sqrt, ← real.le_to_nnreal_iff_coe_le hy, nnreal.sqrt_le_iff, ← real.to_nnreal_mul hy,
  real.to_nnreal_le_to_nnreal_iff (mul_self_nonneg y), sq]

theorem sqrt_le_iff : sqrt x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2 :=
begin
  rw [← and_iff_right_of_imp (λ h, (sqrt_nonneg x).trans h), and.congr_right_iff],
  exact sqrt_le_left
end

/- note: if you want to conclude `x ≤ sqrt y`, then use `le_sqrt_of_sq_le`.
   if you have `x > 0`, consider using `le_sqrt'` -/
theorem le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
by rw [mul_self_le_mul_self_iff hx (sqrt_nonneg _), sq, mul_self_sqrt hy]

theorem le_sqrt' (hx : 0 < x) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
by { rw [sqrt, ← nnreal.coe_mk x hx.le, nnreal.coe_le_coe, nnreal.le_sqrt_iff,
  real.le_to_nnreal_iff_coe_le', sq, nnreal.coe_mul], exact mul_pos hx hx }

theorem abs_le_sqrt (h : x^2 ≤ y) : |x| ≤ sqrt y :=
by rw ← sqrt_sq_eq_abs; exact sqrt_le_sqrt h

theorem sq_le (h : 0 ≤ y) : x^2 ≤ y ↔ -sqrt y ≤ x ∧ x ≤ sqrt y :=
begin
  split,
  { simpa only [abs_le] using abs_le_sqrt },
  { rw [← abs_le, ← sq_abs],
    exact (le_sqrt (abs_nonneg x) h).mp },
end

theorem neg_sqrt_le_of_sq_le (h : x^2 ≤ y) : -sqrt y ≤ x :=
((sq_le ((sq_nonneg x).trans h)).mp h).1

theorem le_sqrt_of_sq_le (h : x^2 ≤ y) : x ≤ sqrt y :=
((sq_le ((sq_nonneg x).trans h)).mp h).2

@[simp] theorem sqrt_inj (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = sqrt y ↔ x = y :=
by simp [le_antisymm_iff, hx, hy]

@[simp] theorem sqrt_eq_zero (h : 0 ≤ x) : sqrt x = 0 ↔ x = 0 :=
by simpa using sqrt_inj h le_rfl

theorem sqrt_eq_zero' : sqrt x = 0 ↔ x ≤ 0 :=
by rw [sqrt, nnreal.coe_eq_zero, nnreal.sqrt_eq_zero, real.to_nnreal_eq_zero]

theorem sqrt_ne_zero (h : 0 ≤ x) : sqrt x ≠ 0 ↔ x ≠ 0 :=
by rw [not_iff_not, sqrt_eq_zero h]

theorem sqrt_ne_zero' : sqrt x ≠ 0 ↔ 0 < x :=
by rw [← not_le, not_iff_not, sqrt_eq_zero']

@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x :=
lt_iff_lt_of_le_iff_le (iff.trans
  (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

@[simp] theorem sqrt_mul (hx : 0 ≤ x) (y : ℝ) : sqrt (x * y) = sqrt x * sqrt y :=
by simp_rw [sqrt, ← nnreal.coe_mul, nnreal.coe_eq, real.to_nnreal_mul hx, nnreal.sqrt_mul]

@[simp] theorem sqrt_mul' (x) {y : ℝ} (hy : 0 ≤ y) : sqrt (x * y) = sqrt x * sqrt y :=
by rw [mul_comm, sqrt_mul hy, mul_comm]

@[simp] theorem sqrt_inv (x : ℝ) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
by rw [sqrt, real.to_nnreal_inv, nnreal.sqrt_inv, nnreal.coe_inv, sqrt]

@[simp] theorem sqrt_div (hx : 0 ≤ x) (y : ℝ) : sqrt (x / y) = sqrt x / sqrt y :=
by rw [division_def, sqrt_mul hx, sqrt_inv, division_def]

@[simp] theorem div_sqrt : x / sqrt x = sqrt x :=
begin
  cases le_or_lt x 0,
  { rw [sqrt_eq_zero'.mpr h, div_zero] },
  { rw [div_eq_iff (sqrt_ne_zero'.mpr h), mul_self_sqrt h.le] },
end

theorem sqrt_div_self' : sqrt x / x = 1 / sqrt x :=
by rw [←div_sqrt, one_div_div, div_sqrt]

theorem sqrt_div_self : sqrt x / x = (sqrt x)⁻¹ :=
by rw [sqrt_div_self', one_div]

theorem lt_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x < sqrt y ↔ x ^ 2 < y :=
by rw [mul_self_lt_mul_self_iff hx (sqrt_nonneg y), sq, mul_self_sqrt hy]

theorem sq_lt : x^2 < y ↔ -sqrt y < x ∧ x < sqrt y :=
begin
  split,
  { simpa only [← sqrt_lt_sqrt_iff (sq_nonneg x), sqrt_sq_eq_abs] using abs_lt.mp },
  { rw [← abs_lt, ← sq_abs],
    exact λ h, (lt_sqrt (abs_nonneg x) (sqrt_pos.mp (lt_of_le_of_lt (abs_nonneg x) h)).le).mp h },
end

theorem neg_sqrt_lt_of_sq_lt (h : x^2 < y) : -sqrt y < x := (sq_lt.mp h).1

theorem lt_sqrt_of_sq_lt (h : x^2 < y) : x < sqrt y := (sq_lt.mp h).2

/-- The natural square root is at most the real square root -/
lemma nat_sqrt_le_real_sqrt {a : ℕ} : ↑(nat.sqrt a) ≤ real.sqrt ↑a :=
begin
  rw real.le_sqrt (nat.cast_nonneg _) (nat.cast_nonneg _),
  norm_cast,
  exact nat.sqrt_le' a,
end

/-- The real square root is at most the natural square root plus one -/
lemma real_sqrt_le_nat_sqrt_succ {a : ℕ} : real.sqrt ↑a ≤ nat.sqrt a + 1 :=
begin
  rw real.sqrt_le_iff,
  split,
  { norm_cast, simp, },
  { norm_cast, exact le_of_lt (nat.lt_succ_sqrt' a), },
end

instance : star_ordered_ring ℝ :=
{ nonneg_iff := λ r, by
  { refine ⟨λ hr, ⟨sqrt r, show r = sqrt r * sqrt r, by rw [←sqrt_mul hr, sqrt_mul_self hr]⟩, _⟩,
    rintros ⟨s, rfl⟩,
    exact mul_self_nonneg s },
  ..real.ordered_add_comm_group }

end real

open real

variables {α : Type*}

lemma filter.tendsto.sqrt {f : α → ℝ} {l : filter α} {x : ℝ} (h : tendsto f l (𝓝 x)) :
  tendsto (λ x, sqrt (f x)) l (𝓝 (sqrt x)) :=
(continuous_sqrt.tendsto _).comp h

variables [topological_space α] {f : α → ℝ} {s : set α} {x : α}

lemma continuous_within_at.sqrt (h : continuous_within_at f s x) :
  continuous_within_at (λ x, sqrt (f x)) s x :=
h.sqrt

lemma continuous_at.sqrt (h : continuous_at f x) : continuous_at (λ x, sqrt (f x)) x := h.sqrt

lemma continuous_on.sqrt (h : continuous_on f s) : continuous_on (λ x, sqrt (f x)) s :=
λ x hx, (h x hx).sqrt

@[continuity]
lemma continuous.sqrt (h : continuous f) : continuous (λ x, sqrt (f x)) := continuous_sqrt.comp h
