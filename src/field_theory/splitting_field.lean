/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.char_p.algebra
import field_theory.intermediate_field
import ring_theory.adjoin.field

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : K[X]` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : K[X]` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `polynomial.splitting_field f`: A fixed splitting field of the polynomial `f`.
* `polynomial.is_splitting_field`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `polynomial.is_splitting_field.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.
* `polynomial.is_splitting_field.alg_equiv`: Every splitting field of a polynomial `f` is isomorphic
  to `splitting_field f` and thus, being a splitting field is unique up to isomorphism.

-/

noncomputable theory
open_locale classical big_operators polynomial

universes u v w

variables {F : Type u} {K : Type v} {L : Type w}

namespace polynomial

variables [field K] [field L] [field F]
open polynomial

section splitting_field

/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : K[X]) : K[X] :=
if H : ∃ g, irreducible g ∧ g ∣ f then classical.some H else X

lemma irreducible_factor (f : K[X]) : irreducible (factor f) :=
begin
  rw factor, split_ifs with H, { exact (classical.some_spec H).1 }, { exact irreducible_X }
end

/-- See note [fact non-instances]. -/
lemma fact_irreducible_factor (f : K[X]) : fact (irreducible (factor f)) :=
⟨irreducible_factor f⟩

local attribute [instance] fact_irreducible_factor

theorem factor_dvd_of_not_is_unit {f : K[X]} (hf1 : ¬is_unit f) : factor f ∣ f :=
begin
  by_cases hf2 : f = 0, { rw hf2, exact dvd_zero _ },
  rw [factor, dif_pos (wf_dvd_monoid.exists_irreducible_factor hf1 hf2)],
  exact (classical.some_spec $ wf_dvd_monoid.exists_irreducible_factor hf1 hf2).2
end

theorem factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree ≠ 0) : factor f ∣ f :=
factor_dvd_of_not_is_unit (mt degree_eq_zero_of_is_unit hf)

theorem factor_dvd_of_nat_degree_ne_zero {f : K[X]} (hf : f.nat_degree ≠ 0) :
  factor f ∣ f :=
factor_dvd_of_degree_ne_zero (mt nat_degree_eq_of_degree_eq_some hf)

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def remove_factor (f : K[X]) : polynomial (adjoin_root $ factor f) :=
map (adjoin_root.of f.factor) f /ₘ (X - C (adjoin_root.root f.factor))

theorem X_sub_C_mul_remove_factor (f : K[X]) (hf : f.nat_degree ≠ 0) :
  (X - C (adjoin_root.root f.factor)) * f.remove_factor = map (adjoin_root.of f.factor) f :=
let ⟨g, hg⟩ := factor_dvd_of_nat_degree_ne_zero hf in
mul_div_by_monic_eq_iff_is_root.2 $ by rw [is_root.def, eval_map, hg, eval₂_mul, ← hg,
    adjoin_root.eval₂_root, zero_mul]

theorem nat_degree_remove_factor (f : K[X]) :
  f.remove_factor.nat_degree = f.nat_degree - 1 :=
by rw [remove_factor, nat_degree_div_by_monic _ (monic_X_sub_C _), nat_degree_map,
       nat_degree_X_sub_C]

theorem nat_degree_remove_factor' {f : K[X]} {n : ℕ} (hfn : f.nat_degree = n+1) :
  f.remove_factor.nat_degree = n :=
by rw [nat_degree_remove_factor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors.

Uses recursion on the degree. For better definitional behaviour, structures
including `splitting_field_aux` (such as instances) should be defined using
this recursion in each field, rather than defining the whole tuple through
recursion.
-/
def splitting_field_aux (n : ℕ) : Π {K : Type u} [field K], by exactI Π (f : K[X]), Type u :=
nat.rec_on n (λ K _ _, K) $ λ n ih K _ f, by exactI
ih f.remove_factor

namespace splitting_field_aux

theorem succ (n : ℕ) (f : K[X]) :
  splitting_field_aux (n+1) f = splitting_field_aux n f.remove_factor := rfl

section lift_instances

/-! ### Instances on `splitting_field_aux`

In order to avoid diamond issues, we have to be careful to define each data field of algebraic
instances on `splitting_field_aux` by recursion, rather than defining the whole structure by
recursion at once.

The important detail is that the `smul` instances can be lifted _before_ we create the algebraic
instances; if we do not do this, this creates a mutual dependence on both on each other, and it
is impossible to untangle this mess. In order to do this, we need that these `smul` instances
are distributive in the sense of `distrib_smul`, which is weak enough to be guaranteed at this
stage. This is sufficient to lift an action to `adjoin_root f` (remember that this is a quotient,
so these conditions are equivalent to well-definedness), which is all we need.
-/

/-- Splitting fields have a zero. -/
protected def zero (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  splitting_field_aux n f :=
nat.rec_on n (λ K fK f, by exactI @has_zero.zero K _) (λ n ih K fK f, ih)

/-- Splitting fields have an addition. -/
protected def add (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
nat.rec_on n (λ K fK f, by exactI @has_add.add K _) (λ n ih K fK f, ih)

/-- Splitting fields inherit scalar multiplication. -/
protected def smul (n : ℕ) : Π (α : Type*) {K : Type u} [field K],
  by exactI Π [distrib_smul α K],
  by exactI Π [is_scalar_tower α K K] {f : K[X]},
  α → splitting_field_aux n f → splitting_field_aux n f :=
nat.rec_on n
  (λ α K fK ds ist f, by exactI @has_smul.smul _ K _)
  (λ n ih α K fK ds ist f, by exactI ih α)

instance has_smul (α : Type*) (n : ℕ) {K : Type u} [field K] [distrib_smul α K]
  [is_scalar_tower α K K] {f : K[X]} :
  has_smul α (splitting_field_aux n f) :=
⟨splitting_field_aux.smul n α⟩

instance is_scalar_tower (n : ℕ) : Π (R₁ R₂ : Type*) {K : Type u}
  [has_smul R₁ R₂] [field K],
  by exactI Π [distrib_smul R₂ K] [distrib_smul R₁ K],
  by exactI Π [is_scalar_tower R₁ K K] [is_scalar_tower R₂ K K] [is_scalar_tower R₁ R₂ K]
    {f : K[X]}, by exactI is_scalar_tower R₁ R₂ (splitting_field_aux n f) :=
nat.rec_on n (λ R₁ R₂ K _ _ hs₂ hs₁ _ _ h f,
begin
  rcases hs₁ with @⟨@⟨⟨hs₁⟩,_⟩,_⟩,
  rcases hs₂ with @⟨@⟨⟨hs₂⟩,_⟩,_⟩,
  exact h,
end) $ λ n ih R₁ R₂ K _ _ _ _ _ _ _ f, by exactI ih R₁ R₂

/-- Splitting fields have a negation. -/
protected def neg (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  splitting_field_aux n f → splitting_field_aux n f :=
nat.rec_on n (λ K fK f, by exactI @has_neg.neg K _) (λ n ih K fK f, ih)

/-- Splitting fields have subtraction. -/
protected def sub (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
nat.rec_on n (λ K fK f, by exactI @has_sub.sub K _) (λ n ih K fK f, ih)

/-- Splitting fields have a one. -/
protected def one (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  splitting_field_aux n f :=
nat.rec_on n (λ K fK f, by exactI @has_one.one K _) (λ n ih K fK f, ih)

/-- Splitting fields have a multiplication. -/
protected def mul (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
nat.rec_on n (λ K fK f, by exactI @has_mul.mul K _) (λ n ih K fK f, ih)

/-- Splitting fields have a power operation. -/
protected def npow (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  ℕ → splitting_field_aux n f → splitting_field_aux n f :=
nat.rec_on n (λ K fK f n x, by exactI @has_pow.pow K _ _ x n) (λ n ih K fK f, ih)

/-- Splitting fields have an injection from the base field. -/
protected def mk (n : ℕ) : Π {K : Type u} [field K],
  by exactI Π {f : K[X]}, K → splitting_field_aux n f :=
nat.rec_on n (λ K fK f, id) (λ n ih K fK f, by exactI ih ∘ coe)
-- note that `coe` goes from `K → adjoin_root f`, and then `ih` lifts to the full splitting field
-- (as we generalise over all fields in this recursion!)

/-- Splitting fields have an inverse. -/
protected def inv (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  splitting_field_aux n f → splitting_field_aux n f :=
nat.rec_on n (λ K fK f, by exactI @has_inv.inv K _) (λ n ih K fK f, ih)

/-- Splitting fields have a division. -/
protected def div (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
nat.rec_on n (λ K fK f, by exactI @has_div.div K _) (λ n ih K fK f, ih)

/-- Splitting fields have powers by integers. -/
protected def zpow (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
  ℤ → splitting_field_aux n f → splitting_field_aux n f :=
nat.rec_on n (λ K fK f n x, by exactI @has_pow.pow K _ _ x n) (λ n ih K fK f, ih)

-- I'm not sure why these two lemmas break, but inlining them seems to not work.
private lemma nsmul_zero (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]}
  (x : splitting_field_aux n f), (0 : ℕ) • x = splitting_field_aux.zero n :=
nat.rec_on n (λ K fK f, by exactI zero_nsmul) (λ n ih K fK f, by exactI ih)

private lemma nsmul_succ (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]}
  (k : ℕ) (x : splitting_field_aux n f),
  (k + 1) • x = splitting_field_aux.add n x (k • x) :=
nat.rec_on n (λ K fK f n x, by exactI succ_nsmul x n) (λ n ih K fK f, by exactI ih)

instance field (n : ℕ) {K : Type u} [field K] {f : K[X]} :
  field (splitting_field_aux n f) :=
begin
  refine
  { zero := splitting_field_aux.zero n,
    one := splitting_field_aux.one n,
    add := splitting_field_aux.add n,
    zero_add := have h : _ := @zero_add, _,
    add_zero := have h : _ := @add_zero, _,
    add_assoc := have h : _ := @add_assoc, _,
    add_comm := have h : _ := @add_comm, _,
    neg := splitting_field_aux.neg n,
    add_left_neg := have h : _ := @add_left_neg, _,
    sub := splitting_field_aux.sub n,
    sub_eq_add_neg := have h : _ := @sub_eq_add_neg, _,
    mul := splitting_field_aux.mul n,
    one_mul := have h : _ := @one_mul, _,
    mul_one := have h : _ := @mul_one, _,
    mul_assoc := have h : _ := @mul_assoc, _,
    left_distrib := have h : _ := @left_distrib, _,
    right_distrib := have h : _ := @right_distrib, _,
    mul_comm := have h : _ := @mul_comm, _,
    inv := splitting_field_aux.inv n,
    inv_zero := have h : _ := @inv_zero, _,
    div := splitting_field_aux.div n,
    div_eq_mul_inv := have h : _ := @div_eq_mul_inv, _,
    mul_inv_cancel := have h : _ := @mul_inv_cancel, _,
    exists_pair_ne := have h : _ := @exists_pair_ne, _,
    nat_cast := splitting_field_aux.mk n ∘ (coe : ℕ → K),
    nat_cast_zero := have h : _ := @comm_ring.nat_cast_zero, _,
    nat_cast_succ := have h : _ := @comm_ring.nat_cast_succ, _,
    nsmul := (•),
    nsmul_zero' := nsmul_zero n,
    nsmul_succ' := nsmul_succ n,
    int_cast := splitting_field_aux.mk n ∘ (coe : ℤ → K),
    int_cast_of_nat := have h : _ := @comm_ring.int_cast_of_nat, _,
    int_cast_neg_succ_of_nat := have h : _ := @comm_ring.int_cast_neg_succ_of_nat, _,
    zsmul := (•),
    zsmul_zero' := have h : _ := @subtraction_comm_monoid.zsmul_zero', _,
    zsmul_succ' := have h : _ := @subtraction_comm_monoid.zsmul_succ', _,
    zsmul_neg' := have h : _ := @subtraction_comm_monoid.zsmul_neg', _,
    rat_cast := splitting_field_aux.mk n ∘ (coe : ℚ → K),
    rat_cast_mk := have h : _ := @field.rat_cast_mk, _,
    qsmul := (•),
    qsmul_eq_mul' := have h : _ := @field.qsmul_eq_mul', _,
    npow := splitting_field_aux.npow n,
    npow_zero' := have h : _ := @comm_ring.npow_zero', _,
    npow_succ' := have h : _ := @comm_ring.npow_succ', _,
    zpow := splitting_field_aux.zpow n,
    zpow_zero' := have h : _ := @field.zpow_zero', _,
    zpow_succ' := have h : _ := @field.zpow_succ', _,
    zpow_neg' := have h : _ := @field.zpow_neg', _},
  all_goals {
    unfreezingI { induction n with n ih generalizing K },
    { apply @h K },
    { exact @ih _ _ _ } },
end

instance inhabited {n : ℕ} {f : K[X]} :
  inhabited (splitting_field_aux n f) := ⟨37⟩

/-- The injection from the base field as a ring homomorphism. -/
@[simps] protected def mk_hom (n : ℕ) {K : Type u} [field K] {f : K[X]} :
  K →+* splitting_field_aux n f :=
{ to_fun := splitting_field_aux.mk n,
  map_one' :=
  begin
    unfreezingI { induction n with k hk generalizing K },
    { simp [splitting_field_aux.mk] },
    exact hk
  end,
  map_mul' :=
  begin
    unfreezingI { induction n with k hk generalizing K },
    { simp [splitting_field_aux.mk] },
    intros x y,
    change (splitting_field_aux.mk k) ((adjoin_root.of f.factor) _) = _,
    rw [map_mul],
    exact hk _ _
  end,
  map_zero' :=
  begin
    unfreezingI { induction n with k hk generalizing K },
    { simp [splitting_field_aux.mk] },
    change (splitting_field_aux.mk k) ((adjoin_root.of f.factor) 0) = _,
    rw [map_zero, hk],
  end,
  map_add' :=
  begin
    unfreezingI { induction n with k hk generalizing K },
    { simp [splitting_field_aux.mk] },
    intros x y,
    change (splitting_field_aux.mk k) ((adjoin_root.of f.factor) _) = _,
    rw [map_add],
    exact hk _ _
  end }

instance algebra (n : ℕ) (R : Type*) {K : Type u} [comm_semiring R] [field K]
  [algebra R K] {f : K[X]} : algebra R (splitting_field_aux n f) :=
{ to_fun := (splitting_field_aux.mk_hom n).comp (algebra_map R K),
  smul := (•),
  smul_def' :=
  begin
    unfreezingI { induction n with k hk generalizing K },
    { exact algebra.smul_def },
    exact hk
  end,
  commutes' := λ a b, mul_comm _ _,
  .. (splitting_field_aux.mk_hom n).comp (algebra_map R K) }

/-- Because `splitting_field_aux` is defined by recursion, we have to make sure all instances
on `splitting_field_aux` are defined by recursion within the fields. Otherwise, there will be
instance diamonds such as the following: -/
example (n : ℕ) {K : Type u} [field K] {f : K[X]} :
    (add_comm_monoid.nat_module : module ℕ (splitting_field_aux n f)) =
  @algebra.to_module _ _ _ _ (splitting_field_aux.algebra n _) :=
rfl

end lift_instances

instance algebra''' {n : ℕ} {f : K[X]} :
  algebra (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor) :=
splitting_field_aux.algebra n _

instance algebra' {n : ℕ} {f : K[X]} :
  algebra (adjoin_root f.factor) (splitting_field_aux n.succ f) :=
splitting_field_aux.algebra'''

instance algebra'' {n : ℕ} {f : K[X]} :
  algebra K (splitting_field_aux n f.remove_factor) :=
splitting_field_aux.algebra n K

instance scalar_tower' {n : ℕ} {f : K[X]} :
  is_scalar_tower K (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor) :=
begin
  -- finding this instance ourselves makes things faster
  haveI : is_scalar_tower K (adjoin_root f.factor) (adjoin_root f.factor) :=
    is_scalar_tower.right,
  exact
    splitting_field_aux.is_scalar_tower n K (adjoin_root f.factor),
end

instance scalar_tower {n : ℕ} {f : K[X]} :
  is_scalar_tower K (adjoin_root f.factor) (splitting_field_aux (n + 1) f) :=
splitting_field_aux.scalar_tower'

theorem algebra_map_succ (n : ℕ) (f : K[X]) :
  by exact algebra_map K (splitting_field_aux (n+1) f) =
    (algebra_map (adjoin_root f.factor)
        (splitting_field_aux n f.remove_factor)).comp
      (adjoin_root.of f.factor) :=
is_scalar_tower.algebra_map_eq _ _ _

protected theorem splits (n : ℕ) : ∀ {K : Type u} [field K], by exactI
  ∀ (f : K[X]) (hfn : f.nat_degree = n),
    splits (algebra_map K $ splitting_field_aux n f) f :=
nat.rec_on n (λ K _ _ hf, by exactI splits_of_degree_le_one _
  (le_trans degree_le_nat_degree $ hf.symm ▸ with_bot.coe_le_coe.2 zero_le_one)) $ λ n ih K _ f hf,
by { resetI, rw [← splits_id_iff_splits, algebra_map_succ, ← map_map, splits_id_iff_splits,
    ← X_sub_C_mul_remove_factor f (λ h, by { rw h at hf, cases hf })],
exact splits_mul _ (splits_X_sub_C _) (ih _ (nat_degree_remove_factor' hf)) }

theorem exists_lift (n : ℕ) : ∀ {K : Type u} [field K], by exactI
  ∀ (f : K[X]) (hfn : f.nat_degree = n) {L : Type*} [field L], by exactI
    ∀ (j : K →+* L) (hf : splits j f), ∃ k : splitting_field_aux n f →+* L,
      k.comp (algebra_map _ _) = j :=
nat.rec_on n (λ K _ _ _ L _ j _, by exactI ⟨j, j.comp_id⟩) $ λ n ih K _ f hf L _ j hj, by exactI
have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hf, cases hf },
have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
let ⟨r, hr⟩ := exists_root_of_splits _ (splits_of_splits_of_dvd j hfn0 hj
  (factor_dvd_of_nat_degree_ne_zero hndf))
  (mt is_unit_iff_degree_eq_zero.2 f.irreducible_factor.1) in
have hmf0 : map (adjoin_root.of f.factor) f ≠ 0, from map_ne_zero hfn0,
have hsf : splits (adjoin_root.lift j r hr) f.remove_factor,
by { rw ← X_sub_C_mul_remove_factor _ hndf at hmf0, refine (splits_of_splits_mul _ hmf0 _).2,
  rwa [X_sub_C_mul_remove_factor _ hndf, ← splits_id_iff_splits, map_map, adjoin_root.lift_comp_of,
      splits_id_iff_splits] },
let ⟨k, hk⟩ := ih f.remove_factor (nat_degree_remove_factor' hf) (adjoin_root.lift j r hr) hsf in
⟨k, by rw [algebra_map_succ, ← ring_hom.comp_assoc, hk, adjoin_root.lift_comp_of]⟩

theorem adjoin_roots (n : ℕ) : ∀ {K : Type u} [field K], by exactI
  ∀ (f : K[X]) (hfn : f.nat_degree = n),
    algebra.adjoin K (↑(f.map $ algebra_map K $ splitting_field_aux n f).roots.to_finset :
      set (splitting_field_aux n f)) = ⊤ :=
nat.rec_on n (λ K _ f hf, by exactI algebra.eq_top_iff.2 (λ x, subalgebra.range_le _ ⟨x, rfl⟩)) $
λ n ih K _ f hfn, by exactI
have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hfn, cases hfn },
have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
have hmf0 : map (algebra_map K (splitting_field_aux n.succ f)) f ≠ 0 := map_ne_zero hfn0,
by { rw [algebra_map_succ, ← map_map, ← X_sub_C_mul_remove_factor _ hndf,
         polynomial.map_mul] at hmf0 ⊢,
rw [roots_mul hmf0, polynomial.map_sub, map_X, map_C, roots_X_sub_C, multiset.to_finset_add,
    finset.coe_union, multiset.to_finset_singleton, finset.coe_singleton,
    algebra.adjoin_union_eq_adjoin_adjoin, ← set.image_singleton,
    algebra.adjoin_algebra_map K (adjoin_root f.factor)
      (splitting_field_aux n f.remove_factor),
    adjoin_root.adjoin_root_eq_top, algebra.map_top,
    is_scalar_tower.adjoin_range_to_alg_hom K (adjoin_root f.factor)
      (splitting_field_aux n f.remove_factor),
    ih _ (nat_degree_remove_factor' hfn), subalgebra.restrict_scalars_top] }

end splitting_field_aux

/-- A splitting field of a polynomial. -/
def splitting_field (f : K[X]) :=
splitting_field_aux f.nat_degree f

namespace splitting_field

variables (f : K[X])

instance : field (splitting_field f) :=
splitting_field_aux.field _

instance inhabited : inhabited (splitting_field f) := ⟨37⟩

instance algebra' {R} [comm_semiring R] [algebra R K] : algebra R (splitting_field f) :=
splitting_field_aux.algebra _ _

instance : algebra K (splitting_field f) :=
splitting_field_aux.algebra _ _

instance [char_zero K] : char_zero (splitting_field f) :=
char_zero_of_injective_algebra_map ((algebra_map K _).injective)

-- The algebra instance deriving from `K` should be definitionally equal to that
-- deriving from the field structure on `splitting_field f`.
example : (add_comm_monoid.nat_module : module ℕ (splitting_field f)) =
    @algebra.to_module _ _ _ _ (splitting_field.algebra' f) :=
rfl

example : (add_comm_group.int_module _ : module ℤ (splitting_field f)) =
    @algebra.to_module _ _ _ _ (splitting_field.algebra' f) :=
rfl

example [char_zero K] : (splitting_field.algebra' f) = algebra_rat :=
rfl

example [char_zero K] : (splitting_field.algebra' f) = algebra_rat :=
rfl

example {q : ℚ[X]} : algebra_int (splitting_field q) = splitting_field.algebra' q := rfl

protected theorem splits : splits (algebra_map K (splitting_field f)) f :=
splitting_field_aux.splits _ _ rfl

variables [algebra K L] (hb : splits (algebra_map K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : splitting_field f →ₐ[K] L :=
{ commutes' := λ r, by { have := classical.some_spec (splitting_field_aux.exists_lift _ _ rfl _ hb),
    exact ring_hom.ext_iff.1 this r },
  .. classical.some (splitting_field_aux.exists_lift _ _ _ _ hb) }

theorem adjoin_roots : algebra.adjoin K
    (↑(f.map (algebra_map K $ splitting_field f)).roots.to_finset : set (splitting_field f)) = ⊤ :=
splitting_field_aux.adjoin_roots _ _ rfl

theorem adjoin_root_set : algebra.adjoin K (f.root_set f.splitting_field) = ⊤ :=
adjoin_roots f

end splitting_field

variables (K L) [algebra K L]
/-- Typeclass characterising splitting fields. -/
class is_splitting_field (f : K[X]) : Prop :=
(splits [] : splits (algebra_map K L) f)
(adjoin_roots [] : algebra.adjoin K (↑(f.map (algebra_map K L)).roots.to_finset : set L) = ⊤)

namespace is_splitting_field

variables {K}
instance splitting_field (f : K[X]) : is_splitting_field K (splitting_field f) f :=
⟨splitting_field.splits f, splitting_field.adjoin_roots f⟩

section scalar_tower

variables {K L F} [algebra F K] [algebra F L] [is_scalar_tower F K L]

variables {K}
instance map (f : F[X]) [is_splitting_field F L f] :
  is_splitting_field K L (f.map $ algebra_map F K) :=
⟨by { rw [splits_map_iff, ← is_scalar_tower.algebra_map_eq], exact splits L f },
 subalgebra.restrict_scalars_injective F $
  by { rw [map_map, ← is_scalar_tower.algebra_map_eq, subalgebra.restrict_scalars_top,
    eq_top_iff, ← adjoin_roots L f, algebra.adjoin_le_iff],
  exact λ x hx, @algebra.subset_adjoin K _ _ _ _ _ _ hx }⟩

variables {K} (L)
theorem splits_iff (f : K[X]) [is_splitting_field K L f] :
  polynomial.splits (ring_hom.id K) f ↔ (⊤ : subalgebra K L) = ⊥ :=
⟨λ h, eq_bot_iff.2 $ adjoin_roots L f ▸ (roots_map (algebra_map K L) h).symm ▸
  algebra.adjoin_le_iff.2 (λ y hy,
    let ⟨x, hxs, hxy⟩ := finset.mem_image.1 (by rwa multiset.to_finset_map at hy) in
    hxy ▸ set_like.mem_coe.2 $ subalgebra.algebra_map_mem _ _),
 λ h, @ring_equiv.to_ring_hom_refl K _ ▸
  ring_equiv.self_trans_symm (ring_equiv.of_bijective _ $ algebra.bijective_algebra_map_iff.2 h) ▸
  by { rw ring_equiv.to_ring_hom_trans, exact splits_comp_of_splits _ _ (splits L f) }⟩

theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [is_splitting_field F K f]
  [is_splitting_field K L (g.map $ algebra_map F K)] :
  is_splitting_field F L (f * g) :=
⟨(is_scalar_tower.algebra_map_eq F K L).symm ▸ splits_mul _
  (splits_comp_of_splits _ _ (splits K f))
  ((splits_map_iff _ _).1 (splits L $ g.map $ algebra_map F K)),
 by rw [polynomial.map_mul, roots_mul (mul_ne_zero (map_ne_zero hf : f.map (algebra_map F L) ≠ 0)
        (map_ne_zero hg)), multiset.to_finset_add, finset.coe_union,
      algebra.adjoin_union_eq_adjoin_adjoin,
      is_scalar_tower.algebra_map_eq F K L, ← map_map,
      roots_map (algebra_map K L) ((splits_id_iff_splits $ algebra_map F K).2 $ splits K f),
      multiset.to_finset_map, finset.coe_image, algebra.adjoin_algebra_map, adjoin_roots,
      algebra.map_top, is_scalar_tower.adjoin_range_to_alg_hom, ← map_map, adjoin_roots,
      subalgebra.restrict_scalars_top]⟩

end scalar_tower

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [algebra K F] (f : K[X]) [is_splitting_field K L f]
  (hf : polynomial.splits (algebra_map K F) f) : L →ₐ[K] F :=
if hf0 : f = 0 then (algebra.of_id K F).comp $
  (algebra.bot_equiv K L : (⊥ : subalgebra K L) →ₐ[K] K).comp $
  by { rw ← (splits_iff L f).1 (show f.splits (ring_hom.id K), from hf0.symm ▸ splits_zero _),
  exact algebra.to_top } else
alg_hom.comp (by { rw ← adjoin_roots L f, exact classical.choice (lift_of_splits _ $ λ y hy,
    have aeval y f = 0, from (eval₂_eq_eval_map _).trans $
      (mem_roots $ by exact map_ne_zero hf0).1 (multiset.mem_to_finset.mp hy),
    ⟨is_algebraic_iff_is_integral.1 ⟨f, hf0, this⟩,
      splits_of_splits_of_dvd _ hf0 hf $ minpoly.dvd _ _ this⟩) })
  algebra.to_top

theorem finite_dimensional (f : K[X]) [is_splitting_field K L f] : finite_dimensional K L :=
⟨@algebra.top_to_submodule K L _ _ _ ▸ adjoin_roots L f ▸
  fg_adjoin_of_finite (finset.finite_to_set _) (λ y hy,
  if hf : f = 0
  then by { rw [hf, polynomial.map_zero, roots_zero] at hy, cases hy }
  else is_algebraic_iff_is_integral.1 ⟨f, hf, (eval₂_eq_eval_map _).trans $
    (mem_roots $ by exact map_ne_zero hf).1 (multiset.mem_to_finset.mp hy)⟩)⟩

instance (f : K[X]) : _root_.finite_dimensional K f.splitting_field :=
finite_dimensional f.splitting_field f

/-- Any splitting field is isomorphic to `splitting_field f`. -/
def alg_equiv (f : K[X]) [is_splitting_field K L f] : L ≃ₐ[K] splitting_field f :=
begin
  refine alg_equiv.of_bijective (lift L f $ splits (splitting_field f) f)
    ⟨ring_hom.injective (lift L f $ splits (splitting_field f) f).to_ring_hom, _⟩,
  haveI := finite_dimensional (splitting_field f) f,
  haveI := finite_dimensional L f,
  have : finite_dimensional.finrank K L = finite_dimensional.finrank K (splitting_field f) :=
  le_antisymm
    (linear_map.finrank_le_finrank_of_injective
      (show function.injective (lift L f $ splits (splitting_field f) f).to_linear_map, from
        ring_hom.injective (lift L f $ splits (splitting_field f) f : L →+* f.splitting_field)))
    (linear_map.finrank_le_finrank_of_injective
      (show function.injective (lift (splitting_field f) f $ splits L f).to_linear_map, from
        ring_hom.injective (lift (splitting_field f) f $ splits L f : f.splitting_field →+* L))),
  change function.surjective (lift L f $ splits (splitting_field f) f).to_linear_map,
  refine (linear_map.injective_iff_surjective_of_finrank_eq_finrank this).1 _,
  exact ring_hom.injective (lift L f $ splits (splitting_field f) f : L →+* f.splitting_field)
end

lemma of_alg_equiv [algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [is_splitting_field K F p] :
  is_splitting_field K L p :=
begin
  split,
  { rw ← f.to_alg_hom.comp_algebra_map,
    exact splits_comp_of_splits _ _ (splits F p) },
  { rw [←(algebra.range_top_iff_surjective f.to_alg_hom).mpr f.surjective,
        ←root_set, adjoin_root_set_eq_range (splits F p), root_set, adjoin_roots F p] },
end

end is_splitting_field

end splitting_field

end polynomial

namespace intermediate_field

open polynomial

variables [field K] [field L] [algebra K L] {p : K[X]}

lemma splits_of_splits {F : intermediate_field K L} (h : p.splits (algebra_map K L))
  (hF : ∀ x ∈ p.root_set L, x ∈ F) : p.splits (algebra_map K F) :=
begin
  simp_rw [root_set, finset.mem_coe, multiset.mem_to_finset] at hF,
  rw splits_iff_exists_multiset,
  refine ⟨multiset.pmap subtype.mk _ hF, map_injective _ (algebra_map F L).injective _⟩,
  conv_lhs { rw [polynomial.map_map, ←is_scalar_tower.algebra_map_eq,
    eq_prod_roots_of_splits h, ←multiset.pmap_eq_map _ _ _ hF] },
  simp_rw [polynomial.map_mul, polynomial.map_multiset_prod,
    multiset.map_pmap, polynomial.map_sub, map_C, map_X],
  refl,
end

end intermediate_field
