/-
Copyright (c) 2022 ACL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ACL
-/

import tactic
import logic.equiv.basic
import tactic.basic tactic.group
import group_theory.group_action.sub_mul_action
import group_theory.group_action.embedding
import group_theory.perm.cycle.type
import group_theory.perm.list
import group_theory.perm.cycle.concrete
import group_theory.group_action.quotient
import group_theory.specific_groups.alternating
import group_theory.abelianization

-- import .sub_mul_actions
-- import .multiple_transitivity
-- import .for_mathlib.extensions

open_locale pointwise

section lists

variables {α β : Type*}

lemma list.disjoint_map (f : α → β) (s t : list α)
  (hf : function.injective f) (h : list.disjoint s t) :
  list.disjoint (s.map f) (t.map f) :=
begin
  simp only [list.disjoint],
  intros b hbs hbt,
  rw list.mem_map at hbs hbt,
  obtain ⟨a, ha, rfl⟩ := hbs,
  apply h ha,
  obtain ⟨a', ha', ha''⟩ := hbt,
  rw hf ha''.symm, exact ha',
end

lemma list.disjoint_pmap {p : α → Prop} (f : Π (a : α), p a → β) (s t : list α)
  (hs : ∀ a ∈ s, p a) (ht : ∀ a ∈ t, p a)
  (hf : ∀ (a a' : α) (ha : p a) (ha' : p a'), f a ha = f a' ha' → a = a')
  (h : list.disjoint s t) : list.disjoint (list.pmap f s hs) (list.pmap f t ht) :=
begin
  simp only [list.disjoint],
  intros b hbs hbt,
  rw list.mem_pmap at hbs hbt,
  obtain ⟨a, ha, rfl⟩ := hbs,
  apply h ha,
  obtain ⟨a', ha', ha''⟩ := hbt,
  rw hf a a' (hs a ha) (ht a' ha') ha''.symm,
  exact ha',
end

def list.mk_subtype {p : α → Prop} :
  Π (l : list α) (hl : ∀ a ∈ l, p a), list (subtype p)
| [] := λ _, list.nil
| (a :: l) := λ hl, (⟨a, hl a (list.mem_cons_self a l)⟩ ::
  list.mk_subtype l (λ b hb, hl b (list.mem_cons_of_mem a hb)))

lemma list.coe_mk {p :α → Prop} (l : list α) (hl : ∀ a ∈ l, p a) :
  list.map coe (list.mk_subtype l hl) = l :=
begin
  induction l with a l' hl',
  -- nil
  simp only [list.mk_subtype, list.map_nil],
  -- (a :: l)
  simp only [list.mk_subtype, list.map_cons],
  split,
  simp only [subtype.coe_mk],
  apply hl',
end

def list.mk_subtype' {p : α → Prop} (l : list α) (hl : ∀ a ∈ l, p a) :
  list (subtype p) :=
  list.pmap (λ (a : α) (ha : p a), (⟨a, ha⟩ : subtype p)) l hl

lemma list.coe_mk' {p :α → Prop} (l : list α) (hl : ∀ a ∈ l, p a) :
  list.map coe (list.mk_subtype' l hl) = l :=
begin
  simp only [list.mk_subtype'],
  rw list.map_pmap,
  rw list.pmap_congr,
  rw list.pmap_eq_map,
  rw list.map_id,
  exact hl,
  intros a ha hpa _,
  simp only [subtype.coe_mk, id.def],
end

example [decidable_eq α] (p : α → Prop) [decidable_pred p] (s : finset α) (hs : ∀ a ∈ s, p a) :
  finset.image coe (finset.subtype p s) = s :=
begin
  ext,
  simp only [finset.mem_image, finset.mem_subtype, exists_prop, subtype.exists,
    subtype.coe_mk, exists_eq_right_right, and_iff_right_iff_imp],
  exact hs a,
end

example (f : α → β) (hf : function.injective f) (l : list (set α))
  (hl : list.pairwise disjoint l) :
  list.pairwise disjoint (list.map (set.image f) l) :=
begin
  rw list.pairwise_map,
  simp_rw set.disjoint_image_iff hf,
  exact hl,
end

end lists

section stabilizers

variables {G : Type*} [group G] {X : Type*} [mul_action G X] (s : set X)

open_locale pointwise

variables (G s)
def sub_mul_action_of_stabilizer : sub_mul_action (mul_action.stabilizer G s) X :=
{ carrier := s,
  smul_mem' := λ g x hx,
  begin
    have h : g • x ∈ g • s := ⟨x, hx, rfl⟩,
    let hg := g.prop, rw mul_action.mem_stabilizer_iff at hg,
    change g • s = s at hg,
    rw hg at h, exact h,
  end}

instance mul_action_of_stabilizer : mul_action (mul_action.stabilizer G s) s :=
  (sub_mul_action_of_stabilizer G s).mul_action

variables {G s}
def sub_mul_action_of_stabilizer_hom : mul_action.stabilizer G s →* equiv.perm s :=
  mul_action.to_perm_hom (mul_action.stabilizer G s) s

lemma sub_mul_action_of_stabilizer_hom_def
  (g : G) (hg : g ∈ mul_action.stabilizer G s) (x : X) (hx : x ∈ s) :
  ↑(sub_mul_action_of_stabilizer_hom (⟨g, hg⟩ : mul_action.stabilizer G s) (⟨x, hx⟩ : s)) = g • x :=
begin
  simp only [sub_mul_action_of_stabilizer_hom],
  simp only [mul_action.to_perm_hom_apply, mul_action.to_perm_apply],
  refl,
end

end stabilizers


section junk

variables (α : Type*) [decidable_eq α] [fintype α]


def K4'  := finset.filter (λ g : equiv.perm (fin 4), g = 1 ∨ (equiv.perm.cycle_type g = {2,2}))
  (set.univ).to_finset

#check K4'

/- Lean calcule K4.card = 4 mais c'est lent ! -/
-- #eval K4.card

/- c = {c1,...,cm}
  on choisit un cycle de longueur c1 : n!/(n-c1)! c1
  un autre de longueur c2 : (n-c1)!/(n-c1-c2)! c2
  etc., ce qui donne n!/((n - c.sum)! * c.prod)
  et il reste à diviser par les permutations possibles des cycles de même longueur :
  pour chaque k, dk = nombre de i tq ci = k
  diviser par prod (dk!) -/


def foo (c : multiset ℕ) (n : ℕ) := if (c.sum ≤ n) then
  n.factorial / ((n - c.sum).factorial * c.prod
  * multiset.prod ((multiset.map (λ n, (multiset.count n c).factorial) c.dedup)))
else 0

#eval foo {2} 5
#eval foo {2,2} 4
#eval foo {2,4} 5

def f : list ℕ → list ℕ
  | [] := list.nil
  | (a :: l) := (a :: list.map (nat.add a) (f l))

#eval f [2,5,9]

def list.ranges' : list ℕ → list (finset ℕ)
  | [] := list.nil
  | (a :: l) := (finset.range(a) :: list.map (finset.image (nat.add a)) (list.ranges' l))

#eval list.ranges' [2,5,4]

end junk

section ranges

def list.ranges : list ℕ → list (list ℕ)
  | [] := list.nil
  | (a :: l) := (list.range(a) :: list.map (list.map (nat.add a)) (list.ranges l))

#eval list.ranges [2,5,4]

lemma list.ranges_disjoint (l : list ℕ) : list.pairwise list.disjoint (list.ranges l) :=
begin
  induction l with a l hl,
  -- nil
  exact list.pairwise.nil,
  -- (a :: l)
  simp only [list.ranges, list.pairwise_cons],
  split,
  { intros s hs,
    obtain ⟨s', hs', rfl⟩ := list.mem_map.mp hs,
    intros u hu,
    rw list.mem_map, rintro ⟨v, hv, rfl⟩,
    rw list.mem_range at hu,
    exact lt_iff_not_le.mp hu (le_self_add), },
  { rw list.pairwise_map,
    apply list.pairwise.imp _ hl,
    intros u v, apply list.disjoint_map _ u v _,
    exact λ u v, nat.add_left_cancel, },
end

lemma list.ranges_nodup (l : list ℕ) : ∀ s ∈ list.ranges l, list.nodup s :=
begin
  induction l with a l hl,
  { -- nil
    intros s hs, exfalso,
    simpa only [list.ranges, list.not_mem_nil] using hs, },
  { -- (a :: l)
    intros s hs,
    simp only [list.ranges, list.mem_cons_iff] at hs,
    cases hs with hs hs,
      -- s = a
      rw hs, exact list.nodup_range a,
      -- s ∈ l
      rw list.mem_map at hs, obtain ⟨t, ht, rfl⟩ := hs,
      refine list.nodup.map (λ u v, nat.add_left_cancel) (hl t ht), }
end

lemma list.ranges_length (l : list ℕ) :
  list.map (list.length) l.ranges = l :=
begin
  induction l with a l hl,
  -- nil
  simp only [list.ranges, list.map_nil],
  -- (a :: l)
  simp only [list.ranges, list.map_cons],
  split,
  exact finset.card_range a,
  simp only [list.map_map],
  conv_rhs { rw ← hl },
  apply list.map_congr,
  intros s hs,
  simp only [function.comp_app],
  rw list.length_map,
end

lemma list.ranges_lt (l : list ℕ) {s : list ℕ} {n : ℕ} (hs : s ∈ list.ranges l)
  (hn : n ∈ s) : n < l.sum :=
begin
  revert s n,
  induction l with a l hl,
  { -- nil
    intros s n hs hn,
    exfalso,
    simp only [list.ranges] at hs,
    exact list.not_mem_nil s hs, },
  { -- (a :: l)
    intros s n hs hn,
    simp only [list.ranges, list.mem_cons_iff] at hs,
    cases hs with hs hs,
    { rw [hs, list.mem_range] at hn,
      apply lt_of_lt_of_le hn,
      rw list.sum_cons,
      exact le_self_add, },
    { rw list.mem_map at hs, obtain ⟨t, ht, rfl⟩ := hs,
      rw list.mem_map at hn, obtain ⟨m, hm, rfl⟩ := hn,
      simp only [list.sum_cons, nat.add_def, add_lt_add_iff_left],
      exact hl ht hm, }, },
end

end ranges

section cycle_types

variables (α : Type*) [decidable_eq α] [fintype α]

def equiv.perm_with_cycle_type (c : multiset ℕ) :=
  finset.filter (λ (g : equiv.perm α), equiv.perm.cycle_type g = c) (set.univ).to_finset

variable {α}
lemma equiv.perm_with_cycle_type_empty {c : multiset ℕ} (hc : fintype.card α < c.sum) :
  equiv.perm_with_cycle_type α c = ∅ :=
begin
  apply finset.eq_empty_of_forall_not_mem,
  intro g,
  unfold equiv.perm_with_cycle_type,
  simp only [set.to_finset_univ, finset.mem_filter, finset.mem_univ, true_and],
  intro hg, apply lt_iff_not_le.mp hc, rw ← hg,
  rw equiv.perm.sum_cycle_type,
  refine (equiv.perm.support g).card_le_univ,
end

lemma list.exists_pw_disjoint_with_card {c : list ℕ} (hc : c.sum ≤ fintype.card α) :
  ∃ (o : list (list α)),
  (list.map (list.length) o = c) ∧ (∀ s ∈ o, list.nodup s) ∧ list.pairwise list.disjoint o :=
begin
  have : nonempty (fin (fintype.card α) ≃ α) := by simp only [← fintype.card_eq, fintype.card_fin],
  have e := this.some,

  let klift : Π (n : ℕ), (n < fintype.card α) → fin (fintype.card α) :=
    λ n hn, (⟨n, hn⟩ : fin(fintype.card α)),

  let klift' : Π (l : list ℕ), (∀ a ∈ l, a < fintype.card α) → list (fin (fintype.card α)) :=
  list.pmap klift,

  have hc'_lt : ∀ (a : list ℕ), a ∈ c.ranges → ∀ (a_1 : ℕ), a_1 ∈ a → a_1 < fintype.card α,
  { intros s u a ha,
    apply lt_of_lt_of_le _ hc,
    apply list.ranges_lt c u ha, },

  let l := list.pmap klift' (list.ranges c) hc'_lt,
  have hl : ∀ (a : list ℕ) (ha : a ∈ c.ranges),
    list.map (fin.coe_embedding) (klift' a (hc'_lt a ha)) = a,
  { intros a ha,
    simp only [klift', klift],
    conv_rhs { rw ← list.map_id a}, rw list.map_pmap,
    simp only [fin.coe_embedding_apply, fin.coe_mk, list.pmap_eq_map, list.map_id'', list.map_id], },

  have hl' : list.map (list.map (fin.coe_embedding)) l = list.ranges c,
  { conv_rhs { rw ← list.map_id (list.ranges c) },
    rw ← list.pmap_eq_map _ id (list.ranges c) (hc'_lt),
    simp only [l],
    rw list.map_pmap,
    apply list.pmap_congr,
    intros a ha ha' ha'',
    simp only [hl a ha, id.def], },

  use list.map (list.map e) l,

  split,
  {  -- length
    rw ← list.ranges_length c,
    simp only [list.map_map, l, list.map_pmap, function.comp_app, list.length_map,
      list.length_pmap, list.pmap_eq_map], },
  split,
  { -- nodup
    intro s,
    rw list.mem_map,
    rintro ⟨t, ht, rfl⟩,
    apply list.nodup.map (equiv.injective e),
    simp only [l, list.mem_pmap] at ht,
    obtain ⟨u, hu, rfl⟩ := ht,
    apply list.nodup.of_map,
    rw hl u hu, apply list.ranges_nodup c u hu, },
  { -- pairwise disjoint
    suffices : list.pairwise list.disjoint l,
    refine list.pairwise.map _ _ this ,
    { intros s t hst,
      apply list.disjoint_map,
      exact equiv.injective e, exact hst, },
    { -- list.pairwise list.disjoint l,
      simp only [l],
      apply list.pairwise.pmap (list.ranges_disjoint c),
      intros u hu v hv huv,
      simp only [klift'],
      apply list.disjoint_pmap,
      { simp only [klift],
        intros a a' ha ha' h,
        simpa only [fin.mk_eq_mk] using h, },
      exact huv,
      }, },
end

lemma equiv.perm_with_cycle_type_nonempty_iff {c : list ℕ} :
  (c.sum ≤ fintype.card α ∧ (∀ a ∈ c, 2 ≤ a)) ↔ (equiv.perm_with_cycle_type α (c : multiset ℕ)).nonempty :=
begin
  split,
  { rintro ⟨hc, h2c⟩,
    obtain ⟨p, hp_length, hp_nodup, hp_disj⟩ := list.exists_pw_disjoint_with_card hc,
    use list.prod (list.map (λ l, list.form_perm l) p),
    simp only [equiv.perm_with_cycle_type, finset.mem_filter, set.to_finset_univ,
      finset.mem_univ, true_and],
    have hp2 : ∀ (x : list α) (hx : x ∈ p), 2 ≤ x.length,
    { intros x hx,
      apply h2c x.length,
      rw [← hp_length, list.mem_map],
      exact ⟨x, hx, rfl⟩, },
    rw equiv.perm.cycle_type_eq _ rfl,
    { -- lengths
      apply congr_arg,
      rw list.map_map, rw ← hp_length,
      apply list.map_congr,
      intros x hx, simp only [function.comp_app],
      have hx_nodup : x.nodup := hp_nodup x hx,
      rw list.support_form_perm_of_nodup x hx_nodup,
      { -- length
        rw list.to_finset_card_of_nodup hx_nodup, },
      { -- length >= 1
        intros a h,
        apply nat.not_succ_le_self 1,
        conv_rhs { rw ← list.length_singleton a, }, rw ← h,
        exact hp2 x hx, }, },
    { -- cycles
      intro g,
      rw list.mem_map,
      rintro ⟨x, hx, rfl⟩,
      have hx_nodup : x.nodup := hp_nodup x hx,
      rw ← cycle.form_perm_coe x hx_nodup,
      apply cycle.is_cycle_form_perm ,
      rw cycle.nontrivial_coe_nodup_iff hx_nodup,
      exact hp2 x hx, },
    { -- disjoint
      rw list.pairwise_map,
      apply list.pairwise.imp_of_mem _ hp_disj,
      intros a b ha hb hab,
      rw list.form_perm_disjoint_iff (hp_nodup a ha) (hp_nodup b hb) (hp2 a ha) (hp2 b hb),
      exact hab, }, },
  { -- empty case
    intro h,
    obtain ⟨g, hg⟩ := h,
    simp only [equiv.perm_with_cycle_type, set.to_finset_univ, finset.mem_filter,
      finset.mem_univ, true_and] at hg,
    split,
    rw [← multiset.coe_sum, ← hg, equiv.perm.sum_cycle_type ],
    exact (equiv.perm.support g).card_le_univ,
    intros a ha,
    rw [← multiset.mem_coe, ← hg] at ha,
    exact equiv.perm.two_le_of_mem_cycle_type ha, },
end

lemma equiv.perm.mem_cycle_factors_conj (g k c : equiv.perm α) :
  c ∈ g.cycle_factors_finset ↔ (k * c * k⁻¹) ∈ (k * g * k⁻¹).cycle_factors_finset :=
begin
  suffices imp_lemma : ∀ (g k c : equiv.perm α),
    c ∈ g.cycle_factors_finset → (k * c * k⁻¹) ∈ (k * g * k⁻¹).cycle_factors_finset,
  { split,
    apply imp_lemma g k c,
    intro h,
    suffices : ∀ (h : equiv.perm α), h = k⁻¹ * (k * h * k⁻¹) * k,
    { rw [this g, this c], apply imp_lemma, exact h, },
    intro h,
    simp only [← mul_assoc],
    simp only [mul_left_inv, one_mul, inv_mul_cancel_right], },
  { intros g k c,
    simp only [equiv.perm.mem_cycle_factors_finset_iff],
    rintro ⟨hc, hc'⟩,
    split,
    exact equiv.perm.is_cycle.is_cycle_conj hc,
    intros a ha,
    simp only [equiv.perm.coe_mul, embedding_like.apply_eq_iff_eq],
    apply hc',
    rw equiv.perm.mem_support at ha ⊢,
    intro ha', apply ha,
    simp only [mul_smul, ← equiv.perm.smul_def] at ha' ⊢,
    rw ha',
    simp only [equiv.perm.smul_def, equiv.perm.apply_inv_self], },
end

example {β : Type*} (e : equiv α β) (a : α) (b : β) :
  e a = b ↔ a = e.symm b :=
begin
  refine equiv.apply_eq_iff_eq_symm_apply e
end

lemma equiv.perm.conj_support_eq (k : conj_act(equiv.perm α)) (g : equiv.perm α) (a : α) :
  a ∈ (k • g).support ↔ k⁻¹.of_conj_act a ∈ g.support :=
begin
  simp only [equiv.perm.mem_support, conj_act.smul_def],
  rw not_iff_not ,
  simp only [equiv.perm.coe_mul, function.comp_app, conj_act.of_conj_act_inv],
  exact equiv.apply_eq_iff_eq_symm_apply (k.of_conj_act),
end

lemma equiv.perm.mem_cycle_factors_conj' (k : conj_act(equiv.perm α)) (g c : equiv.perm α) :
  c ∈ g.cycle_factors_finset ↔ k • c ∈ (k • g).cycle_factors_finset :=
begin
  suffices imp_lemma : ∀ (k : conj_act(equiv.perm α)) (g c : equiv.perm α),
    c ∈ g.cycle_factors_finset → k • c ∈ (k • g).cycle_factors_finset,
  { split,
    { apply imp_lemma k g c, },
    { intro h,
      rw ← inv_smul_smul k c, rw ← inv_smul_smul k g,
      apply imp_lemma,  exact h, } },
  { intros k g c,
    simp only [equiv.perm.mem_cycle_factors_finset_iff],
    rintro ⟨hc, hc'⟩,
    split,
    { exact equiv.perm.is_cycle.is_cycle_conj hc, },
    { intro a,
      rw equiv.perm.conj_support_eq,
      intro ha,
      simp only [conj_act.smul_def],
      simpa using hc' _ ha, }, },
end

open_locale classical

lemma equiv.perm.mem_cycle_factors_conj_eq (k : conj_act (equiv.perm α)) (g : equiv.perm α) :
  equiv.perm.cycle_factors_finset (k • g) = k • (equiv.perm.cycle_factors_finset g) :=
begin
  ext c,
  rw equiv.perm.mem_cycle_factors_conj' k⁻¹ (k • g) c,
  simp only [inv_smul_smul],
  exact finset.inv_smul_mem_iff,
end

example {α : Type*} (s : finset α) (a b : α) (h : a = b) : a ∈ s ↔ b ∈ s :=
begin
  refine iff_of_eq (congr_fun (congr_arg has_mem.mem h) s),
end

example (k: equiv.perm α) : mul_equiv.symm (mul_aut.conj k)
 = mul_aut.conj k⁻¹ := begin
-- simp only [map_inv],
ext g x,
rw [map_inv, mul_aut.conj_symm_apply, mul_aut.conj_inv_apply],
 end

lemma is_conj_iff_inv_is_conj {G : Type*} [group G] (a b k : G) :
  k * a * k⁻¹ = b  ↔ a = k⁻¹ * b * k :=
by rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq , mul_assoc]

lemma equiv.perm.cycle_factors_conj (g k : equiv.perm α) :
  finset.map (mul_aut.conj k).to_equiv.to_embedding g.cycle_factors_finset
  = (k * g * k⁻¹).cycle_factors_finset :=
begin
  ext c,
  rw finset.mem_map_equiv,
  rw equiv.perm.mem_cycle_factors_conj g k,
  apply iff_of_eq,
  apply congr_arg2 _ _,
  refl,
  rw is_conj_iff_inv_is_conj,
  rw [← mul_equiv.to_equiv_symm, mul_equiv.to_equiv_eq_coe, mul_equiv.coe_to_equiv,
    mul_aut.conj_symm_apply],
end


lemma mul_action.conj_act.mem_stabilizer_iff {G : Type*} [group G] (k : conj_act G)
  (g : G) : k ∈ mul_action.stabilizer (conj_act G) g ↔ k * g * k⁻¹ = g :=
begin
  simp only [mul_action.mem_stabilizer_iff, has_smul.smul],
  refl,
end

open_locale pointwise
/-
def equiv.perm.mul_action_conj_cycle_factors' (g : equiv.perm α) :=
  sub_mul_action_of_stabilizer (conj_act (equiv.perm α)) (equiv.perm α) (g.cycle_factors_finset)

def equiv.perm.mul_action_conj_cycle_factors (g : equiv.perm α) :
  sub_mul_action (mul_action.stabilizer (conj_act (equiv.perm α)) g) (equiv.perm α) :=
{ carrier := g.cycle_factors_finset,
  smul_mem' :=
  begin
    rintro ⟨k, hk⟩, intros c hc,
    simp only [finset.mem_coe] at ⊢ hc,
    change k • c ∈ _,
    rw conj_act.smul_def k c,
    rw [mul_action.mem_stabilizer_iff, conj_act.smul_def k g] at hk,
    rw [← hk, ← equiv.perm.mem_cycle_factors_conj],
    exact hc,
  end }
-/
/-
instance equiv.perm.cycle_factors_smul' {g : equiv.perm α} :
  has_smul (mul_action.stabilizer (conj_act (equiv.perm α)) g) (g.cycle_factors_finset) :=
{ smul := λ ⟨k, hk⟩ ⟨c, hc⟩, ⟨k • c,
  begin
    simp only [has_smul.smul],
    convert (equiv.perm.mem_cycle_factors_conj g k c).mp hc,
    apply symm,
    exact (mul_action.conj_act.mem_stabilizer_iff k g).mp hk,
  end⟩}
-/


lemma equiv.perm.cycle_factors_conj_smul_eq {g : equiv.perm α}
 (k : mul_action.stabilizer (conj_act (equiv.perm α)) g) (c : g.cycle_factors_finset) :
  ((k • c) : equiv.perm α) = (conj_act.of_conj_act ↑k) * ↑c * (conj_act.of_conj_act ↑k⁻¹) := rfl

/-
instance equiv.perm.cycle_factors_mul_action' (g : equiv.perm α) :
  mul_action (mul_action.stabilizer (conj_act (equiv.perm α)) g) (g.cycle_factors_finset) :=
{ one_smul := λ c, sorry,
  mul_smul := λ ⟨h, hh⟩ ⟨k, hk⟩ ⟨c, hc⟩,
  begin
    rw ← subtype.coe_inj,
    simp only [submonoid.mk_mul_mk],

    let hzz := equiv.perm.cycle_factors_smul'_eq ⟨k, hk⟩ ⟨c, hc⟩,


      sorry,

  end, },

def equiv.perm.cycle_factors_smul' (g : equiv.perm α) :
  mul_action (subgroup.zpowers g).centralizer (g.cycle_factors_finset) :=
{ one_smul := λ c, by simp only [one_mul, finset.mk_coe, subgroup.coe_one, inv_one, mul_one,
      equiv.coe_fn_mk, equiv.perm.coe_one, id.def],
  mul_smul := λ h k c, by simp only [subtype.coe_mk,
      subgroup.coe_mul, mul_inv_rev, equiv.coe_fn_mk,
      equiv.perm.coe_mul, subtype.mk_eq_mk, ← mul_assoc],
  to_has_smul := { smul :=  λ k c, ⟨k * c * k⁻¹,
    begin
      convert (equiv.perm.mem_cycle_factors_conj g k c).mp c.prop,
      simp only [← (subgroup.mem_centralizer_iff.mp k.prop) g (subgroup.mem_zpowers g),
    mul_inv_cancel_right],
    end⟩ } } -/


open_locale classical

def subgroup.mul_equiv {α β : Type*} [group α] [group β] (e : mul_equiv α β)
  {G : subgroup α} {H : subgroup β} (h : ∀ g, g ∈ G ↔ e g ∈ H) :
  mul_equiv G H :=
{ to_fun := subtype.map e.to_fun (λ g hg, (h g).mp hg), -- λ ⟨g, hg⟩, ⟨e g, h.mp hg⟩,
  inv_fun := subtype.map e.inv_fun (λ k hk,
    by simp only [h, mul_equiv.inv_fun_eq_symm, mul_equiv.apply_symm_apply, hk]),
  left_inv := λ ⟨g, hg⟩,
  begin
    rw ← subtype.coe_inj,
    simp only [subtype.map_coe],
    simp only [mul_equiv.to_fun_eq_coe, mul_equiv.inv_fun_eq_symm, mul_equiv.symm_apply_apply],
  end,
  right_inv := λ ⟨k, hk⟩,
  begin
    rw ← subtype.coe_inj,
    simp only [subtype.map_coe],
    simp only [mul_equiv.inv_fun_eq_symm, mul_equiv.to_fun_eq_coe, mul_equiv.apply_symm_apply],
  end,
  map_mul' := λ ⟨g, hg⟩ ⟨k, hk⟩,
  begin
    simp only [← subtype.coe_inj],
    rw subgroup.coe_mul,
    simp only [subtype.map_coe],
    simp only [mul_mem_class.mk_mul_mk, subgroup.coe_mk, mul_equiv.to_fun_eq_coe, map_mul],
  end, }

example {G : Type*} [group G] (g k : G) : g ⁻¹ * k = k * g⁻¹ ↔ k * g = g * k :=
begin
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_inv_eq_iff_eq_mul, inv_inv],
end

lemma group.commute_iff_mem_centralizer_zpowers {G : Type*} [group G] (g k : G) :
  commute g k ↔ k ∈ subgroup.centralizer (subgroup.zpowers g) :=
begin
  rw subgroup.mem_centralizer_iff,
  split,
  { intros H h,
    rw subgroup.mem_zpowers_iff,
    rintro ⟨n, rfl⟩,
    apply commute.zpow_left,
    exact H },
  { intro H,
    simp only [commute, semiconj_by],
    rw H g (subgroup.mem_zpowers g), },
end

example (g : equiv.perm α) :
  mul_action.stabilizer (conj_act (equiv.perm α)) g ≃* subgroup.centralizer (subgroup.zpowers g) :=
  subgroup.mul_equiv (conj_act.of_conj_act)
  (begin
    intro k,
    rw mul_action.mem_stabilizer_iff,
    simp only [has_smul.smul],
    rw mul_inv_eq_iff_eq_mul,
    rw ← group.commute_iff_mem_centralizer_zpowers,
    simp only [commute, semiconj_by],
    conv_lhs { rw eq_comm, },
  end)

example {α β : Type*} [group α] [mul_action α β] (s : finset β) (g : α) :
  coe (g • s)  = g • (s : set β) := finset.coe_smul_finset g s

open_locale classical


lemma equiv.perm.commute_of_mem_cycles_factors_commute (k g : equiv.perm α)
  (hk : ∀ (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset), commute k c) :
  commute k g :=
begin
  rw ← equiv.perm.cycle_factors_finset_noncomm_prod g
    (equiv.perm.cycle_factors_finset_mem_commute g),
  apply finset.noncomm_prod_commute ,
  simp only [id.def],
  exact hk,
end

lemma equiv.perm.self_mem_cycle_factors_commute
  (g c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) : commute c g :=
begin
  apply equiv.perm.commute_of_mem_cycles_factors_commute,
  intros c' hc',
  apply equiv.perm.cycle_factors_finset_mem_commute g c hc c' hc',
end

lemma equiv.perm.mem_cycle_factors_finset_support
  (g c: equiv.perm α) (hc : c ∈ g.cycle_factors_finset) (a : α) :
  a ∈ c.support ↔ g a ∈ c.support :=
begin
  let hc' := equiv.perm.mem_cycle_factors_finset_iff.mp hc,
  split,
  { intro ha,
    rw ← hc'.2 a ha,
    exact equiv.perm.apply_mem_support.mpr ha, },
  { intro ha,
    rw ← equiv.perm.apply_mem_support,
    suffices : c a = g a,
    rw this, exact ha,
    apply equiv.injective g,
    rw ←  hc'.2 (g a) ha,
    simp only [← equiv.perm.mul_apply],
    have this := equiv.perm.self_mem_cycle_factors_commute g c hc,
    simp only [commute, semiconj_by] at this,
    rw this, },
end

lemma equiv.perm.subtype_perm_apply_pow_of_mem (g : equiv.perm α)
  (s : finset α) (hs : ∀ (x : α), x ∈ s ↔ g x ∈ s)
  (n : ℕ) (x : α) (hx : x ∈ s) :
    (((g.subtype_perm hs) ^ n) (⟨x, hx⟩ : s) : α) = (g ^ n) x :=
begin
  revert x,
  induction n with n hrec,
  { -- zero case
    intros x hx,
    simp only [pow_zero, equiv.perm.coe_one, id.def, subtype.coe_mk], },
  { -- induction case
    intros x hx,
    simp only [pow_succ', equiv.perm.coe_mul, function.comp_app],
    apply hrec, },
end

lemma equiv.perm.subtype_perm_apply_zpow_of_mem (g : equiv.perm α)
  (s : finset α) (hs : ∀ (x : α), x ∈ s ↔ g x ∈ s) (i : ℤ)
  (x : α) (hx : x ∈ s) :
    (((g.subtype_perm hs) ^ i) (⟨x, hx⟩ : s) : α) = (g ^ i) x :=
begin
  induction i,
  -- nat case
  apply equiv.perm.subtype_perm_apply_pow_of_mem,
  -- neg_succ case
  simp only [zpow_neg_succ_of_nat],
  apply equiv.injective (g ^ (i+1)),
  simp only [equiv.perm.apply_inv_self],
  rw ← equiv.perm.subtype_perm_apply_pow_of_mem g s hs,
  simp only [finset.mk_coe, equiv.perm.apply_inv_self, subtype.coe_mk],
  apply finset.coe_mem,
end

/-- Restrict a permutation to its support -/
def equiv.perm.subtype_perm_of_support (c : equiv.perm α) : equiv.perm c.support :=
  equiv.perm.subtype_perm c (λ (x : α), equiv.perm.apply_mem_support.symm)


/-- Support of a cycle is nonempty -/
lemma equiv.perm.support_of_cycle_nonempty (g : equiv.perm α) (hg : g.is_cycle) :
  g.support.nonempty :=
begin
  rw ←  finset.card_pos,
  apply lt_of_lt_of_le _ (equiv.perm.is_cycle.two_le_card_support hg),
  norm_num,
end

/-- Centralizer of a cycle is powers of that cycle on the cycle -/
lemma equiv.perm.centralizer_of_cycle_on (g c : equiv.perm α) (hc : c.is_cycle) :
  (g * c = c * g) ↔  ∃ (hc' : ∀ (x : α), x ∈ c.support ↔ g x ∈ c.support),
      equiv.perm.subtype_perm g hc' ∈ subgroup.zpowers
        (c.subtype_perm_of_support) :=
begin
  split,
  { intro hgc,
    have hgc' : ∀ (x : α), x ∈ c.support ↔ g x ∈ c.support,
    { intro x,
      simp only [equiv.perm.mem_support, not_iff_not, ← equiv.perm.mul_apply],
      rw [← hgc, equiv.perm.mul_apply],
      exact (equiv.apply_eq_iff_eq g).symm, },
    use hgc',
    obtain ⟨a, ha⟩ := equiv.perm.support_of_cycle_nonempty c hc,
    have : equiv.perm.same_cycle c a (g a),
      apply equiv.perm.is_cycle.same_cycle hc (equiv.perm.mem_support.mp ha),
      exact equiv.perm.mem_support.mp ((hgc' a).mp ha),
    simp only [equiv.perm.same_cycle] at this,
    obtain ⟨i, hi⟩ := this, use i,
    ext ⟨x, hx⟩,
    simp only [equiv.perm.subtype_perm_of_support, subtype.coe_mk, equiv.perm.subtype_perm_apply],
    rw equiv.perm.subtype_perm_apply_zpow_of_mem,
    suffices : equiv.perm.same_cycle c a x,
    { obtain ⟨j, rfl⟩ := this,
      have : g * (c ^ j) = (c ^ j) * g := commute.zpow_right hgc j,
      { simp only [← equiv.perm.mul_apply, this],
        rw [← zpow_add, add_comm i j, zpow_add],
        simp only [equiv.perm.mul_apply],
        simp only [embedding_like.apply_eq_iff_eq],
        exact hi, }, },
    exact equiv.perm.is_cycle.same_cycle hc
      (equiv.perm.mem_support.mp ha) (equiv.perm.mem_support.mp hx), },
  { -- converse
    rintro ⟨hc', h⟩,
    obtain ⟨i, hi⟩ := h,
    suffices hi' : ∀ (x : α) (hx : x ∈ c.support), g x = (c ^ i) x,
    { ext x,
      simp only [equiv.perm.coe_mul, function.comp_app],
      by_cases hx : x ∈ c.support,
      { -- hx : x ∈ c.support
        rw hi' x hx,
        rw hi' (c x) (equiv.perm.apply_mem_support.mpr hx),
        simp only [← equiv.perm.mul_apply, ← zpow_add_one, ← zpow_one_add],
        rw int.add_comm 1 i, },
      { -- hx : x ∉ c.support
        rw equiv.perm.not_mem_support.mp hx, apply symm,
        rw ← equiv.perm.not_mem_support,
        intro hx', apply hx,
        exact (hc' x).mpr hx', }, },
    { -- proof of hi'
      intros x hx,
      let hix := equiv.perm.congr_fun hi ⟨x, hx⟩,
      simp only [← subtype.coe_inj, equiv.perm.subtype_perm_of_support] at hix,
      simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply,
        equiv.perm.subtype_perm_apply_zpow_of_mem] at hix,
      exact hix.symm, } },
end

/-- A permutation restricted to the support of a cycle factor is that cycle factor -/
lemma equiv.perm.subtype_perm_on_cycle_factor (g c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) :
  (g.subtype_perm ((equiv.perm.mem_cycle_factors_finset_support g c hc)))
  = (c.subtype_perm_of_support) :=
begin
  ext ⟨x, hx⟩,
  simp only [equiv.perm.subtype_perm_of_support, subtype.coe_mk, equiv.perm.subtype_perm_apply],
  exact ((equiv.perm.mem_cycle_factors_finset_iff.mp hc).2 x hx).symm,
end

lemma equiv.perm.centralizer_mem_cycle_factors_iff (g k : equiv.perm α) (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) :
  k * c = c * k ↔
  ∃ (hc' : ∀ (x : α), x ∈ c.support ↔ k x ∈ c.support),
      k.subtype_perm hc' ∈ subgroup.zpowers (g.subtype_perm
        ((equiv.perm.mem_cycle_factors_finset_support g c hc))) :=
begin
  split,
  { intro H,
    obtain ⟨hc', H'⟩ := (equiv.perm.centralizer_of_cycle_on k c
      (equiv.perm.mem_cycle_factors_finset_iff.mp hc).1).mp H,
    rw ← equiv.perm.subtype_perm_on_cycle_factor g c hc at H',
    exact ⟨hc', H'⟩, },
  { rintro ⟨hc', H'⟩,
    rw equiv.perm.subtype_perm_on_cycle_factor g c hc at H',
    rw equiv.perm.centralizer_of_cycle_on k c (equiv.perm.mem_cycle_factors_finset_iff.mp hc).1,
    exact ⟨hc', H'⟩, },
end

-- The axiom of choice…
example (ι : Type*) (α : Π (i : ι), Type*) (f : Π i, set (α i))
  (h :∀ i, (f i).nonempty)  : ∃ (a : Π i, α i), (∀ i, a i ∈ f i) :=
begin
  suffices : nonempty (Π i, (f i)),
  obtain a := this.some,
  use λ i, ↑(a i),
  intro i, refine subtype.mem (a i),
  rw ← not_is_empty_iff ,
  intro h',
  rw is_empty_pi at h',
  obtain ⟨i, hi⟩ := h',
  rw ← not_nonempty_iff  at hi,
  apply hi,
  simp only [set.nonempty_coe_sort],
  exact h i,
end


example {α β : Type*} : ↥(∅ : set α) → β :=
begin
  refine is_empty_elim,
end

example (ι : Type*) (α : Π (i : ι), Type*) (f : Π (i : ι), set (α i))
  (h :∀  i, (f i).nonempty) (s : finset ι) : ∃ (a : Π (i : s), α i), (∀ i : s, a i ∈ f i) :=
begin
  apply finset.induction_on s,
  { -- empty s
    apply exists.intro,
    intro i, exfalso, exact finset.not_mem_empty _ i.prop,
    intro i, exfalso, exact finset.not_mem_empty _ i.prop, },
  { -- insert
    intros k s hks hrec,
    obtain ⟨a, ha⟩ := hrec,
    apply exists.intro,
    rintro ⟨i,hi⟩,
    rw finset.mem_insert at hi,
    cases hi with hi hi,



    sorry, },
end

example (g : equiv.perm α) (τ : equiv.perm (g.cycle_factors_finset)) :
  ∃ (k : equiv.perm α), (g * k = k * g) ∧ (∀ (c : g.cycle_factors_finset),
    k • (c : equiv.perm α).support = (τ c : equiv.perm α).support) :=
begin

  have this : ∀(c : g.cycle_factors_finset), ∃ (a : α), a ∈ (c : equiv.perm α).support,
  sorry,
  have : ∃ (a : g.cycle_factors_finset → α),
  ∀ (c : g.cycle_factors_finset), (a c) ∈ (c : equiv.perm α).support,


  let p : Π (c : g.cycle_factors_finset), (c : equiv.perm α).support → g.cycle_factors_finset :=
    λ c hc, c,

  have : ∃ (a : g.cycle_factors_finset → α),
    ∀ c :g.cycle_factors_finset, a c ∈ (c : equiv.perm α).support,
  sorry,

  sorry,
end




lemma equiv.perm_conj_stabilizer_card (g : equiv.perm α) (l : list ℕ)
  (hc : g.cycle_type = l) :
  fintype.card (mul_action.stabilizer (conj_act (equiv.perm α)) g) =
   (fintype.card α - l.sum).factorial * (l.prod *
    (list.map (λ (n : ℕ), (list.count n l).factorial) l.dedup).prod) :=
begin
  -- regarder l'action du stabilizateur sur g.cycle_factors
  let s : set (equiv.perm α) := equiv.perm.cycle_factors_finset g,
  let H := mul_action.stabilizer (conj_act (equiv.perm α)) s,
  let K := mul_action.stabilizer (conj_act (equiv.perm α)) g,
  have hKH : K ≤ H,
  { simp only [K, H, s], intro k,
    simp only [mul_action.mem_stabilizer_iff],
    intro hk,
    rw [← finset.coe_smul_finset k _, ← equiv.perm.mem_cycle_factors_conj_eq, hk], },

  haveI :=
      (sub_mul_action_of_stabilizer
        (conj_act (equiv.perm α))
        (equiv.perm.cycle_factors_finset g : set (equiv.perm α))).mul_action,

  -- on obtient un morphisme vers un groupe symétrique
  let φ : K →* equiv.perm s := (mul_action.to_perm_hom H s).comp (subgroup.inclusion hKH),

  have φ_eq : ∀ (k : conj_act (equiv.perm α)) (hk : k ∈ K)
    (c : equiv.perm α) (hc : c ∈ equiv.perm.cycle_factors_finset g),
      (φ ⟨k, hk⟩ ⟨c, hc⟩ : equiv.perm α) = k • c,
  { intros k hk c hc,
    simp only [φ],
    simp only [monoid_hom.coe_comp, function.comp_app, mul_action.to_perm_hom_apply, mul_action.to_perm_apply],
    refl, },
  have φ_eq' : ∀ (k : equiv.perm α) (hk : conj_act.to_conj_act k ∈ K)
    (c : equiv.perm α) (hc : c ∈ equiv.perm.cycle_factors_finset g),
      (φ ⟨conj_act.to_conj_act k, hk⟩ ⟨c, hc⟩ :equiv.perm α) = k * c * k⁻¹,
  { intros k hk c hc,
    rw φ_eq,
    rw [conj_act.smul_eq_mul_aut_conj, conj_act.of_conj_act_to_conj_act k, mul_aut.conj_apply], },
  -- son image :
  have lemm_range : ∀ (k : equiv.perm (equiv.perm.cycle_factors_finset g)),
    k ∈ φ.range ↔ ∀ c : equiv.perm.cycle_factors_finset g,
      (equiv.perm.support ((k c) : equiv.perm α)).card =
        (equiv.perm.support (c : equiv.perm α)).card,
  { intro k,
    split,
    { simp only [monoid_hom.mem_range],
      rintro ⟨⟨k, hk⟩, rfl⟩,
      rintro ⟨c, hc⟩,
      rw [φ_eq, subtype.coe_mk],
      rw conj_act.smul_def,
      rw equiv.perm.card_support_conj, },
    { intro hk,

      let Tac := { ac : α × (equiv.perm α) // ac.1 ∈ ac.2.support ∧ ac.2 ∈ g.cycle_factors_finset },
      let hf' : Tac → α := λ ⟨⟨a, c⟩, ⟨hac, hc⟩⟩, a,
      /- !!! ICI CA NE SUFFIT PAS !!!s
       IL FAUT AJUSTER LES ÉQUIVALENCES  (e c) : c ≃ k • c SI ON VEUT QUE L'ENSEMBLE COMMUTE À g !
        x ∈ c : g x ∈ c
        h x = (e c) x ∈ k • c,
        g h x = g ((e c) x)
        h g x = (e c) (g x)
        on veut donc que g ∘ (e c) = (e c) ∘ g : c → (k • c)
        a ∈ c, (e c) a = b
        x = (g ^ i) a, (e c) x = (e c) (g ^ i) a = (g ^ i) (e c) a = (g ^ i) b


        -/
      let hg' : Tac → α := λ ⟨⟨a, c⟩, ⟨hac, hc⟩⟩, (finset.equiv_of_card_eq (hk ⟨c, hc⟩).symm) ⟨a, hac⟩,
      let hh := function.extend hf' hg' id,
      have hf'_inj : function.injective hf',
      { rintros ⟨⟨a, c⟩, ⟨hac, hc⟩⟩ ⟨⟨b, d⟩, ⟨hbd, hd⟩⟩ hab,
        simp only [prod.mk.inj_iff], apply and.intro hab,
        by_contradiction hcd,
        have := (g.cycle_factors_finset_pairwise_disjoint c hc d hd hcd),
        rw [equiv.perm.disjoint_iff_disjoint_support, finset.disjoint_iff_ne] at this,
        exact this a hac b hbd hab, },
      have hh_1 : ∀ (x : α) (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) (hxc : x ∈ c.support),
        hh x = (finset.equiv_of_card_eq (hk ⟨c, hc⟩).symm) ⟨x, hxc⟩,
      { intros x c hc hxc,
        simp only [hh],
        have x_eq : x = hf' (⟨⟨x,c⟩, ⟨hxc, hc⟩⟩ : Tac), refl,
        conv_lhs { rw x_eq },
        rw function.extend_apply hf'_inj hg' id (⟨⟨x,c⟩, ⟨hxc, hc⟩⟩ : Tac), },
      have hh_1' : ∀ (x : α) (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) (hxc : x ∈ c.support),
        hh x ∈ ((k ⟨c, hc⟩) : equiv.perm α).support,
      { intros x c hc hxc, rw hh_1 x c hc hxc,
        apply finset.coe_mem, },

      have hh_2 : ∀ (x : α),
        ¬ (∃ (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset), x ∈ c.support) →
        hh x = x,
      { intros x hx,
        simp only [hh],
        suffices hx' : ¬ (∃ ac : Tac, hf' ac = x),
        rw function.extend_apply' hg' id x hx',
        simp only [id.def],
        { rintro ⟨⟨⟨a,c⟩ , ⟨hac, hc⟩⟩, hacx⟩,
          apply hx, use c, use hc, rw ← hacx, exact hac, } },
      have hh_bij : function.bijective hh,
      { apply function.injective.bijective_of_finite,
        intros x y hxy,
        by_cases hx : ∃ (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset), x ∈ c.support,
        { obtain ⟨c, hc, hxc⟩ := hx,
          by_cases hy : ∃ (d : equiv.perm α) (hc : d ∈ g.cycle_factors_finset), y ∈ d.support,
          { -- hx et hy
            obtain ⟨d, hd, hyd⟩ := hy,
            have hcd : c = d,
            { rw [← subtype.coe_mk c hc, ← subtype.coe_mk d hd, subtype.coe_inj],
              apply equiv.injective k,
              by_contradiction hcd,
              let kc := k ⟨c, hc⟩, let kd := k ⟨d, hd⟩,
              have hcd' : ↑kc ≠ ↑kd := function.injective.ne (subtype.coe_injective) hcd,
              have := g.cycle_factors_finset_pairwise_disjoint ↑kc kc.prop ↑kd kd.prop hcd',
              rw [equiv.perm.disjoint_iff_disjoint_support, finset.disjoint_iff_ne] at this,
              specialize this (hh x) (hh_1' x c hc hxc) (hh y) (hh_1' y d hd hyd),
              exact this hxy, },
            have hyc : y ∈ c.support, { rw hcd, exact hyd, },
            rw [hh_1 x c hc hxc, hh_1 y c hc hyc, subtype.coe_inj,
              function.injective.eq_iff (equiv.injective _), subtype.mk_eq_mk] at hxy,
            exact hxy, },
          { -- hx mais pas hy
            rw [hh_2 y hy] at hxy,
            exfalso, apply hy,
            let hz1 := hh_1' x c hc hxc,
            rw hxy at hz1,
            use ↑(k ⟨c, hc⟩), use (k ⟨c, hc⟩).prop, exact hz1, }, },
        { by_cases hy : ∃ (d : equiv.perm α) (hc : d ∈ g.cycle_factors_finset), y ∈ d.support,
          { -- pas hx, mais hy
            obtain ⟨d, hd, hyd⟩ := hy,
            rw [hh_2 x hx] at hxy, exfalso, apply hx,
            let hz1 := hh_1' y d hd hyd, rw ← hxy at hz1,
            use ↑(k ⟨d, hd⟩), use (k ⟨d, hd⟩).prop, exact hz1, },
          { -- ni hx ni hy
            rw ← hh_2 x hx, rw ← hh_2 y hy, exact hxy, }, }, },
      let he :=  equiv.of_bijective hh hh_bij,
      use he,
      { -- he ∈ K
        simp only [K, mul_action.mem_stabilizer_iff],


        sorry },
      { -- to_perm he = k
        sorry, }, },
  },
  -- noyau : un groupe symétrique x produit de groupes cycliques
  have lemma_mem_ker : ∀ (z : equiv.perm α),
    conj_act.to_conj_act z ∈ subgroup.map K.subtype φ.ker ↔
      ∀ (t : equiv.perm α) (ht : t ∈ g.cycle_factors_finset), z * t = t * z,
  { intro z,
    split,
    { intro hz,
      rw subgroup.mem_map at hz,
      obtain ⟨⟨k, hkK⟩, hk, hk'⟩ := hz,
      simp only [monoid_hom.mem_ker] at hk,
      intros t ht,
      rw [← mul_inv_eq_iff_eq_mul, ← mul_aut.conj_apply, ← conj_act.of_conj_act_to_conj_act z,
        ← conj_act.smul_eq_mul_aut_conj _ t],
      rw ← hk',
      simp only [subgroup.coe_subtype, subgroup.coe_mk],
      simp only [← φ_eq k hkK t ht, hk],
      refl, },
    { intro H,
      rw subgroup.mem_map,
      use conj_act.to_conj_act z,
      { simp only [K],
        rw mul_action.mem_stabilizer_iff,
        rw conj_act.smul_eq_mul_aut_conj,
        rw mul_aut.conj_apply,
        rw mul_inv_eq_iff_eq_mul,
        rw conj_act.of_conj_act_to_conj_act,
        exact equiv.perm.commute_of_mem_cycles_factors_commute z g H, },
      simp only [monoid_hom.mem_ker],
      split,
      { ext ⟨c, hc⟩,
        rw φ_eq',
        rw H c hc,
        simp only [mul_inv_cancel_right, equiv.perm.coe_one, id.def, subtype.coe_mk], },
      { simp only [subgroup.coe_subtype, subgroup.coe_mk], }, }, },

  have lemma_ker : ∀ (z : equiv.perm α),
    conj_act.to_conj_act z ∈ subgroup.map K.subtype φ.ker ↔
    ∀ (s : equiv.perm α) (hs : s ∈ g.cycle_factors_finset),
    ∃ (hs' : ∀ (x : α), x ∈ s.support ↔ z x ∈ s.support),
      equiv.perm.subtype_perm z hs' ∈ subgroup.zpowers (equiv.perm.subtype_perm g
        (equiv.perm.mem_cycle_factors_finset_support g s hs)),
  { intro z,
    rw lemma_mem_ker,
    split,
    { intros H c hc,
      exact (equiv.perm.centralizer_mem_cycle_factors_iff g z c hc).mp (H c hc), },
    { intros H c hc,
      exact (equiv.perm.centralizer_mem_cycle_factors_iff g z c hc).mpr (H c hc), }, },

 --  have ψ : Π (c ∈ g.equiv.perm.cycle_factors_finset), subgroup.zpowers c → equiv.perm α,

sorry,
end
#check α × α
#check decidable.rec_on_true

def pi.comm_prod_map {ι : Type*} [fintype ι] (G : ι → Type*) [Π (i : ι), group (G i)]
  {H : Type*} [comm_group H] (φ : Π (i : ι), (G i →* H)) :
  (Π (i : ι), G i) →* H := {
to_fun    := λ g, finset.prod (finset.univ) (λ (i : ι), (φ i) (g i)),
map_one'  := by simp only [pi.one_apply, map_one, finset.prod_const_one],
map_mul'  := λ g h, begin simp only [pi.mul_apply, map_mul, finset.prod_mul_distrib], end, }

def pi.noncomm_prod_map {ι : Type*} [fintype ι] {G : ι → Type*} [Π (i : ι), group (G i)]
  {H : Type*} [group H] (φ : Π (i : ι), (G i →* H))
  (hφ : ∀ (g : Π i, G i) (i j : ι), commute ((φ i) (g i)) ((φ j) (g j)))
  (hφ' : ∀ (g h : Π i, G i) (i j : ι) (hij : i ≠ j), commute ((φ i) (h i)) ((φ j) (g j))):
  (Π (i : ι), G i) →* H := {
to_fun    := λ g, finset.noncomm_prod (finset.univ) (λ (i : ι), (φ i) (g i)) (λ i hi j hj, hφ g i j),
map_one'  := begin
  simp only [pi.one_apply, map_one],
  rw finset.noncomm_prod_eq_pow_card,
  exact one_pow _,
  { intros x _, refl, },
  end,
map_mul'  := λ g h,
begin
  rw ← finset.noncomm_prod_mul_distrib (λ (i : ι), (φ i) (g i)) (λ (i : ι), (φ i) (h i)) _ _ _,
  simp only [pi.mul_apply, map_mul],
  intros i _ j _ hij,
  exact hφ' g h i j hij,
end, }

lemma lemm_card_product (g : equiv.perm α) :
  fintype.card (Π (c ∈  g.cycle_factors_finset), subgroup.zpowers c) =
  finset.prod (g.cycle_factors_finset) (λ c : equiv.perm α, c.support.card) :=
begin
  rw fintype.card_pi,
  rw ← finset.union_compl (g.cycle_factors_finset),
  rw finset.prod_union _,
  rw ← mul_one (finset.prod (g.cycle_factors_finset) (λ c : equiv.perm α, c.support.card)),
  apply congr_arg2,
  { apply finset.prod_congr rfl,
    intros c hc,
    let e : (c ∈ g.cycle_factors_finset → (subgroup.zpowers c)) ≃ (subgroup.zpowers c) :=
    { to_fun := λ f, f hc,
      inv_fun := λ x, function.const _ x,
      left_inv := λ f, funext (λ hc', rfl),
      right_inv := λ x, by simp only, },
    rw fintype.card_congr e,
    rw ← order_eq_card_zpowers,
    apply equiv.perm.order_of_is_cycle,
    exact (equiv.perm.mem_cycle_factors_finset_iff.mp hc).1, },
  { rw ← finset.prod_const_one,
    apply finset.prod_congr rfl,
    intros c hc,
    simp at hc,
    rw fintype.card_eq_one_iff_nonempty_unique,
    have e : (c ∈ g.cycle_factors_finset → (subgroup.zpowers c)) :=
      λ h, false.rec ↥(subgroup.zpowers c) (hc h),
    use e,
    intro f, apply funext, intro h, exfalso, exact hc h, },
  { simp only [finset.disjoint_right, finset.mem_compl, imp_self, forall_const], },
end


example (c : equiv.perm α) (x : α) :
  x ∈ c.support ↔ c x ∈ c.support := equiv.perm.apply_mem_support.symm

/-  -- Should be useless
lemma equiv.perm.of_subtype_of_subtype_perm_of_support (c : equiv.perm α) :
  c.subtype_perm_of_support.of_subtype = c :=
begin
  ext x,
  by_cases hx : x ∈ c.support,
  { apply equiv.perm.of_subtype_apply_of_mem, exact hx, },
  { rw equiv.perm.of_subtype_apply_of_not_mem,
    rw [equiv.perm.mem_support, not_not] at hx, exact hx.symm,
    exact hx, },
end

lemma equiv.perm.subtype_perm_of_support_apply_of_mem (c : equiv.perm α)
  (x : α) (hx : x ∈ c.support) :
    (c.subtype_perm_of_support (⟨x, hx⟩ : c.support) : α) = c x :=
begin
  simp only [equiv.perm.subtype_perm_of_support],
  simp only [equiv.perm.apply_mem_support, imp_self, implies_true_iff, subtype.coe_mk,
    equiv.perm.subtype_perm_of_fintype_apply],
end

lemma equiv.perm.subtype_perm_of_support_apply_pow_of_mem (c : equiv.perm α)
  (x : α) (hx : x ∈ c.support) (n : ℕ) :
    (((c.subtype_perm_of_support) ^ n) (⟨x, hx⟩ : c.support) : α) = (c ^ n) x :=
begin
  simp only [equiv.perm.subtype_perm_of_support],
  induction n with n hrec,
  { -- zero case
    simp only [pow_zero, equiv.perm.coe_one, id.def, subtype.coe_mk], },
  { -- induction case
    simp only [pow_succ],
    simp only [equiv.perm.apply_mem_support, imp_self, implies_true_iff, equiv.perm.coe_mul,
      function.comp_app, equiv.perm.subtype_perm_of_fintype_apply, subtype.coe_mk,
      embedding_like.apply_eq_iff_eq],
    exact hrec, }
end

lemma equiv.perm.subtype_perm_of_support_apply_zpow_of_mem (c : equiv.perm α)
  (x : α) (hx : x ∈ c.support) (i : ℤ) :
    (((c.subtype_perm_of_support) ^ i) (⟨x, hx⟩ : c.support) : α) = (c ^ i) x :=
begin
  induction i,
  -- nat case
  apply equiv.perm.subtype_perm_of_support_apply_pow_of_mem,
  -- neg_succ case
  simp only [zpow_neg_succ_of_nat],
  apply equiv.injective (c ^ (i+1)),
  simp only [equiv.perm.apply_inv_self],
  rw ← equiv.perm.subtype_perm_of_support_apply_pow_of_mem,
  simp only [finset.mk_coe, equiv.perm.apply_inv_self, subtype.coe_mk],
  apply finset.coe_mem,
end

lemma equiv.perm.subtype_perm_of_support_support {c : equiv.perm α} :
  (c.subtype_perm_of_support).support = ⊤ :=
begin
  simp only [equiv.perm.subtype_perm_of_support],
  rw eq_top_iff,
  rintros ⟨x, hx⟩ _,
  rw equiv.perm.mem_support,
  intro hx_eq,
  rw ← subtype.coe_inj at hx_eq,
  simp only [equiv.perm.apply_mem_support, imp_self, implies_true_iff, subtype.coe_mk,
    equiv.perm.subtype_perm_of_fintype_apply] at hx_eq,
  rw equiv.perm.mem_support at hx,
  exact hx hx_eq,
end
-/

example (g : equiv.perm α) (hg : g.is_cycle) : g.support.nonempty :=
begin
sorry,
end

example (g : equiv.perm α) (s : finset α) (hs : ∀ (x : α), x ∈ s ↔ g x ∈ s) (i : ℤ) :
  ∀ (x : α), x ∈ s ↔ (g ^ i) x ∈ s :=
begin
  intro x,
  library_search,
sorry
end



example (s : finset α) : s → α := coe

example {α β : Type*} (a b : α) (e : α ≃ β) : a = b ↔ e a = e b :=
begin
  library_search,
end

#check equiv.perm.cycle_factors_finset_pairwise_disjoint,
example (f g : equiv.perm α) (hfg : disjoint f.support g.support) :
  commute f g :=
begin
end

example {G : Type*} [group G] (H : subgroup G) (K : subgroup H) : subgroup G :=
begin
  refine subgroup.map H.subtype K,
end

example (s t : finset α) (hst : s.card = t.card): (s ≃ t) :=
begin
  exact finset.equiv_of_card_eq hst,
end

example (s t : finset α) (hst : s ≃ t) : equiv.perm α :=
begin
  exact equiv.extend_subtype hst,
end

example {ι : Type*} (s : finset ι) (l : ι → equiv.perm α) : equiv.perm α :=
begin
  apply  finset.noncomm_prod s l _,

end


theorem equiv.perm_with_list_cycle_type_card (c : list ℕ)  :
  (equiv.perm_with_cycle_type α c).card
  * (fintype.card α - c.sum).factorial * c.prod
  * list.prod (list.map (λ n, (list.count n c).factorial) c.dedup)
  = if ((c.sum ≤ fintype.card α) ∧ (∀ a ∈ c, 2 ≤ a)) then (fintype.card α).factorial else 0 :=
begin
  split_ifs with hc hc,
  { -- nonempty case
    obtain ⟨g₀, hg₀⟩ := equiv.perm_with_cycle_type_nonempty_iff.mp hc,
    simp only [equiv.perm_with_cycle_type, set.to_finset_univ, finset.mem_filter,
      finset.mem_univ, true_and] at hg₀,
    have c_eq_orb : equiv.perm_with_cycle_type α c
      = (mul_action.orbit (conj_act (equiv.perm α)) g₀).to_finset,
    { ext g,
      simp only [equiv.perm_with_cycle_type],
      simp only [set.to_finset_univ, finset.mem_filter, finset.mem_univ,
        true_and, set.mem_to_finset],
      rw ← hg₀,
      rw ← equiv.perm.is_conj_iff_cycle_type_eq,
      rw mul_action.mem_orbit_iff,
      simp only [is_conj_iff],
      split,
      { rintro ⟨k, hk⟩,
        use conj_act.to_conj_act k⁻¹,
        rw ← hk,
        simp only [has_smul.smul],
        simp only [← mul_assoc, conj_act.of_conj_act_to_conj_act,
          mul_left_inv, one_mul, inv_inv, inv_mul_cancel_right], },
      { rintro ⟨x, hx⟩,
        use conj_act.of_conj_act x⁻¹,
        simp only [has_smul.smul] at hx,
        rw ← hx,
        simp only [← mul_assoc],
        simp only [conj_act.of_conj_act_inv, mul_left_inv,
          one_mul, inv_inv, inv_mul_cancel_right], }, },

    have c_eq_orb' : (equiv.perm_with_cycle_type α ↑c).card =
       fintype.card (mul_action.orbit (conj_act (equiv.perm α)) g₀),
    simp only [c_eq_orb, set.to_finset_card],
    rw c_eq_orb',
    simp only [mul_assoc],

    rw ← equiv.perm_conj_stabilizer_card g₀ c hg₀,

    rw mul_action.card_orbit_mul_card_stabilizer_eq_card_group,
    rw ← fintype.card_perm,
    rw conj_act.card, },
  { -- empty case
    suffices : (equiv.perm_with_cycle_type α c) = ∅,
    simp only [hc, this, finset.card_empty, zero_mul, if_false],
    rw ← finset.not_nonempty_iff_eq_empty ,
    intro h,
    rw ← equiv.perm_with_cycle_type_nonempty_iff at h,
    exact hc h, },
end

example (c : multiset ℕ) : c.to_list.prod = c.prod :=
by simp only [multiset.prod_to_list]

example {β : Type*} (c : list α) (f : α → β) :
  (multiset.map f ↑c) = list.map f c :=  by simp only [multiset.coe_map]

theorem equiv.perm_with_cycle_type_card (c : multiset ℕ)  :
  (equiv.perm_with_cycle_type α c).card
  * (fintype.card α - c.sum).factorial * c.prod
  * multiset.prod (multiset.map (λ n, (multiset.count n c).factorial) c.dedup)
  = if ((c.sum ≤ fintype.card α) ∧ (∀ a ∈ c, 2 ≤ a)) then (fintype.card α).factorial else 0 :=
begin
  rw ← multiset.coe_to_list c,
  convert equiv.perm_with_list_cycle_type_card c.to_list,
  simp only [multiset.coe_to_list, multiset.sum_to_list],
  simp only [multiset.coe_to_list, multiset.prod_to_list],
  { rw [multiset.coe_dedup, multiset.coe_map, multiset.coe_prod],
    apply congr_arg,
    apply congr_arg2 list.map rfl,
    refl, },
  simp only [multiset.coe_to_list, multiset.sum_to_list],
end

def S4 := equiv.perm (fin 4)
def A4 := alternating_group (fin 4)
def K4 := commutator A4

variable (α)
def equiv.perm_with_cycle_type_card_eq (c : multiset ℕ) :=
  if ((c.sum ≤ fintype.card α) ∧ (∀ a ∈ c, 2 ≤ a))
  then (fintype.card α).factorial / ((fintype.card α - c.sum).factorial * c.prod
      * multiset.prod (multiset.map (λ n, (multiset.count n c).factorial) c.dedup))
  else 0

#check equiv.perm_with_cycle_type_card_eq

#eval equiv.perm_with_cycle_type_card_eq (fin 9) {2,2}

/- N = nombre de 2-sylow de A4 :
 #A4 = 12
  N | 3
  N = 1 mod 2
  donc N = 1 ou 3
  il faudrait dire N = 1… -/
