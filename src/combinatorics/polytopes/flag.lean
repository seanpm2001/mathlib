/-
Copyright (c) 2021 Grayson Burton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Violeta Hernández Palacios.
-/
import tactic.wlog tactic.linarith order.zorn category_theory.conj data.fin.basic

/-!
# Flags of polytopes

In this file we define flags, which are maximal chains of a partial order. We prove that
automorphisms of posets induces a group action on flags. We also prove that flags contain elements
of each possible grade.
-/

open category_theory

universe u

/-- A flag is a maximal chain. -/
@[reducible] def polytope.flag (α : Type u) [has_le α] : Type u :=
{c : set α // @zorn.is_max_chain α (≤) c}

/-- The category of posets of type `α`. -/
@[instance]
private def Poset (α : Type u) [has_le α] : category (partial_order α) :=
{ hom  := λ a b, a.le →r b.le,
  id   := λ a, rel_hom.id a.le,
  comp := λ a b c hab hbc, rel_hom.comp hbc hab }

/-- The type of automorphisms of a poset. -/
def polytope.automorphism (α : Type u) [p : partial_order α] :=
@Aut (partial_order α) (Poset α) p

/-- One element covers another when there's no other element strictly in between. -/
def polytope.covers {α : Type u} [preorder α] (y x : α) : Prop :=
x < y ∧ ∀ z, ¬ z ∈ set.Ioo x y

notation x ` ⋗ `:50 y:50 := polytope.covers x y
notation x ` ⋖ `:50 y:50 := polytope.covers y x

/-- A graded order is an order homomorphism into ℕ such that:
    * `⊥` has grade 0
    * the homomorphism respects covering. -/
@[protect_proj]
class polytope.graded (α : Type u) [preorder α] extends order_bot α : Type u :=
(grade : α → ℕ)
(grade_bot : grade ⊥ = 0)
(strict_mono : strict_mono grade)
(hcovers : ∀ {x y}, x ⋖ y → grade y = grade x + 1)

/-- An abbreviation for the grade function of a graded order. -/
abbreviation polytope.grade {α : Type u} [preorder α] [polytope.graded α] : α → ℕ :=
polytope.graded.grade

/-- Grade is a relation homomorphism. -/
def polytope.graded.rel_hom (α : Type u) [preorder α] [bg : polytope.graded α] :
  @rel_hom α ℕ (<) (<) :=
⟨_, bg.strict_mono⟩

/-- If a natural covers another, it must be a successor. -/
lemma nat.succ_of_cover (m n : ℕ) : m ⋖ n → n = m + 1 := begin
  rintro ⟨hmnl, hmnr⟩,
  cases le_or_gt n (m + 1) with hnm hnm,
  exact antisymm hnm (nat.succ_le_of_lt hmnl),
  exact (hmnr _ ⟨lt_add_one m, hnm⟩).elim,
end

instance : polytope.graded ℕ :=
⟨id, rfl, strict_mono_id, nat.succ_of_cover⟩

/-- Two `fin`s cover each other iff their values do. -/
lemma fin.cover_iff_cover {n : ℕ} (a b : fin n) : a ⋖ b ↔ a.val ⋖ b.val :=
  ⟨ λ ⟨hl, hr⟩, ⟨hl, λ c hc, (hr ⟨c, lt_trans hc.right b.property⟩) hc⟩,
  λ ⟨hl, hr⟩, ⟨hl, λ c hc, hr c hc⟩ ⟩

instance (n : ℕ) : polytope.graded (fin (n + 1)) :=
{ grade := λ n, n,
  grade_bot := refl _,
  strict_mono := strict_mono_id,
  hcovers := begin
    intros x y,
    rw fin.cover_iff_cover,
    exact nat.succ_of_cover _ _,
  end }

open polytope

namespace polytope.flag

instance (α : Type u) [has_le α] : has_mem α (flag α) :=
⟨λ a Φ, a ∈ Φ.val⟩

variables {α : Type u}

instance [has_le α] (Φ : flag α) : has_le Φ :=
⟨λ a b, a.val ≤ b.val⟩

instance [has_le α] [has_lt α] (Φ : flag α) : has_lt Φ :=
⟨λ a b, a.val < b.val⟩

instance [has_le α] : inhabited (flag α) :=
⟨⟨_, zorn.max_chain_spec⟩⟩

/-- Any two elements of a flag are comparable. -/
protected theorem le_total [preorder α] : ∀ (Φ : flag α) (x y : Φ), x ≤ y ∨ y ≤ x :=
begin
  rintros ⟨_, hΦ, _⟩ x y,
  by_cases heq : x = y,
    { exact or.inl (le_of_eq heq) },
    { cases x with x hx, cases y with y hy,
      rw subtype.mk_eq_mk at heq,
      exact hΦ x hx y hy heq }
end

/-- `<` is trichotomous for partially ordered flags. -/
instance [partial_order α] (Φ : flag α) : is_trichotomous Φ (<) :=
begin
  refine ⟨λ x y, _⟩,
  by_cases heq : x = y, { exact or.inr (or.inl heq) },
  simp_rw lt_iff_le_and_ne,
  cases Φ.le_total x y with hle hle,
    { exact or.inl ⟨hle, heq⟩ },
    { exact or.inr (or.inr ⟨hle, ne.symm heq⟩) },
end

@[priority 900] -- lower priority in case subtype.linear_order comes up with something computable
noncomputable instance [partial_order α] (Φ : flag α) : linear_order Φ :=
{ le_total := Φ.le_total,
  decidable_le := classical.dec_rel (≤),
  ..subtype.partial_order _ }

/-- An element belongs to a flag iff it's comparable with everything in it. -/
lemma mem_flag_iff_comp [preorder α] (Φ : flag α) {a : α} : a ∈ Φ ↔ ∀ b : Φ, a ≤ ↑b ∨ ↑b ≤ a :=
begin
  refine ⟨λ ha _, Φ.le_total ⟨a, ha⟩ _, λ H, _⟩,
  by_contra,
  exact Φ.prop.right ⟨_, zorn.chain_insert Φ.prop.left (λ _ hΦ _, H ⟨_, hΦ⟩), set.ssubset_insert h⟩
end

/-- `⊥` belongs to every flag. -/
theorem bot_in_flag [preorder α] [order_bot α] (Φ : flag α) : (⊥ : α) ∈ Φ :=
Φ.mem_flag_iff_comp.mpr $ λ _, or.inl bot_le

instance [preorder α] [order_bot α] (Φ : flag α) : order_bot Φ :=
subtype.order_bot Φ.bot_in_flag

/-- `⊤` belongs to every flag. -/
theorem top_in_flag [preorder α] [order_top α] (Φ : flag α) : (⊤ : α) ∈ Φ :=
Φ.mem_flag_iff_comp.mpr $ λ _, or.inr le_top

instance [preorder α] [order_top α] (Φ : flag α) : order_top Φ :=
subtype.order_top Φ.top_in_flag

instance [preorder α] [bounded_order α] (Φ : flag α) : bounded_order Φ :=
{ ..Φ.order_top, ..Φ.order_bot }

end polytope.flag

namespace polytope.automorphism

/-- The automorphism group of a poset. -/
instance (α : Type u) [p : partial_order α] : group (automorphism α) :=
@Aut.group (partial_order α) (Poset α) p

variables {α : Type u} [partial_order α]

/-- Any automorphism is a relation isomorphism. -/
def to_rel_iso (γ : automorphism α) : ((≤) : α → α → Prop) ≃r (≤) :=
{ to_fun := γ.hom,
  inv_fun := γ.inv,
  left_inv := λ x, by change (γ.hom ≫ _) _ = _; rw γ.hom_inv_id; refl,
  right_inv := λ x, by change (γ.inv ≫ _) _ = _; rw γ.inv_hom_id; refl,
  map_rel_iff' := begin
    intros,
    change γ.hom a ≤ γ.hom b ↔ a ≤ b,
    refine ⟨λ h, _, λ h, γ.hom.map_rel h⟩,
    have : (γ.hom ≫ γ.inv) a ≤ (γ.hom ≫ γ.inv) b := γ.inv.map_rel h,
    rwa γ.hom_inv_id at this
  end }

/-- Automorphisms preserve `≤`. -/
@[simp]
lemma hom_map_le (γ : automorphism α) (a b : α) : γ.hom a ≤ γ.hom b ↔ a ≤ b :=
γ.to_rel_iso.map_rel_iff

/-- Automorphisms preserve `=`. -/
@[simp]
lemma hom_map_eq (γ : automorphism α) (a b : α) : γ.hom a = γ.hom b ↔ a = b :=
γ.to_rel_iso.eq_iff_eq

/-- Automorphisms preserve `≠`. -/
lemma hom_map_ne (γ : automorphism α) (a b : α) : γ.hom a ≠ γ.hom b ↔ a ≠ b :=
by simp only [ne.def, hom_map_eq]

/-- Automorphisms and their inverses give the identity. -/
@[simp]
lemma hom_inv (γ : automorphism α) (a : α) : γ.hom (γ.inv a) = a :=
γ.to_rel_iso.right_inv a

/-- Inverse automorphisms preserve `≤`. -/
@[simp]
lemma inv_map_le (γ : automorphism α) (a b : α) : γ.inv a ≤ γ.inv b ↔ a ≤ b :=
γ.to_rel_iso.symm.map_rel_iff

/-- Inverse automorphisms preserve `=`. -/
@[simp]
lemma inv_map_eq (γ : automorphism α) (a b : α) : γ.inv a = γ.inv b ↔ a = b :=
γ.to_rel_iso.symm.eq_iff_eq

/-- Inverse automorphisms preserve `≠`. -/
lemma inv_map_ne (γ : automorphism α) (a b : α) : γ.inv a ≠ γ.inv b ↔ a ≠ b :=
by simp only [ne.def, inv_map_eq]

/-- Automorphisms and their inverses give the identity. -/
@[simp]
lemma inv_hom (γ : automorphism α) (a : α) : γ.inv (γ.hom a) = a :=
γ.to_rel_iso.left_inv a

/-- Scalar multiplication of automorphisms by flags. -/
@[reducible]
def smul_def (γ : automorphism α) (Φ : flag α) : set α :=
γ.hom '' Φ.val

/-- Definition of scalar multiplication of automorphisms by flags. -/
@[simp]
theorem smul_def.eq (γ : automorphism α) (Φ : flag α) : γ.smul_def Φ = γ.hom '' Φ.val :=
rfl

/-- Automorphisms map flags to chains. -/
lemma smul_is_chain (γ : automorphism α) (Φ : flag α) : zorn.chain (≤) (γ.smul_def Φ) :=
begin
  rcases Φ with ⟨Φf, hΦ, hΦ'⟩,
  rintros a ⟨aw, ha, ha'⟩ b ⟨bw, hb, hb'⟩,
  induction ha', induction hb',
  simp only [hom_map_le, hom_map_ne],
  exact hΦ _ ha _ hb
end

/-- Automorphisms map flags to flags. -/
theorem smul_is_max_chain (γ : automorphism α) (Φ : flag α) :
  @zorn.is_max_chain _ (≤) (γ.smul_def Φ) :=
begin
  refine ⟨γ.smul_is_chain Φ, _⟩,
  rcases Φ with ⟨Φf, hΦ, hΦ'⟩,
  rintros ⟨w, hwl, hwr⟩,
  rcases set.exists_of_ssubset hwr with ⟨a, ha, hna⟩,
  refine hΦ' ⟨set.insert (γ.inv a) Φf, _⟩,
  split,
    { rintros x (hx : _ ∨ _) y (hy : _ ∨ _) hne,
      have hxyne : x ≠ γ.inv a ∨ y ≠ γ.inv a,
        { rw ←not_and_distrib,
          rintro ⟨hl, hr⟩,
          exact hne (hl.trans hr.symm) },
      by_cases hxy : x ∈ Φf ∧ y ∈ Φf, { exact hΦ _ hxy.left _ hxy.right hne },
      wlog h : x = γ.inv a ∧ y ∈ Φf using [x y, y x],
        { cases hx,
            { exact or.inl ⟨hx, hy.resolve_left (hxyne.resolve_left $ not_not_intro hx)⟩ },
          cases hy,
            { exact or.inr ⟨hy, hx⟩ },
            { exact (hxy ⟨hx, hy⟩).elim } },
      cases h with hx' hy',
      replace hx' := hx'.symm,
      induction hx',
      rw [←γ.hom_map_le y, ←γ.hom_map_le, γ.hom_inv],
      replace hne : a ≠ γ.hom y := by rw ←γ.inv_map_ne; simpa,
      apply hwl _ ha _ _ hne,
      replace hy' := set.mem_image_of_mem γ.hom hy',
      exact hwr.left hy' },
    { apply set.ssubset_insert,
      intro h,
      replace h := set.mem_image_of_mem γ.hom h,
      rw γ.hom_inv at h,
      exact hna h },
end

instance : has_scalar (automorphism α) (flag α) :=
⟨λ γ Φ, ⟨γ.smul_def Φ, γ.smul_is_max_chain Φ⟩⟩

@[reducible, simp]
theorem smul_def.eq' (γ : automorphism α) (Φ : flag α) : (γ • Φ).val = γ.hom '' Φ.val :=
rfl

/-- The group action of the automorphism group of a poset on its flags. -/
instance : mul_action (automorphism α) (flag α) :=
{ one_smul := λ ⟨b, _⟩, subtype.eq (set.image_id b),
  mul_smul := begin
    rintros γ γ' ⟨b, _⟩,
    apply subtype.eq,
    change (γ'.hom ≫ γ.hom) '' b = γ.hom '' (γ'.hom '' b),
    rw ←set.image_comp,
    refl
  end }

end polytope.automorphism

/-- Covering is irreflexive. -/
instance covers.is_irrefl {α : Type u} [preorder α] : is_irrefl α covers :=
⟨ λ _ ha, ne_of_lt ha.left (refl _) ⟩

/-- A natural covers another iff it's a successor. -/
lemma nat.cover_iff_succ (m n : ℕ) : m ⋖ n ↔ n = m + 1 :=
begin
  split, {
    rintro ⟨hmnl, hmnr⟩,
    cases le_or_gt n (m + 1) with hnm hnm,
    exact antisymm hnm (nat.succ_le_of_lt hmnl),
    exact (hmnr _ ⟨lt_add_one m, hnm⟩).elim,
  },
  intro hnm,
  split, {
    rw hnm,
    exact lt_add_one m,
  },
  rintros r ⟨hrl, hrr⟩,
  rw hnm at hrr,
  exact nat.lt_irrefl _ (lt_of_le_of_lt (nat.succ_le_of_lt hrl) hrr),
end

namespace graded

/-- An abbreviation for the grade of `⊤`. -/
abbreviation grade_top (α : Type u) [preorder α] [order_top α] [graded α] : ℕ :=
grade (⊤ : α)

lemma grade_le_grade_top {α : Type u} [partial_order α] [order_top α] [graded α] (a : α) :
  grade a ≤ grade_top α :=
graded.strict_mono.monotone le_top

lemma dual_cover_iff_cover {α : Type u} [preorder α] [order_top α] [graded α] (a b : α) :
  a ⋖ b ↔ @polytope.covers (order_dual α) _ a b :=
by split; repeat { exact λ ⟨habl, habr⟩, ⟨habl, λ c ⟨hcl, hcr⟩, habr c ⟨hcr, hcl⟩⟩ }

instance (α : Type u) [partial_order α] [order_top α] [graded α] : graded (order_dual α) :=
{ grade := λ a : α, grade_top α - grade a,
  grade_bot := nat.sub_self _,
  strict_mono := begin
    refine λ (a b : α) hab, _,
    have : grade a > grade b := graded.strict_mono hab,
    have := grade_le_grade_top a,
    have := grade_le_grade_top b,
    linarith,
  end,
  hcovers := begin
    refine λ (x y : α) hxy, _,
    change grade x with graded.grade x,
    rw ←dual_cover_iff_cover at hxy,
    rw [graded.hcovers hxy, ←nat.sub_sub,
        nat.sub_add_cancel (tsub_pos_of_lt (graded.strict_mono (lt_of_lt_of_le hxy.left le_top)))]
  end }

/-- `grade` is injective for linearly ordered `α`. -/
theorem grade.inj (α : Type u) [linear_order α] [graded α] : function.injective (grade : α → ℕ) :=
graded.strict_mono.injective

variables {α : Type u}

/-- An element has grade 0 iff it is the bottom element. -/
@[simp]
theorem eq_zero_iff_eq_bot [partial_order α] [graded α] (x : α) : grade x = 0 ↔ x = ⊥ :=
begin
  refine ⟨λ h, _, λ h, by cases h; exact graded.grade_bot⟩,
  rw ←@graded.grade_bot α at h,
  by_contra hx,
  change _ ≠ _ at hx,
  rw ←bot_lt_iff_ne_bot at hx,
  exact not_le_of_lt (graded.strict_mono hx) (le_of_eq h)
end

/-- An element has the top grade iff it is the top element. -/
@[simp]
theorem eq_grade_top_iff_eq_top [partial_order α] [order_top α] [graded α] (x : α) :
  grade x = grade_top α ↔ x = ⊤ :=
begin
  refine ⟨λ h, _, λ h, by cases h; refl⟩,
  by_contra hx,
  change _ ≠ _ at hx,
  rw ←lt_top_iff_ne_top at hx,
  exact not_le_of_lt (graded.strict_mono hx) (ge_of_eq h)
end

section
variables [linear_order α] [graded α]

lemma grade_le_iff_le (x y : α) : grade x ≤ grade y ↔ x ≤ y :=
begin
  split,
    { contrapose,
      exact λ hxy, not_le_of_gt (graded.strict_mono (lt_of_not_ge hxy)), },
  exact λ hxy, graded.strict_mono.monotone hxy,
end

/-- `grade` is an order embedding into ℕ for linearly ordered `α`. -/
def oem_nat : α ↪o ℕ :=
{ to_fun := _,
  inj' := grade.inj α,
  map_rel_iff' := grade_le_iff_le }

lemma grade_lt_iff_lt (x y : α) : grade x < grade y ↔ x < y :=
order_embedding.lt_iff_lt oem_nat

lemma grade_eq_iff_eq (x y : α) : grade x = grade y ↔ x = y :=
order_embedding.eq_iff_eq oem_nat

lemma grade_ne_iff_ne (x y : α) : grade x ≠ grade y ↔ x ≠ y :=
not_congr (grade_eq_iff_eq x y)

/-- A grade function into `fin` for `α` with a top element. -/
def grade_fin [order_top α] (x : α) : fin (grade_top α + 1) :=
⟨grade x, by rw nat.lt_add_one_iff; exact grade_le_grade_top _⟩

@[simp]
theorem grade_fin.val_eq [order_top α] (x : α) : (grade_fin x).val = grade x :=
rfl

theorem grade_fin.strict_mono [order_top α] : strict_mono (grade_fin : α → fin (grade_top α + 1)) :=
graded.strict_mono

theorem grade_fin.inj [order_top α] : function.injective (grade_fin : α → fin (grade_top α + 1)) :=
grade_fin.strict_mono.injective

/-- `grade_fin` is an order embedding into `fin` for linearly ordered `α` with a top element. -/
def oem_fin [order_top α] : α ↪o fin (grade_top α + 1) :=
{ to_fun := grade_fin,
  inj' := grade_fin.inj,
  map_rel_iff' := grade_le_iff_le }

/-- In linear orders, `hcovers` is an equivalence. -/
lemma hcovers_iff_grade_eq_succ_grade (a b : α) : a ⋖ b ↔ grade b = grade a + 1 :=
begin
  refine ⟨graded.hcovers, λ hba, _⟩,
  have := nat.lt_of_succ_le (le_of_eq hba.symm),
  rw graded.grade_lt_iff_lt at this,
  refine ⟨this, λ z, _⟩,
  rintros ⟨hzl, hzr⟩,
  rw ←nat.cover_iff_succ at hba,
  rw ←graded.grade_lt_iff_lt at hzl,
  rw ←graded.grade_lt_iff_lt at hzr,
  exact hba.right _ ⟨hzl, hzr⟩,
end

/-- Two elements in a linear order cover each other iff their grades do. -/
theorem cover_iff_nat_cover (a b : α) : a ⋖ b ↔ grade a ⋖ grade b :=
begin
  split, { rw nat.cover_iff_succ, exact graded.hcovers },
  intro hab,
  rw nat.cover_iff_succ at hab,
  rwa graded.hcovers_iff_grade_eq_succ_grade
end

end
end graded

theorem set.Ioo_is_empty_of_covers {α : Type u} [preorder α] {x y : α} : x ⋖ y → set.Ioo x y = ∅ :=
λ ⟨_, hr⟩, set.eq_empty_iff_forall_not_mem.mpr hr

namespace flag

/-- A point subdivides an interval into three. -/
private lemma ioo_tricho {a b c : ℕ} (hc : c ∈ set.Ioo a b) (d: ℕ) : c = d ∨ c ∈ set.Ioo a d ∨ c ∈ set.Ioo d b :=
begin
  cases eq_or_ne c d with hcd hcd,
    { exact or.inl hcd },
  cases ne.lt_or_lt hcd with ha hb,
    { exact or.inr (or.inl ⟨and.left hc, ha⟩) },
    { exact or.inr (or.inr ⟨hb, and.right hc⟩) }
end

/-- A set of nats without gaps is an interval. The sizes of the gaps and intervals we consider are
    bounded by `n`, so that we may induct on it. -/
private lemma all_ioo_of_ex_ioo {P : ℕ → Prop} (n : ℕ)
  (hP : ∀ a b, b ≤ a + n → P a → P b → nonempty (set.Ioo a b) → ∃ c ∈ set.Ioo a b, P c) (a b : ℕ) :
  b ≤ a + n → P a → P b → ∀ c ∈ set.Ioo a b, P c :=
begin
  revert a b,
  induction n with n hP',
    { exact λ _ _ hba _ _ _ hci, ((not_lt_of_ge hba) (lt_trans hci.left hci.right)).elim },
  intros a b hba ha hb _ hci,
  rcases hP a b hba ha hb (nonempty.intro ⟨_, hci⟩) with ⟨d, ⟨hdil, hdir⟩, hd⟩,
  cases ioo_tricho hci d with hcd hdb, { rwa ←hcd at hd },
  have hxy : ∃ x y, P x ∧ P y ∧ c ∈ set.Ioo x y ∧ y ≤ x + n := begin
    cases hdb with hcad hcdb,
      { refine ⟨a, d, ha, hd, hcad, _⟩,
        have := lt_of_lt_of_le hdir hba,
        rw nat.add_succ at this,
        exact nat.le_of_lt_succ this },
      { refine ⟨d, b, hd, hb, hcdb, _⟩,
        have := nat.add_le_add hdil rfl.le,
        rw nat.succ_add a n at this,
        exact le_trans hba this }
  end,
  rcases hxy with ⟨x, y, hx, hy, hxy, hyx⟩,
  refine hP' (λ _ _ hba, _) x y hyx hx hy c hxy,
  exact hP _ _ (hba.trans (nat.le_succ _)),
end

/-- A set of nats without gaps is an interval. -/
lemma all_icc_of_ex_ioo {P : ℕ → Prop}
  (hP : ∀ a b, P a → P b → (nonempty (set.Ioo a b)) → ∃ c ∈ set.Ioo a b, P c) (a b : ℕ) :
  P a → P b → ∀ c ∈ set.Icc a b, P c :=
begin
  rintros ha hb c ⟨hac, hcb⟩,
  cases eq_or_lt_of_le hac with hac hac,
    { rwa ←hac },
  cases eq_or_lt_of_le hcb with hcb hcb,
    { rwa  hcb },
  exact all_ioo_of_ex_ioo b (λ c d _, hP c d) _ _ le_add_self ha hb _ ⟨hac, hcb⟩
end

variables {α : Type u} [partial_order α]

/-- An element covers another iff they do so in the flag. -/
@[simp]
theorem cover_iff_flag_cover {Φ : flag α} (x y : Φ) : x ⋖ y ↔ x.val ⋖ y.val :=
begin
  refine ⟨λ h, ⟨h.left, λ z hzi, _⟩, λ ⟨hxy, hz⟩, ⟨hxy, λ _, hz _⟩⟩,
  cases h with hxy h,
  refine h ⟨z, _⟩ hzi,
  cases hzi with hxz hzy,
  refine Φ.mem_flag_iff_comp.mpr (λ w, _),
  have hwi := h w,
  simp only [set.mem_Ioo, not_and, not_lt] at hwi,
  rcases lt_trichotomy x w with hxw | hxw | hxw,
    { exact or.inl (le_of_lt $ lt_of_lt_of_le hzy (hwi hxw)) },
    { induction hxw, exact or.inr (le_of_lt hxz) },
    { exact or.inr (le_of_lt $ lt_trans hxw hxz) }
end

variable [graded α]

instance (Φ : flag α) : graded Φ :=
{ grade := λ a, grade a.val,
  grade_bot := graded.grade_bot,
  strict_mono := λ _ _ h, graded.strict_mono h,
  hcovers := λ _ _ hcov, graded.hcovers $ (cover_iff_flag_cover _ _).mp hcov }

/-- A number is a grade of some element in a flag. -/
private abbreviation is_grade (Φ : flag α) (n : ℕ) : Prop :=
∃ a : Φ, grade a = n

/-- If `x < y` but `y` does not cover `x`, then there's an element in between. -/
private lemma between_of_ncover {x y : α} (hnxy : ¬x ⋖ y) (hxy : x < y) :
  ∃ z, x < z ∧ z < y :=
by by_contra hne; push_neg at hne; exact hnxy ⟨hxy, λ z ⟨hl, hr⟩, hne z hl hr⟩

/-- The set of grades in a flag has no gaps. -/
lemma grade_ioo (Φ : flag α) (m n : ℕ) :
  is_grade Φ m → is_grade Φ n → nonempty (set.Ioo m n) → ∃ r ∈ set.Ioo m n, is_grade Φ r :=
begin
  rintros ⟨a, ham⟩ ⟨b, hbn⟩ ⟨r, hr⟩,

  have hnab : ¬a ⋖ b := begin
    have : ¬m ⋖ n := λ hmn, (hmn.right r) hr,
    rwa [←ham, ←hbn, ←graded.cover_iff_nat_cover] at this,
  end,

  have hab : a < b := begin
    rw [←graded.grade_lt_iff_lt, ham, hbn],
    exact lt_trans hr.left hr.right,
  end,

  rcases between_of_ncover hnab hab with ⟨c, hac, hcb⟩,
  refine ⟨grade c, ⟨_, ⟨c, rfl⟩⟩⟩,
  split,
    { rw ←ham,
      exact graded.strict_mono hac },
  rw ←hbn,
  exact graded.strict_mono hcb
end

/-- If a flag contains two elements, it contains elements with all grades in between. -/
private lemma flag_grade_aux {Φ : flag α} (a b : Φ) (j ∈ set.Icc (grade a) (grade b)) :
  ∃ c : Φ, grade c = j :=
(all_icc_of_ex_ioo (grade_ioo Φ)) (grade a) (grade b) ⟨a, rfl⟩ ⟨b, rfl⟩ j H

variables [order_top α] (j : fin (graded.grade_top α + 1)) (Φ : flag α)

/-- A flag has an element of grade `j` when `j ≤ grade ⊤`. -/
theorem ex_of_grade_in_flag : ∃ a : Φ, grade a = j :=
begin
  refine (flag_grade_aux ⊥ ⊤ j) ⟨_, nat.le_of_lt_succ j.property⟩,
  have : grade (⊥ : Φ) = 0 := graded.grade_bot,
  rw this,
  exact zero_le j,
end

/-- A flag has a unique element of grade `j` when `j ≤ grade ⊤`. -/
theorem ex_unique_of_grade_in_flag : ∃! a : Φ, grade a = j :=
begin
  cases ex_of_grade_in_flag j Φ with a ha,
  use [a, ha],
  intros b hb,
  apply graded.grade.inj _,
  rw [ha, hb],
end

/-- The element of a certain grade in a flag. -/
noncomputable def flag_idx : Φ :=
classical.some (ex_of_grade_in_flag j Φ)

/-- The defining property of `flag_idx`. -/
@[simp]
theorem grade_flag_idx : grade (flag_idx j Φ) = j :=
classical.some_spec (ex_of_grade_in_flag j Φ)

/-- `flag_idx j Φ` is the unique element of grade `j` in the flag. -/
theorem grade_eq_iff_flag_idx (a : Φ) : grade a = j ↔ a = flag_idx j Φ :=
begin
  have idx := grade_flag_idx j Φ,
  split, {
    intro ha,
    rcases ex_unique_of_grade_in_flag j Φ with ⟨_, _, h⟩,
    rw [(h _ ha), (h _ idx)],
  },
  intro h,
  rw h,
  exact idx,
end

variables (Ψ : flag α)

/-- Two flags are j-adjacent iff they share all but their j-th element. Note that a flag is never
    adjacent to itself. -/
def flag_adj : Prop :=
∀ i, (flag_idx i Φ).val = (flag_idx i Ψ).val ↔ i ≠ j

instance : is_irrefl (flag α) (flag_adj j) :=
⟨λ _ h, (h j).mp rfl rfl⟩

theorem flag_adj.symm : flag_adj j Φ Ψ → flag_adj j Ψ Φ :=
by intros h i; rw ←(h i); exact eq_comm

end flag
