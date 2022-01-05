/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/

import control.functor.multivariate
import data.pfunctor.multivariate.basic
import data.pfunctor.multivariate.M
import data.qpf.multivariate.basic

/-!
# The final co-algebra of a multivariate qpf is again a qpf.

For a `(n+1)`-ary QPF `F (α₀,..,αₙ)`, we take the least fixed point of `F` with
regards to its last argument `αₙ`. The result is a `n`-ary functor: `fix F (α₀,..,αₙ₋₁)`.
Making `fix F` into a functor allows us to take the fixed point, compose with other functors
and take a fixed point again.

## Main definitions

 * `cofix.mk`     - constructor
 * `cofix.dest    - destructor
 * `cofix.corec`  - corecursor: useful for formulating infinite, productive computations
 * `cofix.bisim`  - bisimulation: proof technique to show the equality of possibly infinite values
                    of `cofix F α`

## Implementation notes

For `F` a QPF`, we define `cofix F α` in terms of the M-type of the polynomial functor `P` of `F`.
We define the relation `Mcongr` and take its quotient as the definition of `cofix F α`.

`Mcongr` is taken as the weakest bisimulation on M-type.  See
[avigad-carneiro-hudon2019] for more details.

## Reference

 * Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
   [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

universe u
open_locale mvfunctor

namespace mvqpf
open typevec mvpfunctor
open mvfunctor (liftp liftr)

variables {n : ℕ} {F : typevec.{u} (n+1) → Type u} [mvfunctor F] [q : mvqpf F]
include q

/-- `corecF` is used as a basis for defining the corecursor of `cofix F α`. `corecF`
uses corecursion to construct the M-type generated by `q.P` and uses function on `F`
as a corecursive step -/
def corecF {α : typevec n} {β : Type*} (g : β → F (α.append1 β)) : β → q.P.M α :=
M.corec _ (λ x, repr (g x))

theorem corecF_eq {α : typevec n} {β : Type*} (g : β → F (α.append1 β)) (x : β) :
  M.dest q.P (corecF g x) = append_fun id (corecF g) <$$> repr (g x) :=
by rw [corecF, M.dest_corec]

/-- Characterization of desirable equivalence relations on M-types -/
def is_precongr {α : typevec n} (r : q.P.M α → q.P.M α → Prop) : Prop :=
  ∀ ⦃x y⦄, r x y →
    abs (append_fun id (quot.mk r) <$$> M.dest q.P x) =
      abs (append_fun id (quot.mk r) <$$> M.dest q.P y)

/-- Equivalence relation on M-types representing a value of type `cofix F` -/
def Mcongr {α : typevec n} (x y : q.P.M α) : Prop :=
∃ r, is_precongr r ∧ r x y

/-- Greatest fixed point of functor F. The result is a functor with one fewer parameters
than the input. For `F a b c` a ternary functor, fix F is a binary functor such that

```lean
cofix F a b = F a b (cofix F a b)
```
-/
def cofix (F : typevec (n + 1) → Type u) [mvfunctor F] [q : mvqpf F] (α : typevec n) :=
quot (@Mcongr _ F _ q α)

instance {α : typevec n} [inhabited q.P.A] [Π (i : fin2 n), inhabited (α i)] :
  inhabited (cofix F α) := ⟨ quot.mk _ (default _) ⟩

/-- maps every element of the W type to a canonical representative -/
def Mrepr {α : typevec n} : q.P.M α → q.P.M α := corecF (abs ∘ M.dest q.P)

/-- the map function for the functor `cofix F` -/
def cofix.map {α β : typevec n} (g : α ⟹ β) : cofix F α → cofix F β :=
quot.lift (λ x : q.P.M α, quot.mk Mcongr (g <$$> x))
  begin
    rintros aa₁ aa₂ ⟨r, pr, ra₁a₂⟩, apply quot.sound,
    let r' := λ b₁ b₂, ∃ a₁ a₂ : q.P.M α, r a₁ a₂ ∧ b₁ = g <$$> a₁ ∧ b₂ = g <$$> a₂,
    use r', split,
    { show is_precongr r',
      rintros b₁ b₂ ⟨a₁, a₂, ra₁a₂, b₁eq, b₂eq⟩,
      let u : quot r → quot r' := quot.lift (λ x : q.P.M α, quot.mk r' (g <$$> x))
        (by { intros a₁ a₂ ra₁a₂, apply quot.sound, exact ⟨a₁, a₂, ra₁a₂, rfl, rfl⟩ }),
      have hu : (quot.mk r' ∘ λ x : q.P.M α, g <$$> x) = u ∘ quot.mk r,
        { ext x, refl },
      rw [b₁eq, b₂eq, M.dest_map, M.dest_map, ←q.P.comp_map, ←q.P.comp_map],
      rw [←append_fun_comp, id_comp, hu, hu, ←comp_id g, append_fun_comp],
      rw [q.P.comp_map, q.P.comp_map, abs_map, pr ra₁a₂, ←abs_map] },
    show r' (g <$$> aa₁) (g <$$> aa₂), from ⟨aa₁, aa₂, ra₁a₂, rfl, rfl⟩
  end

instance cofix.mvfunctor : mvfunctor (cofix F) :=
{ map := @cofix.map _ _ _ _}

/-- Corecursor for `cofix F` -/
def cofix.corec {α : typevec n} {β : Type u} (g : β → F (α.append1 β)) : β → cofix F α :=
λ x, quot.mk  _ (corecF g x)

/-- Destructor for `cofix F` -/
def cofix.dest {α : typevec n} : cofix F α → F (α.append1 (cofix F α)) :=
quot.lift
  (λ x, append_fun id (quot.mk Mcongr) <$$> (abs (M.dest q.P x)))
  begin
    rintros x y ⟨r, pr, rxy⟩, dsimp,
    have : ∀ x y, r x y → Mcongr x y,
    { intros x y h, exact ⟨r, pr, h⟩ },
    rw [←quot.factor_mk_eq _ _ this], dsimp,
    conv { to_lhs,
      rw [append_fun_comp_id, comp_map, ←abs_map, pr rxy, abs_map, ←comp_map,
        ←append_fun_comp_id] }
  end

/-- Abstraction function for `cofix F α` -/
def cofix.abs {α} : q.P.M α → cofix F α :=
quot.mk _

/-- Representation function for `cofix F α` -/
def cofix.repr {α} : cofix F α → q.P.M α :=
M.corec _ $ repr ∘ cofix.dest

/-- Corecursor for `cofix F` -/
def cofix.corec'₁ {α : typevec n} {β : Type u}
  (g : Π {X}, (β → X) → F (α.append1 X)) (x : β) : cofix F α :=
cofix.corec (λ x, g id) x

/-- More flexible corecursor for `cofix F`. Allows the return of a fully formed
value instead of making a recursive call -/
def cofix.corec' {α : typevec n} {β : Type u} (g : β → F (α.append1 (cofix F α ⊕ β))) (x : β) :
  cofix F α :=
let f : α ::: cofix F α ⟹ α ::: (cofix F α ⊕ β) := id ::: sum.inl in
cofix.corec
(sum.elim (mvfunctor.map f ∘ cofix.dest) g)
(sum.inr x : cofix F α ⊕ β)

/-- Corecursor for `cofix F`. The shape allows recursive calls to
look like recursive calls. -/
def cofix.corec₁ {α : typevec n} {β : Type u}
  (g : Π {X}, (cofix F α → X) → (β → X) → β → F (α ::: X)) (x : β) : cofix F α :=
cofix.corec' (λ x, g sum.inl sum.inr x) x

theorem cofix.dest_corec {α : typevec n} {β : Type u} (g : β → F (α.append1 β)) (x : β) :
  cofix.dest (cofix.corec g x) = append_fun id (cofix.corec g) <$$> g x :=
begin
  conv { to_lhs, rw [cofix.dest, cofix.corec] }, dsimp,
  rw [corecF_eq, abs_map, abs_repr, ←comp_map, ←append_fun_comp], reflexivity
end

/-- constructor for `cofix F` -/
def cofix.mk {α : typevec n} : F (α.append1 $ cofix F α) → cofix F α :=
cofix.corec (λ x, append_fun id (λ i : cofix F α, cofix.dest.{u} i) <$$> x)

/-!
## Bisimulation principles for `cofix F`

The following theorems are bisimulation principles. The general idea
is to use a bisimulation relation to prove the equality between
specific values of type `cofix F α`.

A bisimulation relation `R` for values `x y : cofix F α`:

 * holds for `x y`: `R x y`
 * for any values `x y` that satisfy `R`, their root has the same shape
   and their children can be paired in such a way that they satisfy `R`.

-/

private theorem cofix.bisim_aux {α : typevec n}
    (r : cofix F α → cofix F α → Prop)
    (h' : ∀ x, r x x)
    (h : ∀ x y, r x y →
      append_fun id (quot.mk r) <$$> cofix.dest x = append_fun id (quot.mk r) <$$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
begin
  intro x, apply quot.induction_on x, clear x,
  intros x y, apply quot.induction_on y, clear y,
  intros y rxy,
  apply quot.sound,
  let r' := λ x y, r (quot.mk _ x) (quot.mk _ y),
  have : is_precongr r',
  { intros a b r'ab,
      have  h₀ :
          append_fun id (quot.mk r ∘ quot.mk Mcongr) <$$> abs (M.dest q.P a) =
          append_fun id (quot.mk r ∘ quot.mk Mcongr) <$$> abs (M.dest q.P b) :=
        by rw [append_fun_comp_id, comp_map, comp_map]; exact h _ _ r'ab,
    have h₁ : ∀ u v : q.P.M α, Mcongr u v → quot.mk r' u = quot.mk r' v,
    { intros u v cuv, apply quot.sound, dsimp [r'], rw quot.sound cuv, apply h' },
    let f : quot r → quot r' := quot.lift (quot.lift (quot.mk r') h₁)
      begin
        intro c, apply quot.induction_on c, clear c,
        intros c d, apply quot.induction_on d, clear d,
        intros d rcd, apply quot.sound, apply rcd
      end,
    have : f ∘ quot.mk r ∘ quot.mk Mcongr = quot.mk r' := rfl,
    rw [←this, append_fun_comp_id, q.P.comp_map, q.P.comp_map, abs_map, abs_map, abs_map,
         abs_map, h₀] },
  refine ⟨r', this, rxy⟩
end

/-- Bisimulation principle using `map` and `quot.mk` to match and relate children of two trees. -/
theorem cofix.bisim_rel {α : typevec n}
    (r : cofix F α → cofix F α → Prop)
    (h : ∀ x y, r x y →
      append_fun id (quot.mk r) <$$> cofix.dest x = append_fun id (quot.mk r) <$$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
let r' x y := x = y ∨ r x y in
begin
  intros x y rxy,
  apply cofix.bisim_aux r',
  { intro x, left, reflexivity },
  { intros x y r'xy,
    cases r'xy, { rw r'xy },
    have : ∀ x y, r x y → r' x y := λ x y h, or.inr h,
    rw ←quot.factor_mk_eq _ _ this, dsimp,
    rw [append_fun_comp_id, append_fun_comp_id],
    rw [@comp_map _ _ _ q _ _ _ (append_fun id (quot.mk r)),
        @comp_map _ _ _ q _ _ _ (append_fun id (quot.mk r))],
    rw h _ _ r'xy },
  right, exact rxy
end

/-- Bisimulation principle using `liftr` to match and relate children of two trees. -/
theorem cofix.bisim {α : typevec n}
    (r : cofix F α → cofix F α → Prop)
    (h : ∀ x y, r x y → liftr (rel_last α r) (cofix.dest x) (cofix.dest y)) :
  ∀ x y, r x y → x = y :=
begin
  apply cofix.bisim_rel,
  intros x y rxy,
  rcases (liftr_iff (rel_last α r) _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩,
  rw [dxeq, dyeq, ←abs_map, ←abs_map, mvpfunctor.map_eq, mvpfunctor.map_eq],
  rw [←split_drop_fun_last_fun f₀, ←split_drop_fun_last_fun f₁],
  rw [append_fun_comp_split_fun, append_fun_comp_split_fun],
  rw [id_comp, id_comp],
  congr' 2 with i j, cases i with _ i; dsimp,
  { apply quot.sound, apply h' _ j },
  { change f₀ _ j = f₁ _ j, apply h' _ j },
end

open mvfunctor

/-- Bisimulation principle using `liftr'` to match and relate children of two trees. -/
theorem cofix.bisim₂ {α : typevec n}
    (r : cofix F α → cofix F α → Prop)
    (h : ∀ x y, r x y → liftr' (rel_last' α r) (cofix.dest x) (cofix.dest y)) :
  ∀ x y, r x y → x = y :=
cofix.bisim _ $ by intros; rw ← liftr_last_rel_iff; apply h; assumption

/-- Bisimulation principle the values `⟨a,f⟩` of the polynomial functor representing
`cofix F α` as well as an invariant `Q : β → Prop` and a state `β` generating the
left-hand side and right-hand side of the equality through functions `u v : β → cofix F α` -/
theorem cofix.bisim' {α : typevec n} {β : Type*} (Q : β → Prop)
  (u v : β → cofix F α)
    (h : ∀ x, Q x → ∃ a f' f₀ f₁,
      cofix.dest (u x) = abs ⟨a, q.P.append_contents f' f₀⟩ ∧
      cofix.dest (v x) = abs ⟨a, q.P.append_contents f' f₁⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f₀ i = u x' ∧ f₁ i = v x') :
  ∀ x, Q x → u x = v x :=
λ x Qx,
let R := λ w z : cofix F α, ∃ x', Q x' ∧ w = u x' ∧ z = v x' in
cofix.bisim R
  (λ x y ⟨x', Qx', xeq, yeq⟩,
    begin
      rcases h x' Qx' with ⟨a, f', f₀, f₁, ux'eq, vx'eq, h'⟩,
      rw liftr_iff,
      refine ⟨a, q.P.append_contents f' f₀, q.P.append_contents f' f₁,
        xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, _⟩,
      intro i, cases i,
      { apply h' },
      { intro j, apply eq.refl },
    end)
  _ _ ⟨x, Qx, rfl, rfl⟩

lemma cofix.mk_dest {α : typevec n} (x : cofix F α) : cofix.mk (cofix.dest x) = x :=
begin
  apply cofix.bisim_rel (λ x y : cofix F α, x = cofix.mk (cofix.dest y)) _ _ _ rfl, dsimp,
  intros x y h, rw h,
  conv { to_lhs, congr, skip, rw [cofix.mk], rw cofix.dest_corec},
  rw [←comp_map, ←append_fun_comp, id_comp],
  rw [←comp_map, ←append_fun_comp, id_comp, ←cofix.mk],
  congr' 2 with u, apply quot.sound, refl
end

lemma cofix.dest_mk {α : typevec n} (x : F (α.append1 $ cofix F α)) : cofix.dest (cofix.mk x) = x :=
begin
  have : cofix.mk ∘ cofix.dest = @_root_.id (cofix F α) := funext cofix.mk_dest,
  rw [cofix.mk, cofix.dest_corec, ←comp_map, ←cofix.mk, ← append_fun_comp, this, id_comp,
    append_fun_id_id, mvfunctor.id_map]
end

lemma cofix.ext {α : typevec n} (x y : cofix F α) (h : x.dest = y.dest) : x = y :=
by rw [← cofix.mk_dest x,h,cofix.mk_dest]

lemma cofix.ext_mk {α : typevec n} (x y : F (α ::: cofix F α)) (h : cofix.mk x = cofix.mk  y) :
  x = y :=
by rw [← cofix.dest_mk x,h,cofix.dest_mk]

/-!
`liftr_map`, `liftr_map_last` and `liftr_map_last'` are useful for reasoning about
the induction step in bisimulation proofs.
-/

section liftr_map

omit q

theorem liftr_map {α β : typevec n} {F' : typevec n → Type u} [mvfunctor F']
  [is_lawful_mvfunctor F']
  (R : β ⊗ β ⟹ repeat n Prop) (x : F' α) (f g : α ⟹ β)
  (h : α ⟹ subtype_ R)
  (hh : subtype_val _ ⊚ h = (f ⊗' g) ⊚ prod.diag) :
  liftr' R (f <$$> x) (g <$$> x) :=
begin
  rw liftr_def,
  existsi h <$$> x,
  rw [mvfunctor.map_map,comp_assoc,hh,← comp_assoc,fst_prod_mk,comp_assoc,fst_diag],
  rw [mvfunctor.map_map,comp_assoc,hh,← comp_assoc,snd_prod_mk,comp_assoc,snd_diag],
  dsimp [liftr'], split; refl,
end

open function

theorem liftr_map_last [is_lawful_mvfunctor F] {α : typevec n} {ι ι'}
  (R : ι' → ι' → Prop) (x : F (α ::: ι)) (f g : ι → ι')
  (hh : ∀ x : ι, R (f x) (g x)) :
  liftr' (rel_last' _ R) ((id ::: f) <$$> x) ((id ::: g) <$$> x) :=
let h : ι → { x : ι' × ι' // uncurry R x } := λ x, ⟨ (f x,g x), hh x ⟩ in
let b : α ::: ι ⟹ _ := @diag_sub n α ::: h,
    c : subtype_ α.repeat_eq ::: {x // uncurry R x} ⟹
        (λ (i : fin2 (n)), {x // of_repeat (α.rel_last' R i.fs x)}) ::: subtype (uncurry R) :=
      of_subtype _ ::: id
in
have hh : subtype_val _ ⊚ to_subtype _ ⊚ from_append1_drop_last ⊚ c ⊚ b =
          (id ::: f ⊗' id ::: g) ⊚ prod.diag,
  by { dsimp [c,b],
       apply eq_of_drop_last_eq,
       { dsimp,
         simp only [prod_map_id, drop_fun_prod, drop_fun_append_fun, drop_fun_diag, id_comp,
                    drop_fun_to_subtype],
         erw [to_subtype_of_subtype_assoc,id_comp],
         clear_except,
         ext i x : 2, induction i,
         refl,  apply i_ih, },
       simp only [h, last_fun_from_append1_drop_last, last_fun_to_subtype, last_fun_append_fun,
                  last_fun_subtype_val, comp.left_id, last_fun_comp, last_fun_prod],
       dsimp, ext1, refl },
liftr_map _ _ _ _ (to_subtype _ ⊚ from_append1_drop_last ⊚ c ⊚ b) hh

theorem liftr_map_last' [is_lawful_mvfunctor F] {α : typevec n} {ι}
  (R : ι → ι → Prop) (x : F (α ::: ι)) (f : ι → ι)
  (hh : ∀ x : ι, R (f x) x) :
  liftr' (rel_last' _ R) ((id ::: f) <$$> x) x :=
begin
  have := liftr_map_last R x f id hh,
  rwa [append_fun_id_id,mvfunctor.id_map] at this,
end

end liftr_map

lemma cofix.abs_repr {α} (x : cofix F α) :
  quot.mk _ (cofix.repr x) = x :=
begin
  let R := λ x y : cofix F α,
    cofix.abs (cofix.repr y) = x,
  refine cofix.bisim₂ R _ _ _ rfl,
  clear x, rintros x y h, dsimp [R] at h, subst h,
  dsimp [cofix.dest,cofix.abs],
  induction y using quot.ind,
  simp only [cofix.repr, M.dest_corec, abs_map, abs_repr],
  conv { congr, skip, rw cofix.dest },
  dsimp, rw [mvfunctor.map_map,mvfunctor.map_map,← append_fun_comp_id,← append_fun_comp_id],
  let f : α ::: (P F).M α ⟹ subtype_ (α.rel_last' R) :=
    split_fun diag_sub (λ x, ⟨(cofix.abs (cofix.abs x).repr, cofix.abs x),_⟩),
  refine liftr_map _ _ _ _ f _,
  { simp only [←append_prod_append_fun, prod_map_id],
    apply eq_of_drop_last_eq,
    { dsimp, simp only [drop_fun_diag],
      erw subtype_val_diag_sub },
    ext1,
    simp only [cofix.abs, prod.mk.inj_iff, prod_map, function.comp_app, last_fun_append_fun,
               last_fun_subtype_val, last_fun_comp, last_fun_split_fun],
    dsimp [drop_fun_rel_last,last_fun,prod.diag],
    split; refl, },
  dsimp [rel_last',split_fun,function.uncurry,R],
  refl,
end

section tactic

setup_tactic_parser
open tactic
omit q

/-- tactic for proof by bisimulation -/
meta def mv_bisim (e : parse texpr) (ids : parse with_ident_list) : tactic unit :=
do e ← to_expr e,
   (expr.pi n bi d b) ← retrieve $ do
   { generalize e,
     target },
   `(@eq %%t %%l %%r) ← pure b,
   x ← mk_local_def `n d,
   v₀ ← mk_local_def `a t,
   v₁ ← mk_local_def `b t,
   x₀ ← mk_app ``eq [v₀,l.instantiate_var x],
   x₁ ← mk_app ``eq [v₁,r.instantiate_var x],
   xx ← mk_app ``and [x₀,x₁],
   ex ← lambdas [x] xx,
   ex ← mk_app ``Exists [ex] >>= lambdas [v₀,v₁],
   R ← pose `R none ex,
   refine ``(cofix.bisim₂ %%R _ _ _ ⟨_,rfl,rfl⟩),
   let f (a b : name) : name := if a = `_ then b else a,
   let ids := (ids ++ list.repeat `_ 5).zip_with f [`a,`b,`x,`Ha,`Hb],
   (ids₀,w::ids₁) ← pure $ list.split_at 2 ids,
   intro_lst ids₀,
   h ← intro1,
   [(_,[w,h],_)] ← cases_core h [w],
   cases h ids₁,
   pure ()

run_cmd add_interactive [``mv_bisim]

end tactic

theorem corec_roll {α : typevec n} {X Y} {x₀ : X}
  (f : X → Y) (g : Y → F (α ::: X)) :
  cofix.corec (g ∘ f) x₀ = cofix.corec (mvfunctor.map (id ::: f) ∘ g) (f x₀) :=
begin
  mv_bisim x₀,
  rw [Ha,Hb,cofix.dest_corec,cofix.dest_corec],
  rw [mvfunctor.map_map,← append_fun_comp_id],
  refine liftr_map_last _ _ _ _ _,
  intros a, refine ⟨a,rfl,rfl⟩
end

theorem cofix.dest_corec' {α : typevec n} {β : Type u}
  (g : β → F (α.append1 (cofix F α ⊕ β))) (x : β) :
  cofix.dest (cofix.corec' g x) = append_fun id (sum.elim id (cofix.corec' g)) <$$> g x :=
begin
  rw [cofix.corec',cofix.dest_corec], dsimp,
  congr' with (i|i); rw corec_roll; dsimp [cofix.corec'],
  { mv_bisim i,
    rw [Ha,Hb,cofix.dest_corec], dsimp [(∘)],
    repeat { rw [mvfunctor.map_map,← append_fun_comp_id] },
    apply liftr_map_last', dsimp [(∘),R], intros, exact ⟨_,rfl,rfl⟩ },
  { congr' with y, erw [append_fun_id_id], simp [mvfunctor.id_map] },
end

theorem cofix.dest_corec₁ {α : typevec n} {β : Type u}
  (g : Π {X}, (cofix F α → X) → (β → X) → β → F (α.append1 X)) (x : β)
  (h : ∀ X Y (f : cofix F α → X) (f' : β → X) (k : X → Y),
         g (k ∘ f) (k ∘ f') x = (id ::: k) <$$> g f f' x) :
  cofix.dest (cofix.corec₁ @g x) = g id (cofix.corec₁ @g) x :=
by rw [cofix.corec₁,cofix.dest_corec',← h]; refl

instance mvqpf_cofix : mvqpf (cofix F) :=
{ P         := q.P.Mp,
  abs       := λ α, quot.mk Mcongr,
  repr      := λ α, cofix.repr,
  abs_repr  := λ α, cofix.abs_repr,
  abs_map   := λ α β g x, rfl }

end mvqpf
