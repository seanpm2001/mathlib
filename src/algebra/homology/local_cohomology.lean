/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Scott Morrison, Jake Levinson, Sam van Gool
-/
import ring_theory.ideal.basic
import algebra.category.Module.colimits
import algebra.category.Module.projective
import category_theory.abelian.ext
import ring_theory.finiteness

/-!
# Local cohomology.

This file defines the `i`-th local cohomology module of an `R`-module `M` with support in an
ideal `I` of `R`, where `R` is a commutative ring, as the direct limit of Ext modules:

Given a collection of ideals cofinal with the powers of `I`, consider the directed system of
quotients of `R` by these ideals, and take the direct limit of the system induced on the `i`-th
Ext into `M`.  One can, of course, take the collection to simply be the integral powers of `I`.

## References

* [M. Hochster, *Local cohomology*][hochsterunpublished]
  <https://dept.math.lsa.umich.edu/~hochster/615W22/lcc.pdf>
* [R. Hartshorne, *Local cohomology: A seminar given by A. Grothendieck*][hartshorne61]
* [M. Brodmann and R. Sharp, *Local cohomology: An algebraic introduction with geometric
  applications*][brodmannsharp13]
* [S. Iyengar, G. Leuschke, A. Leykin, Anton, C. Miller, E. Miller, A. Singh, U. Walther,
  *Twenty-four hours of local cohomology*][iyengaretal13]

## Tags

local cohomology, local cohomology modules

## Future work

* Prove that this definition is equivalent to:
    * the right-derived functor definition
    * the characterization as the limit of Koszul homology
    * the characterization as the cohomology of a Cech-like complex
* Prove that local cohomology depends only on the radical of the ideal
* Establish long exact sequence(s) in local cohomology
-/

open opposite
open category_theory
open category_theory.limits

noncomputable theory

universes u v


namespace local_cohomology

/- We define local cohomology, implemented as a direct limit of `Ext(R/J, -)`. -/
section
variables {R : Type u} [comm_ring R] {D : Type v} [small_category D]

/--  The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `R`,
determined by the functor `I`  -/
def ring_mod_ideals (I : D ⥤ ideal R) : D ⥤ Module.{u} R :=
{ obj := λ t, Module.of R $ R ⧸ (I.obj t),
  map := λ s t w, submodule.mapq _ _ (linear_map.id) (I.map w).down.down }

/- TODO:  Once this file is ported, move this file to the right location. -/
instance Module_enough_projectives' : enough_projectives (Module.{u} R) :=
  Module.Module_enough_projectives.{u}

/-- The diagram we will take the colimit of to define local cohomology, corresponding to the
directed system determined by the functor `I` -/
def diagram (I : D ⥤ ideal R) (i : ℕ) : Dᵒᵖ ⥤ Module.{u} R ⥤ Module.{u} R :=
(ring_mod_ideals I).op ⋙ Ext R (Module.{u} R) i

end

section
-- We momentarily need to work with a type inequality, as later we will take colimits
-- along diagrams either in Type, or in the same universe as the ring, and we need to cover both.
variables {R : Type max u v} [comm_ring R] {D : Type v} [small_category D]

/-- `local_cohomology.of_diagram I i` is the the functor sending a module `M` over a commutative
ring `R` to the direct limit of `Ext^i(R/J, M)`, where `J` ranges over a collection of ideals
of `R`, represented as a functor `I`. -/
/-
In this definition we do not assume any special property of the diagram `I`, but the relevant case
will be where `I` is (cofinal with) the diagram of powers of a single given ideal.

Below, we give two equivalent (to be shown) definitions of the usual local cohomology with support
in an ideal `J`, `local_cohomology` and `local_cohomology.of_self_le_radical`.

TODO: Show that any functor cofinal with `I` gives the same result.
 -/
def of_diagram (I : D ⥤ ideal R) (i : ℕ) :
  Module.{max u v} R ⥤ Module.{max u v} R :=
colimit (diagram.{(max u v) v} I i)

end

section diagrams

variables {R : Type u} [comm_ring R]

/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
def ideal_powers_diagram (J : ideal R) : ℕᵒᵖ ⥤ ideal R :=
{ obj := λ t, J^(unop t),
  map := λ s t w, ⟨⟨ideal.pow_le_pow w.unop.down.down⟩⟩, }

/-- The full subcategory of all ideals with radical containing `J` -/
@[derive category] def self_le_radical (J : ideal R) : Type u :=
full_subcategory (λ J' : ideal R, J ≤ J'.radical)

instance self_le_radical.inhabited (J : ideal R) : inhabited (self_le_radical J) :=
{ default := ⟨J, ideal.le_radical⟩ }

/-- The diagram of all ideals with radical containing `J`, represented as a functor.
This is the "largest" diagram that computes local cohomology with support in `J`. -/
def self_le_radical_diagram (J : ideal R) : (self_le_radical J) ⥤ ideal R :=
full_subcategory_inclusion _

end diagrams

end local_cohomology

/-! We give two models for the local cohomology with support in an ideal `J`: first in terms of
the powers of `J` (`local_cohomology`), then in terms of *all* ideals with radical
containing `J` (`local_cohomology.of_self_le_radical`). -/
section models_for_local_cohomology

open local_cohomology

variables {R : Type u} [comm_ring R]

/-- `local_cohomology J i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R`, defined as the direct limit
of `Ext^i(R/J^t, M)` over all powers `t : ℕ`. -/
def local_cohomology (J : ideal R) (i : ℕ) : Module.{u} R ⥤ Module.{u} R :=
  of_diagram (ideal_powers_diagram J) i

/-- Local cohomology as the direct limit of `Ext^i(R/J', M)` over *all* ideals `J'` with radical
containing `J`. -/
def local_cohomology.of_self_le_radical (J : ideal R) (i : ℕ) :
  Module.{u} R ⥤ Module.{u} R :=
of_diagram.{u} (self_le_radical_diagram.{u} J) i
/- TODO: Construct `local_cohomology J i ≅ local_cohomology.of_self_le_radical J i`. Use this to
show that local cohomology depends only on `J.radical`. -/

end models_for_local_cohomology


section local_cohomology_equiv

open local_cohomology

variables {R : Type u} [comm_ring R] (I J : ideal R)

/-- Lifting `ideal_powers_diagram J` from a diagram valued in `ideals R` to a diagram
valued in `self_le_radical J`. -/
def local_cohomology.ideal_powers_to_self_le_radical (J : ideal R) : ℕᵒᵖ ⥤ self_le_radical J :=
full_subcategory.lift _ (ideal_powers_diagram J)
(λ k, begin
  change _ ≤ (J^(unop k)).radical,
  cases (unop k),
  { simp only [ideal.radical_top, pow_zero, ideal.one_eq_top, le_top] },
  { simp only [J.radical_pow _ n.succ_pos, ideal.le_radical] },
end)

/-- The composition with the inclusion into `ideals R` is isomorphic to `ideal_powers_diagram J`. -/
def local_cohomology.ideal_powers_to_self_le_radical_comp_inclusion (J : ideal R) :
local_cohomology.ideal_powers_to_self_le_radical J ⋙ self_le_radical_diagram J
  ≅ ideal_powers_diagram J :=
  full_subcategory.lift_comp_inclusion _ _ _

/-- The lemma below essentially says that `ideal_powers_to_self_le_radical I` is initial in
`self_le_radical_diagram I`.

PORTING NOTE: This lemma should probably be moved to `ring_theory/finiteness.lean`
to be near `ideal.exists_radical_pow_le_of_fg`, which it generalizes. -/
lemma ideal.exists_pow_le_of_le_radical_of_fg (hIJ : I ≤ J.radical) (hJ : J.radical.fg) :
  ∃ (k : ℕ), I^k ≤ J :=
begin
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ,
  use k,
  calc I^k ≤ J.radical^k : ideal.pow_mono hIJ _
       ... ≤ J           : hk,
end

end local_cohomology_equiv
