/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

Hausdorff completions of topological spaces.

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `completion α` and a morphism
(ie. uniformly continuous map) `to_completion : α → completion α` which solves the universal 
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`. 
It means any uniformly continuous `f : α → β` gives rise to a unique morphism 
`g : completion α → β` such that `f = g ∘ to_completion α`. This morphism
is `completion_lift H` where `H : uniform_continuous f` (`f` itself is an implicit argument to
`completion_lift`). 

Beware that `to_completion α` is not injective if `α` is not Hausdorff. But its image is always 
dense.

The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, if turns `f : α → β`, `H : uniform_continuous f` into
a morphism `completion_lift H : completion α → completion β` such that 
`(to_completion β) ∘ f = (completion_lift H) ∘ to_completion α`. This construction is
compatible with composition.

This formalization is mostly based on N. Bourbaki: General Topology but from a slightly 
different perspective in order to reuse material in analysis.topology.uniform_space.
-/

import analysis.topology.uniform_space
import data.set.function

import for_mathlib.quotient
import for_mathlib.continuity

local attribute [instance] separation_setoid

open Cauchy

namespace uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]

lemma separated_of_uniform_continuous {f : α → β} (H : uniform_continuous f) {x y : α} 
(h : x ≈ y) : f x ≈ f y :=
assume _ h', h _ (H h')

lemma eq_of_separated_of_uniform_continuous [separated β] {f : α → β} (H : uniform_continuous f) {x y : α} 
(h : x ≈ y) : f x = f y :=
separated_def.1 (by apply_instance) _ _ $ separated_of_uniform_continuous H h

variable (α)

/-- Hausdorff completion of `α` -/
def completion := quotient (separation_setoid $ Cauchy α)

instance : uniform_space (completion α) := by unfold completion ; apply_instance

instance : complete_space (completion α) := complete_space_separation 

instance : separated (completion α) := separated_separation

/-- The following instances are no longer useful here, but could go to mathlib anyway.

instance inhabited_separation_space [h : inhabited α] : 
  inhabited (quotient (separation_setoid α)) := ⟨⟦h.default⟧⟩

instance inhabited_completion [inhabited α] : inhabited (completion α) := 
by unfold completion; apply_instance


/-- Canonical map. Not always injective. -/
def to_completion : α → completion α := quotient.mk ∘ pure_cauchy

namespace to_completion
open set

lemma uniform_continuous : uniform_continuous (to_completion α) :=
uniform_continuous.comp uniform_embedding_pure_cauchy.uniform_continuous uniform_continuous_quotient_mk

lemma dense : closure (range (to_completion α)) = univ   :=
begin
  dsimp[to_completion],
  rw range_comp,
  exact dense_of_quotient_dense pure_cauchy_dense
end
end to_completion

variable {α}
variables [complete_space β] [separated β]

open set

/-- Universal mapping property of Hausdorff completion -/
theorem completion_ump {f : α → β} (H : uniform_continuous f) :
∃! g : completion α → β, (uniform_continuous g) ∧ f = g ∘ (to_completion α) :=
begin
  let de := uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense,
  let g₀ := de.extend f,
  have g₀_unif : uniform_continuous g₀ := 
    uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense H,
  have compat : ∀ p q : Cauchy α, p ≈ q → g₀ p = g₀ q :=
    assume p q h, eq_of_separated_of_uniform_continuous g₀_unif h, 
  let g := quotient.lift g₀ compat,
  have g_unif : uniform_continuous g,
  { intros r r_in,
      rw filter.mem_map,
      rw quotient.prod_preimage_eq_image g rfl r,
      exact filter.image_mem_map (g₀_unif r_in) },
  have g_factor : f = g ∘ (to_completion α),
  { ext x,
      exact eq.symm (de.extend_e_eq (H.continuous.tendsto x)) },
  existsi g,
  split,
  { exact ⟨g_unif, g_factor⟩ },
  { rintro h ⟨h_unif, h_factor⟩,
    ext x,
    have closed_eq : is_closed {x | h x = g x} := is_closed_eq h_unif.continuous g_unif.continuous,
    have eq_on_α : ∀ x, (h ∘ to_completion α) x = (g ∘ to_completion α) x, by cc,
    apply is_closed_property (to_completion.dense α) closed_eq eq_on_α x }
end

/-- "Extension" to the completion -/
noncomputable def completion_extension {f : α → β} (H : uniform_continuous f) : completion α → β :=
classical.some (completion_ump H)

variables {γ : Type*} [uniform_space γ]

/-- Completion functor acting on morphisms -/
noncomputable def completion_lift {f : α → γ} (H : uniform_continuous f) : completion α → completion γ :=
classical.some (completion_ump $ uniform_continuous.comp H (to_completion.uniform_continuous γ))
end uniform_space


namespace completion_extension
open uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables [complete_space β] [separated β]

variables {f : α → β} (H : uniform_continuous f)

lemma lifts : f = (completion_extension H) ∘ to_completion α :=
(classical.some_spec (completion_ump H)).1.2

lemma unique {f' : completion α → β} :
  uniform_continuous f' → f = (f' ∘ to_completion α) → f' = completion_extension H :=
assume uc fac, (classical.some_spec (completion_ump H)).2 f' ⟨uc, fac⟩

lemma uniform_continuity : uniform_continuous (completion_extension H) :=
(classical.some_spec (completion_ump H)).1.1
end completion_extension

namespace completion_lift
open uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]

variables {f : α → β} (H : uniform_continuous f)
variables {g : β → γ} (H' : uniform_continuous g)

lemma lifts : (to_completion β) ∘ f = (completion_lift H) ∘ to_completion α :=
completion_extension.lifts $ uniform_continuous.comp H (to_completion.uniform_continuous β)

lemma unique {f' : completion α → completion β} :
  uniform_continuous f' → (to_completion β) ∘ f = f' ∘ to_completion α → f' = completion_lift H :=
completion_extension.unique $ uniform_continuous.comp H (to_completion.uniform_continuous β)

lemma uniform_continuity : uniform_continuous (completion_lift H) :=
completion_extension.uniform_continuity $ uniform_continuous.comp H (to_completion.uniform_continuous β)

lemma comp : completion_lift (uniform_continuous.comp H H') = (completion_lift H') ∘ completion_lift H :=
begin
  let l  := completion_lift H,
  let l' := completion_lift H',
  have : uniform_continuous (l' ∘ l ):= 
    uniform_continuous.comp (uniform_continuity H) (uniform_continuity H'),
  have : (to_completion γ ∘ g) ∘ f = (l' ∘ l) ∘ to_completion α := calc
    (to_completion γ ∘ g) ∘ f = (l' ∘ to_completion β) ∘ f : by rw completion_lift.lifts H'
    ... = l' ∘ (to_completion β ∘ f) : rfl
    ... = l' ∘ (l  ∘ to_completion α) : by rw completion_lift.lifts H,
  apply eq.symm,
  apply unique; assumption  
end
end completion_lift