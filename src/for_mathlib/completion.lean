/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

Hausdorff completions of uniform spaces.

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `completion α` and a morphism
(ie. uniformly continuous map) `to_completion : α → completion α` which solves the universal 
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`. 
It means any uniformly continuous `f : α → β` gives rise to a unique morphism 
`completion.map f : completion α → β` such that `f = completion_extension f ∘ to_completion α`.
Actually `completion_extension f` is defined for all maps from `α` to `β` but it has the desired 
properties only if `f` is uniformly continuous.

Beware that `to_completion α` is not injective if `α` is not Hausdorff. But its image is always 
dense.

The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, if turns `f : α → β` into
a morphism `completion.map f : completion α → completion β` such that 
`(to_completion β) ∘ f = (completion.map f) ∘ to_completion α` provided `f` is uniformly continuous.
This construction is compatible with composition.

This formalization is mostly based on N. Bourbaki: /General Topology/ but from a slightly 
different perspective in order to reuse material in analysis.topology.uniform_space.
-/

import analysis.topology.uniform_space
import data.set.function

import for_mathlib.quotient
import for_mathlib.continuity
import for_mathlib.uniform_space
import for_mathlib.function

namespace uniform_space
variables {α : Type*} [uniform_space α] {β : Type*} [uniform_space β] {γ : Type*} [uniform_space γ]

lemma uniform_continuous.prod.partial1 {f : α × β → γ} (h : uniform_continuous f) :
∀ b, uniform_continuous (λ a, f (a,b)) := λ b, uniform_continuous.comp 
      (uniform_continuous.prod_mk uniform_continuous_id uniform_continuous_const) h

lemma uniform_continuous.prod.partial2 {f : α × β → γ} (h : uniform_continuous f) :
∀ a, uniform_continuous (λ b, f (a,b)) := λ a, uniform_continuous.comp 
      (uniform_continuous.prod_mk uniform_continuous_const uniform_continuous_id) h

instance complete_space.prod [complete_space α] [complete_space β] : complete_space (α × β) :=
{ complete := λ f hf,
    let ⟨x1, hx1⟩ := complete_space.complete $ cauchy_map uniform_continuous_fst hf in
    let ⟨x2, hx2⟩ := complete_space.complete $ cauchy_map uniform_continuous_snd hf in
    ⟨(x1, x2), by rw [nhds_prod_eq, filter.prod_def];
      from filter.le_lift (λ s hs, filter.le_lift' $ λ t ht,
        have H1 : prod.fst ⁻¹' s ∈ f.sets := hx1 hs,
        have H2 : prod.snd ⁻¹' t ∈ f.sets := hx2 ht,
        filter.inter_mem_sets H1 H2)⟩ }

end uniform_space

local attribute [instance, priority 0] classical.prop_decidable

local attribute [instance] separation_setoid

open Cauchy

namespace uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]

lemma separated_of_uniform_continuous {f : α → β} (H : uniform_continuous f) {x y : α} 
(h : x ≈ y) : f x ≈ f y :=
assume _ h', h _ (H h')

lemma eq_of_separated_of_uniform_continuous [separated β] {f : α → β} (H : uniform_continuous f) {x y : α} 
(h : x ≈ y) : f x = f y :=
separated_def.1 (by apply_instance) _ _ $ separated_of_uniform_continuous H h

lemma separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
begin
  split ; intro h,
  { exact ⟨separated_of_uniform_continuous uniform_continuous_fst h,
           separated_of_uniform_continuous uniform_continuous_snd h⟩ },
  { rcases h with ⟨eqv_α, eqv_β⟩,  
    intros r r_in,
    rw uniformity_prod at r_in,
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, H⟩,

    let p_α := λ (p : (α × β) × α × β), ((p.fst).fst, (p.snd).fst),
    let p_β := λ (p : (α × β) × α × β), ((p.fst).snd, (p.snd).snd),    
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α, by simp[p_α, eqv_α r_α r_α_in],
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β, by simp[p_β, eqv_β r_β r_β_in],
    exact H ⟨h_α key_α, h_β key_β⟩ },
end

instance separated.prod [separated α] [separated β] : separated (α × β) := 
separated_def.2 $ assume x y H, prod.ext 
  (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
  (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)

lemma prod_cauchy {f : filter α} {g : filter β} : cauchy f → cauchy g → cauchy (filter.prod f g)
| ⟨f_proper, hf⟩ ⟨g_proper, hg⟩ := ⟨filter.prod_neq_bot.2 ⟨f_proper, g_proper⟩,
  let p_α := λp:(α×β)×(α×β), (p.1.1, p.2.1), p_β := λp:(α×β)×(α×β), (p.1.2, p.2.2) in
  suffices (f.prod f).vmap p_α ⊓ (g.prod g).vmap p_β ≤ uniformity.vmap p_α ⊓ uniformity.vmap p_β,
    by simpa [uniformity_prod, filter.prod, filter.vmap_inf, filter.vmap_vmap_comp, (∘),
        lattice.inf_assoc, lattice.inf_comm, lattice.inf_left_comm],
  lattice.inf_le_inf (filter.vmap_mono hf) (filter.vmap_mono hg)⟩

variable (α)

/-- Hausdorff completion of `α` -/
def completion := quotient (separation_setoid $ Cauchy α)

instance : uniform_space (completion α) := by unfold completion ; apply_instance

instance : complete_space (completion α) := complete_space_separation 

instance : separated (completion α) := separated_separation

instance : t2_space (completion α) := separated_t2

instance : regular_space (completion α) := separated_regular

/-- Canonical map. Not always injective. -/
def to_completion : α → completion α := quotient.mk ∘ pure_cauchy

/-- Automatic coercion from `α` to its completion -/
instance : has_coe α (completion α) := ⟨to_completion α⟩

namespace to_completion
open set

lemma uniform_continuous : uniform_continuous (to_completion α) :=
uniform_continuous.comp uniform_embedding_pure_cauchy.uniform_continuous 
  uniform_continuous_quotient_mk

lemma continuous : continuous (to_completion α) :=
uniform_continuous.continuous (uniform_continuous α)

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

lemma nonempty_completion_iff : nonempty (completion α) ↔ nonempty α :=
begin
  split ; rintro ⟨c⟩,
  { have := eq_univ_iff_forall.1 (to_completion.dense α) c,
    have := mem_closure_iff.1 this _ is_open_univ trivial,
    rcases exists_mem_of_ne_empty this with ⟨_, ⟨_, a, _⟩⟩,
    exact ⟨a⟩ },
  { exact ⟨to_completion α c⟩ }
end

/-- "Extension" to the completion. 
    Defined for any map `f` but returns garbage if `f` is not uniformly continuous -/
noncomputable
def completion_extension (f : α → β) : completion α → β :=
if H : uniform_continuous f then 
  let g₀ := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).extend f in
  have g₀_unif : uniform_continuous g₀ := 
    uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense H,
  have compat : ∀ p q : Cauchy α, p ≈ q → g₀ p = g₀ q :=
    assume p q h, eq_of_separated_of_uniform_continuous g₀_unif h,
  quotient.lift g₀ compat
else
  λ x, f (classical.inhabited_of_nonempty $ nonempty_completion_iff.1 ⟨x⟩).default

/-- Completion functor acting on morphisms -/
noncomputable def completion.map (f : α → γ) : completion α → completion γ :=
completion_extension ((to_completion γ) ∘ f)
end uniform_space

namespace completion_extension
open uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables [complete_space β] [separated β]

variables {f : α → β} (H : uniform_continuous f)
include H

lemma lifts : f = (completion_extension f) ∘ to_completion α :=
begin
  unfold completion_extension,
  simp [H],
  ext x,
  let lim := H.continuous.tendsto x,
  have := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).extend_e_eq lim,
  rw ←this,
  refl
end

@[simp]
lemma lifts' : ∀ a : α, f a = (completion_extension f) a := λ a, congr_fun (lifts H) a

lemma uniform_continuity : uniform_continuous (completion_extension f) :=
begin
  unfold completion_extension,
  split_ifs,
  let g := completion_extension f,
  intros r r_in,
  let g₀ := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).extend f,
  have g₀_unif : uniform_continuous g₀ := 
    uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense H,

  rw filter.mem_map,
  dsimp[completion],
  rw quotient.prod_preimage_eq_image _ rfl r, 
  exact filter.image_mem_map (g₀_unif r_in)
end

lemma continuity : continuous (completion_extension f) :=
uniform_continuous.continuous (uniform_continuity H)

lemma unique {h : completion α → β} :
  uniform_continuous h → f = (h ∘ to_completion α) → h = completion_extension f :=
begin
  let g := completion_extension f,
  have g_unif : uniform_continuous g := uniform_continuity H,
  intros h_unif h_lifts,
  change h = g,
  ext x,
  have closed_eq : is_closed {x | h x = g x} := is_closed_eq h_unif.continuous g_unif.continuous,
  have : f = g ∘ to_completion α := lifts H,
  have eq_on_α : ∀ x, (h ∘ to_completion α) x = (g ∘ to_completion α) x, by cc,
  exact (is_closed_property (to_completion.dense α) closed_eq eq_on_α x : _)
end
end completion_extension

namespace completion
variables {α : Type*} [uniform_space α] {β : Type*} [uniform_space β]
open uniform_space

def dense_cauchy := uniform_embedding_pure_cauchy.dense_embedding (@pure_cauchy_dense α _)

lemma dense_prod : dense_embedding (λ p : α × β, (pure_cauchy p.1, pure_cauchy p.2)) :=
dense_embedding.prod dense_cauchy dense_cauchy

noncomputable
def prod_prod : (completion α) × (completion β) → completion (α × β) :=
begin
  let g₀ := λ (a : Cauchy α) (b : Cauchy β),  (dense_prod.extend (to_completion (α × β))) (a, b),
  
  refine function.uncurry (quotient.lift₂ g₀ _),
  { intros a₁ b₁ a₂ b₂ eqv₁ eqv₂,
    have g₁_uc : uniform_continuous (dense_prod.extend (to_completion (α × β))),
    { let ue : uniform_embedding (λ (p : α × β), (pure_cauchy (p.fst), pure_cauchy (p.snd))) :=
        uniform_embedding.prod uniform_embedding_pure_cauchy uniform_embedding_pure_cauchy,
      refine uniform_continuous_uniformly_extend ue _ (to_completion.uniform_continuous (α × β)) },
    
    have := eq_of_separated_of_uniform_continuous g₁_uc (separation_prod.2 ⟨eqv₁, eqv₂⟩),
    exact this },
end

lemma prod_prod.uc : uniform_continuous (@prod_prod α _ β _) :=
begin
  dsimp[prod_prod],
  rw uncurry_def,
  apply uniform_continuous_quotient_lift₂,
  suffices : uniform_continuous (dense_embedding.extend dense_prod (to_completion (α × β))),
  by simpa,
  exact uniform_continuous_uniformly_extend  
    (uniform_embedding.prod uniform_embedding_pure_cauchy uniform_embedding_pure_cauchy)
    dense_prod.dense (to_completion.uniform_continuous _)
end

lemma prod_prod_lift (a : α) (b : β) : @prod_prod α _ β _ (a, b) = (a, b) := 
begin
  let f := to_completion (α × β),
  change dense_embedding.extend dense_prod f (pure_cauchy a, pure_cauchy b) = ⟦pure_cauchy (a, b)⟧,

  have hf : filter.tendsto f (nhds (a, b)) (nhds (f (a,b))) := 
    continuous.tendsto (to_completion.continuous _) _,

  exact (dense_prod.extend_e_eq hf : _)
end

end completion


namespace completion.map
open uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]

variables {f : α → β} (H : uniform_continuous f)
variables {g : β → γ} (H' : uniform_continuous g)

lemma lifts : (to_completion β) ∘ f = (completion.map f) ∘ to_completion α :=
completion_extension.lifts $ uniform_continuous.comp H (to_completion.uniform_continuous β)

lemma unique {f' : completion α → completion β} :
  uniform_continuous f' → (to_completion β) ∘ f = f' ∘ to_completion α → f' = completion.map f :=
completion_extension.unique $ uniform_continuous.comp H (to_completion.uniform_continuous β)

lemma uniform_continuity : uniform_continuous (completion.map f) :=
completion_extension.uniform_continuity $ uniform_continuous.comp H (to_completion.uniform_continuous β)

include H H'
lemma comp : completion.map (g ∘ f) = (completion.map g) ∘ completion.map f :=
begin
  let l  := completion.map f,
  let l' := completion.map g,
  have : uniform_continuous (g ∘ f) := uniform_continuous.comp H H',
  have : uniform_continuous (l' ∘ l ):= 
    uniform_continuous.comp (uniform_continuity H) (uniform_continuity H'),
  have : (to_completion γ ∘ g) ∘ f = (l' ∘ l) ∘ to_completion α := calc
    (to_completion γ ∘ g) ∘ f = (l' ∘ to_completion β) ∘ f : by rw completion.map.lifts H'
    ... = l' ∘ (to_completion β ∘ f) : rfl
    ... = l' ∘ (l  ∘ to_completion α) : by rw completion.map.lifts H,
  apply eq.symm,
  apply unique ; assumption
end
end completion.map