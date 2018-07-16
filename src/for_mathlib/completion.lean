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

def completion := quotient (separation_setoid $ Cauchy α)

instance : uniform_space (completion α) := by unfold completion ; apply_instance

instance : complete_space (completion α) := complete_space_separation 

instance : separated (completion α) := separated_separation


def to_completion : α → completion α := quotient.mk ∘ pure_cauchy

open set

lemma dense_in_completion  : closure (range (to_completion α)) = univ   :=
begin
  dsimp[to_completion],
  rw range_comp,
  exact dense_of_quotient_dense pure_cauchy_dense
end

variable {α}
variables [complete_space β] [separated β] [inhabited β]

open set

theorem completion_ump {f : α → β} (H : uniform_continuous f) :
∃! g : completion α → β, (uniform_continuous g) ∧ f = g ∘ (to_completion α) :=
begin
  let de := uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense,
  let g₀ := de.ext f,
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
      exact eq.symm (de.ext_e_eq (H.continuous.tendsto x)) },
  existsi g,
  split,
  { exact ⟨g_unif, g_factor⟩ },
  { rintro h ⟨h_unif, h_factor⟩,
    ext x,
    have closed_eq : is_closed {x | h x = g x} := is_closed_eq h_unif.continuous g_unif.continuous,
    have eq_on_α : ∀ x, (h ∘ to_completion α) x = (g ∘ to_completion α) x, by cc,
    apply is_closed_property (dense_in_completion α) closed_eq eq_on_α x }
end
end uniform_space