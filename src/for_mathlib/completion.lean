import analysis.topology.uniform_space
import data.set.function

local attribute [instance] separation_setoid

open Cauchy

namespace uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]

lemma separation_rel_of_uniform_continuous {f : α → β} (H : uniform_continuous f) {x y : α} 
(h : x ≈ y) : f x ≈ f y :=
assume _ h', h _ (H h')

lemma apply_eq_of_separated [separated β] {f : α → β} (H : uniform_continuous f) {x y : α} 
(h : x ≈ y) : f x = f y :=
separated_def.1 (by apply_instance) _ _ $ separation_rel_of_uniform_continuous H h

variable (α)

def completion := quotient (separation_setoid $ Cauchy α)

instance : uniform_space (completion α) := by unfold completion ; apply_instance

instance : complete_space (completion α) := complete_space_separation 

instance : separated (completion α) := separated_separation


def to_completion : α → completion α := quotient.mk ∘ pure_cauchy

variable {α}
variables [complete_space β] [separated β] [inhabited β]

open set

theorem completion_ump {f : α → β} (H : uniform_continuous f) :
∃ g : completion α → β, (uniform_continuous g) ∧ f = g ∘ (to_completion α) :=
begin
  let de := uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense,
  let g₀ := de.ext f,
  have g₀_unif : uniform_continuous g₀ := 
    uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense H,
  have compat : ∀ p q : Cauchy α, p ≈ q → g₀ p = g₀ q :=
    assume p q h, apply_eq_of_separated g₀_unif h, 
  let g := quotient.lift g₀ compat,
  existsi g,
  split,
  { intros r r_in,
    rw filter.mem_map,
    
    sorry },
  { ext x,
    apply eq.symm,
    exact de.ext_e_eq (H.continuous.tendsto x) }
end
end uniform_space