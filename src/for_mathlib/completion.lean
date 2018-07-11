import analysis.topology.uniform_space
import data.set.function

local attribute [instance] separation_setoid

open Cauchy

namespace uniform_space
variables (α : Type*) [uniform_space α]

def completion := quotient (separation_setoid $ Cauchy α)

instance : uniform_space (completion α) := by unfold completion ; apply_instance

instance : complete_space (completion α) := complete_space_separation 

instance : separated (completion α) := separated_separation


def to_completion : α → completion α := quotient.mk ∘ pure_cauchy

variable {α}
variables {β : Type*} [uniform_space β] [complete_space β] [separated β] [inhabited β]

open set

theorem completion_ump {f : α → β} (H : uniform_continuous f) :
∃ g : completion α → β, (uniform_continuous g) ∧ f = g ∘ (to_completion α) :=
begin
  let g₀ := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).ext f,
  have compat : ∀ p q : Cauchy α, p ≈ q → g₀ p = g₀ q, sorry,
  existsi (quotient.lift g₀ compat),
  split,
  { 
    sorry },
  { ext,
    sorry },
end
end uniform_space