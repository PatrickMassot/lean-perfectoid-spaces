import analysis.topology.uniform_space

import for_mathlib.filter

namespace uniform_space
variables {α : Type*} [uniform_space α] {β : Type*} [uniform_space β] {γ : Type*} [uniform_space γ]

section separation_space

local attribute [instance] separation_setoid

lemma uniform_continuous_quotient {f : quotient (separation_setoid α) → β}
  (hf : uniform_continuous (λx, f ⟦x⟧)) : uniform_continuous f :=
hf

lemma uniform_continuous_quotient_lift
  {f : α → β} {h : ∀a b, (a, b) ∈ separation_rel α → f a = f b}
  (hf : uniform_continuous f) : uniform_continuous (λa, quotient.lift f h a) :=
uniform_continuous_quotient hf

lemma uniformity_quotient :
  @uniformity (quotient (separation_setoid α)) _ = uniformity.map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) :=
rfl

lemma uniform_continuous_quotient_lift₂ [uniform_space γ]
  {f : α → β → γ} {h : ∀a c b d, (a, b) ∈ separation_rel α → (c, d) ∈ separation_rel β → f a c = f b d}
  (hf : uniform_continuous (λp:α×β, f p.1 p.2)) :
  uniform_continuous (λp:_×_, quotient.lift₂ f h p.1 p.2) :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    filter.prod_map_map_eq, filter.tendsto_map'_iff, filter.tendsto_map'_iff],
  rwa [uniform_continuous, uniformity_prod_eq_prod, filter.tendsto_map'_iff] at hf
end

end separation_space

end uniform_space