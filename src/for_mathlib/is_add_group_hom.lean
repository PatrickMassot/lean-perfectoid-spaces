variables {α : Type*} {β : Type*} [add_group α] [add_group β]
class is_add_group_hom  (f : α → β) : Prop :=
(add : ∀ a b : α, f (a + b) = f a + f b)

namespace is_add_group_hom
variables (f : α → β) [is_add_group_hom f]
instance comp {γ} [add_group γ] (g : β → γ) [is_add_group_hom g] :
  is_add_group_hom (g ∘ f) :=
⟨λ x y, calc
  g (f (x + y)) = g (f x + f y)       : by rw add f
  ...           = g (f x) + g (f y)   : by rw add g⟩
end is_add_group_hom
