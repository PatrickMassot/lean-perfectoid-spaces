import analysis.topology.topological_space
open set
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

lemma closure_prod (s : set α) (t : set β) : closure (set.prod s t) = set.prod (closure s) (closure t) :=
begin
  ext x,
  simp,
  repeat { rw mem_closure_iff },
  split,
  { intros h,
    split,
    { intros U U_op x_in,
      have op : is_open (set.prod U (univ : set β)), sorry,
      have in_ : x ∈ (set.prod U (univ : set β)), sorry,
      have := h _ op in_,
      rw [set.prod_inter_prod, prod_neq_empty_iff] at this,
      exact this.1 },
    { intros U U_op x_in,
      have op : is_open (set.prod (univ : set α) U), sorry,
      have in_ : x ∈ (set.prod (univ : set α) U), sorry,
      have := h _ op in_,
      rw [set.prod_inter_prod, prod_neq_empty_iff] at this,
      exact this.2 } },
  { rintro ⟨h, h'⟩ U H x_in,
    have : ∃ (U₁ : set α) (U₂ : set β), is_open U₁ ∧ is_open U₂ ∧ x ∈ set.prod U₁ U₂ ∧ set.prod U₁ U₂ ⊆ U,
    sorry,
    rcases this with ⟨U₁, U₂, ⟨op₁, op₂, x_in_prod, prod_sub⟩⟩,
    rw mem_prod at x_in_prod,
    specialize h U₁ op₁ x_in_prod.1,
    specialize h' U₂ op₂ x_in_prod.2,
    have := prod_neq_empty_iff.2 ⟨h, h'⟩,
    rw ←set.prod_inter_prod at this,
    have sub := inter_subset_inter_left (set.prod s t) prod_sub,
    exact subset_ne_empty sub this },
end