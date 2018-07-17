/-
 Lemmas in this file are currently not used in the perfectoid spaces project, but they
 were once thought to be useful, and could be PR'ed into mathlib anyway.
-/

import analysis.topology.topological_space

open set
lemma nonempty_iff_univ {α : Type*} : nonempty α ↔ (univ : set α) ≠ ∅ :=
begin
  split,
  { intro H,
    cases H with a,
    intro H2,
    show (∅ : set α) a,
    rw ←H2,
    trivial
  },
  intro H,
  apply classical.by_contradiction,
  intro H2,
  apply H,
  funext,
  exfalso,
  apply H2,
  exact ⟨a⟩
end

lemma nonempty_of_nonempty_range {α : Type*} {β : Type*} {f : α → β} (H : ¬range f = ∅) : nonempty α :=
begin
  cases exists_mem_of_ne_empty H with x h,
  cases mem_range.1 h with y _,
  exact ⟨y⟩
end


lemma closure_empty_iff {α : Type*} [topological_space α] (s : set α) :
closure s = ∅ ↔ s = ∅ :=
begin
  split ; intro h,
  { rw set.eq_empty_iff_forall_not_mem,
    intros x H,
    simpa [h] using subset_closure H },
  { exact (eq.symm h) ▸ closure_empty },
end
