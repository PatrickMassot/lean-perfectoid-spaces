import analysis.topology.topological_structures

import for_mathlib.completion
import for_mathlib.function
import for_mathlib.is_add_group_hom

section
variables {α : Type*} {β : Type*} {γ : Type*}
/-- This is a helper lemma for associativity of addition in `completion_group_str`. 
    It could probably be inlined. TODO: prove every permutation of a finite product 
    of top spaces is continuous. -/
lemma continuous_pat_perm [topological_space α] [topological_space β] [topological_space γ] : 
  continuous (λ x : α × β × γ, (x.2.2, (x.1, x.2.1))) :=
have c : continuous (λ x : α × β × γ, x.2.2) :=
   continuous.comp continuous_snd continuous_snd,
have c' : continuous (λ x : α × β × γ, (x.1, x.2.1)) :=
 continuous.prod_mk continuous_fst (continuous.comp continuous_snd continuous_fst), 
continuous.prod_mk c c'
end
open filter

lemma set.preimage_subset_iff {α : Type*} {β : Type*} {A : set α} {B : set β} {f : α → β} :
  (∀ a : α, f a ∈ B → a ∈ A) ↔ f⁻¹' B ⊆ A :=
⟨λ H x h, H x h, λ H x h, H h⟩ 

lemma vmap_eq_of_inverse {α : Type*} {β : Type*} {f : filter α} {g : filter β} 
  {φ : α → β} {ψ : β → α} (inv₁ : φ ∘ ψ = id) (inv₂ : ψ ∘ φ = id)
  (lim₁ : tendsto φ f g) (lim₂ : tendsto ψ g f)
 : vmap φ g = f :=
begin
  have ineq₁ := calc
    vmap φ g = map ψ g : eq.symm (map_eq_vmap_of_inverse inv₂ inv₁)
         ... ≤ f : lim₂,
  have ineq₂ : f ≤ vmap φ g := map_le_iff_le_vmap.1 lim₁,
  exact le_antisymm ineq₁ ineq₂
end

lemma pure_le_nhds {α : Type*} [topological_space α] (a : α) : pure a ≤ nhds a :=
assume s s_nhds, by simp[mem_of_nhds s_nhds]

section topological_add_group
universe u
variables {G : Type u} [add_group G] [topological_space G] [topological_add_group G]  

lemma half_nhd (U ∈ (nhds (0 : G)).sets) : 
  ∃ V ∈ (nhds (0 : G)).sets, ∀ v w ∈ V, v + w ∈ U :=
/- Here is the story : by continuity of addition, and because 0 + 0 = 0,
   (+)⁻¹(U) is a neighborhood of (0, 0). Hence it contains some V₁ × V₂. Then set V = V₁ ∩ V₂ -/
begin
  have nhdb_in_prod : ((λ a : G × G, a.1+a.2)⁻¹' U) ∈ (nhds ((0, 0) : G × G)).sets,
    by apply tendsto_add' ; simp [H],
  rw nhds_prod_eq at nhdb_in_prod,
  rcases mem_prod_iff.1 nhdb_in_prod with ⟨V₁, H₁, V₂, H₂, H⟩,
  have H12: V₁ ∩ V₂ ∈ (nhds (0 : G)).sets := inter_mem_sets H₁ H₂,    
  existsi [(V₁ ∩ V₂), H12],
  intros v w Hv Hw,
  have : (v,w) ∈ set.prod V₁ V₂, by finish,
  simpa using H this
end

lemma continuous_translation (a : G) : continuous (λ b, b + a) := 
have cont : continuous (λ b : G, (b, a)) := continuous.prod_mk continuous_id continuous_const,
 by simp[continuous.comp cont continuous_add']

lemma continuous_neg_translation (a : G) :
continuous (λ b, b - a) := continuous_translation (-a)

variable (G)
lemma nhds_zero_symm : vmap (λ r : G, -r) (nhds (0 : G)) = nhds (0 : G) :=
begin
  let neg := (λ r : G, -r),
  have inv : neg ∘ neg = id, { funext x, simp[neg_eq_iff_neg_eq] },
  have lim : tendsto neg (nhds 0) (nhds 0) := 
    by simpa using continuous.tendsto (topological_add_group.continuous_neg G) 0,
  exact vmap_eq_of_inverse inv inv lim lim
end

variable {G}

lemma nhds_translation (x : G) : nhds x = vmap (λ y, y-x) (nhds (0 : G)) := 
begin
  have lim₁ : tendsto (λ (y : G), y-x) (nhds x) (nhds 0), 
    by simpa using continuous.tendsto (continuous_neg_translation x) x,
  have lim₂ : tendsto (λ (y : G), y+x) (nhds 0) (nhds x), 
    by simpa using continuous.tendsto (continuous_translation x) 0,
  
  have inv₁ : (λ y, y-x) ∘ (λ y, y+x) = id, by {funext x, dsimp[id, (∘)], rw [add_assoc, add_right_neg], simp },
  have inv₂ : (λ y, y+x) ∘ (λ y, y-x) = id, by {funext x, dsimp[id, (∘)], simp, },
  exact eq.symm (vmap_eq_of_inverse inv₁ inv₂ lim₁ lim₂)
end
end topological_add_group

section topological_add_comm_group
universe u
variables {G : Type u} [add_comm_group G] [topological_space G] [topological_add_group G]  

def δ : G × G → G := λ p, p.2 - p.1
def Δ : filter (G × G) := principal id_rel

instance toplogical_add_group.to_uniform_space : uniform_space G := 
{ uniformity          := vmap δ (nhds 0),
  refl                := 
    begin 
      suffices : map δ Δ ≤ nhds (0: G), from map_le_iff_le_vmap.1 this,
      suffices : map δ Δ ≤ pure (0 : G), from le_trans this (pure_le_nhds 0),
      dsimp [Δ], 
      rw map_principal,
      have : (δ '' id_rel : set G) = {(0 : G)},
      { ext,
        simp [δ, id_rel],
        split; try { intro H, existsi (0 : G) } ; finish },
      finish 
    end,
  symm                := 
    begin 
      suffices : vmap δ (nhds (0 : G)) ≤ vmap prod.swap (vmap δ (nhds (0 : G))),
        from map_le_iff_le_vmap.2 this,
      suffices : vmap δ (nhds (0 : G)) ≤ vmap (δ ∘ prod.swap)  (nhds (0 : G)), 
        by simp[vmap_vmap_comp, this],
      have δ_swap : (δ ∘ prod.swap : G × G → G) = (λ p, -p) ∘ δ, by {funext, simp[δ] },
      have : vmap (δ ∘ prod.swap) (nhds (0 : G)) = vmap δ (nhds 0),
        by rw [δ_swap, ←vmap_vmap_comp, nhds_zero_symm G],
      finish
    end,
  comp                := 
    begin
      intros D H,
      rw mem_lift'_sets,
      { rcases H with ⟨U, U_nhds, U_sub⟩,
        rcases half_nhd U U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩,
        existsi δ⁻¹'V,
        have H : δ⁻¹'V ∈ (vmap δ (nhds (0 : G))).sets,
          by existsi [V, V_nhds] ; refl,
        existsi H,
        have comp_rel_sub : comp_rel (δ⁻¹'V) (δ⁻¹'V) ⊆ δ⁻¹' U,
        begin
          intros p p_comp_rel,
          rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩,
          simpa[δ] using V_sum _ _ Hz1 Hz2
        end,
        exact set.subset.trans comp_rel_sub U_sub },
      { exact monotone_comp_rel monotone_id monotone_id }
    end,
  is_open_uniformity  := 
    begin
      intro S,
      let S' := λ x, {p : G × G | p.1 = x → p.2 ∈ S},
      
      change is_open S ↔ ∀ (x : G), x ∈ S → S' x ∈ (vmap δ (nhds (0 : G))).sets,
      have := calc 
      is_open S ↔ ∀ (x : G), x ∈ S → S ∈ (nhds x).sets          : is_open_iff_mem_nhds
            ... ↔ ∀ (x : G), x ∈ S → S ∈ (vmap (λ y, y-x) (nhds (0:G))).sets : by conv in (_ ∈ _) {rw (nhds_translation x)},
      have : (∀ x ∈ S, S ∈ (vmap (λ y, y-x)  (nhds (0 : G))).sets) ↔ (∀ x ∈ S, S' x ∈ (vmap δ (nhds (0 : G))).sets),
        { split ; intros H x x_in_S ; specialize H x x_in_S;
          { rcases H with ⟨U, U_nhds, U_prop⟩,
            existsi [U, U_nhds],
            have := calc
            (λ y, y-x)⁻¹' U ⊆ S ↔ (∀ y, y-x ∈ U → y ∈ S) : set.preimage_subset_iff
            ... ↔  (∀ p : G × G, p.2-p.1 ∈ U → p.1 = x → p.2 ∈ S) : 
                                                          begin
                                                            split,
                                                            { intros H h h' h'',
                                                              apply H, cc },
                                                            { intros H y h,
                                                              specialize H (x,y),
                                                              finish }
                                                          end
            ... ↔  (∀ p : G × G, δ p ∈ U → p ∈ S' x) : by simp[δ, S' x]
            ... ↔ δ⁻¹'U ⊆ S' x : set.preimage_subset_iff,
            
            cc } },
      cc 
    end,}

lemma uniformity_eq_vmap_nhds_zero : uniformity = vmap δ (nhds (0 : G)) := rfl

instance topological_add_group_is_uniform : uniform_add_group G := 
⟨begin
  rw [uniform_continuous, uniformity_prod_eq_prod],
  apply tendsto_map',
  apply tendsto_vmap_iff.2,

  suffices : tendsto (λ (x : (G × G) × G × G), (x.1).2 - (x.1).1 - ((x.2).2 - (x.2).1))
    (filter.prod uniformity uniformity)
    (nhds 0),
  { simpa [(∘), δ] },

  suffices : tendsto (λ (x : (G × G) × G × G), (x.1).2 - (x.1).1 - ((x.2).2 - (x.2).1))
    (vmap (λ (p : (G × G) × G × G), ((p.1).2 - (p.1).1, (p.2).2 - (p.2).1))
       (filter.prod (nhds 0) (nhds 0)))
    (nhds 0),
  by simpa [(∘), δ, uniformity_eq_vmap_nhds_zero, prod_vmap_vmap_eq, -sub_eq_add_neg],
  
  conv { for (nhds _) [3] { rw [show (0:G) = 0 - 0, by simp] }},
  exact tendsto_sub (tendsto.comp tendsto_vmap tendsto_fst) (tendsto.comp tendsto_vmap tendsto_snd),
end⟩

variables {H : Type*} [add_comm_group H] [topological_space H] [topological_add_group H]  

lemma uniform_continuous_of_continuous {f : G → H} [is_add_group_hom f] (h : continuous f) : 
  uniform_continuous f := 
begin
  simp only [uniform_continuous, uniformity_eq_vmap_nhds_zero],
  rw [tendsto_iff_vmap, vmap_vmap_comp],
  
  change vmap δ (nhds 0) ≤ vmap ( λ (x : G × G), f x.2 - f x.1) (nhds 0),
  have : (λ (x : G × G), f (x.snd) - f (x.fst)) = λ (x : G × G), f (x.snd -  x.fst),
    by simp only [is_add_group_hom.sub f],
  rw [this, ←tendsto_iff_vmap],
  
  exact tendsto.comp tendsto_vmap (is_add_group_hom.zero f ▸ continuous.tendsto h (0:G))
end
end topological_add_comm_group

section topological_add_comm_group_completion
universe u
variables {α : Type*} [uniform_space α]
variables (G : Type u) [add_comm_group G] [topological_space G] [topological_add_group G]  

open uniform_space function set uniform_space.to_completion

lemma uniform_continuous_add'' [add_group α] [uniform_add_group α] :
uniform_continuous (uncurry add_semigroup.add : α × α → α) :=
by rw uncurry_def ; exact uniform_continuous_add'

noncomputable
def uncurry_add : completion G × completion G → completion G := 
  completion.map (uncurry add_semigroup.add) ∘ completion.prod


noncomputable instance : has_add (completion G) := 
  ⟨curry (uncurry_add G)⟩

instance : has_zero (completion G) := ⟨(0:G)⟩

noncomputable instance : has_neg (completion G) := ⟨completion.map (λ x, -x)⟩

variable {G}
lemma completion.add_lift (a b : G) : (a : completion G) + (b : completion G) = (a + b : G) := 
begin
  change (completion.map (uncurry add_semigroup.add) ∘ completion.prod) (↑a, ↑b) =  (to_completion G ∘ uncurry add_semigroup.add) (a, b),
  rw [completion.map.lifts uniform_continuous_add'', comp_apply, completion.prod.lift],
  refl,
  apply_instance
end


lemma completion.neg_lift (a : G) : -(a : completion G) = (-a : G) := 
begin
  rw [completion.map.lifts' uniform_continuous_neg'],
  refl,
  apply_instance
end

lemma completion.uniform_continuous_add' : uniform_continuous (uncurry_add G) := 
uniform_continuous.comp completion.prod.uc (completion.map.uniform_continuity (@uniform_continuous_add'' G _ _ _))

lemma completion.uniform_continuous_add {f g : α → completion G} (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λ x, f x + g x) := 
uniform_continuous.comp (uniform_continuous.prod_mk hf hg) completion.uniform_continuous_add'

lemma completion.continuous_add' : continuous (uncurry_add G) := 
uniform_continuous.continuous completion.uniform_continuous_add'

lemma completion.continuous_add'' : continuous (λ x : (completion G) × (completion G), x.1 + x.2) :=
begin
  change continuous (λ (x : (completion G) × (completion G)), (uncurry_add G) (x.fst, x.snd)),
  simp[completion.continuous_add']
end 
      

lemma completion.continuous_add {f g : α → completion G} (hf : continuous f) (hg : continuous g) : continuous (λ x, f x + g x) := 
continuous.comp (continuous.prod_mk hf hg) completion.continuous_add'

lemma completion.uniform_continuous_neg' : uniform_continuous (λ x : completion G, -x) := 
completion.map.uniform_continuity uniform_continuous_neg'

lemma completion.uniform_continuous_neg {f : α → completion G} (hf : uniform_continuous f) : uniform_continuous (λ x, -f x) := 
uniform_continuous.comp hf completion.uniform_continuous_neg'

lemma completion.continuous_neg' : continuous (λ x : completion G, -x) := 
uniform_continuous.continuous completion.uniform_continuous_neg'

lemma completion.continuous_neg {f : α → completion G} (hf : continuous f) : continuous (λ x, -f x) := 
continuous.comp hf completion.continuous_neg'

noncomputable
instance completion_group_str : add_comm_group (completion G) := 
begin
  let H := completion G,
  refine_struct {
    add := curry ((completion.map (function.uncurry ((+) : G → G → G))) ∘ completion.prod),
    zero := (0:G),
    neg := completion.map (λ x, -x),
  },
  { intros a b c,
    have closed : is_closed {x : H × H × H | x.1 + x.2.1 + x.2.2 = x.1 + (x.2.1 + x.2.2) }, 
    { 
      have c₁ : continuous (λ x : H × (H × H), (x.1 + x.2.1) + x.2.2), 
      { have c : continuous (λ x : H × (H × H), (x.2.1 + x.2.2) + x.1) :=
          completion.continuous_add (continuous.comp continuous_snd completion.continuous_add'') continuous_fst,
        exact continuous.comp continuous_pat_perm c },
      have c₂ : continuous (λ x : H × (H × H), x.1 + (x.2.1 + x.2.2)) := 
        completion.continuous_add continuous_fst (continuous.comp continuous_snd completion.continuous_add''),
      exact is_closed_eq c₁ c₂ },
    have := is_closed_property dense₃ closed (by {intro a, repeat { rw completion.add_lift }, rw add_assoc }),
    exact this ⟨a, b, c⟩ },
  { have closed : is_closed {x : H | 0 + x = x } := 
      is_closed_eq (completion.continuous_add continuous_const continuous_id) continuous_id,
    exact is_closed_property dense₁ closed (by {intro x, rw completion.add_lift, rw zero_add}) },
  { have closed : is_closed {x : H | x + (0:G) = x } :=
      is_closed_eq (completion.continuous_add continuous_id continuous_const) continuous_id ,
    exact is_closed_property dense₁ closed (by {intro x, rw completion.add_lift, rw add_zero}) },
  { have closed : is_closed {x : H | -x + x = (0:G)} :=
     is_closed_eq (completion.continuous_add completion.continuous_neg' continuous_id) continuous_const,
    have := is_closed_property dense₁ closed (by {intro x, rw completion.neg_lift, rw completion.add_lift, rw add_left_neg }),
    exact this },
  { intros a b,
    have closed : is_closed {x : H × H | x.1 + x.2 = x.2 + x.1 } :=
      is_closed_eq completion.continuous_add'' (continuous.comp continuous_swap completion.continuous_add''),
    have := is_closed_property dense₂ closed (by {intro a, repeat { rw completion.add_lift }, rw add_comm }),
    exact this ⟨a, b⟩ },
end

-- The following two instances seem to be necessary to short-circuit what would otherwise be class instance resolution loops
instance : topological_space (completion G) := by unfold completion ; apply_instance
instance completion_prod_top : topological_space ((completion G) × (completion G)) := by unfold completion ; apply_instance

instance completion_group_top : topological_add_group (completion G) := 
begin
  refine {..}, -- no idea why I cannot directly construct this instance
  { exact completion.continuous_add'' },
  { exact completion.continuous_neg' }
end


instance to_completion_mph : is_add_group_hom (to_completion G) := 
⟨begin
  intros a b,
  change ↑(a + b)= ↑a + ↑b,
  exact eq.symm (completion.add_lift a b)
end⟩

variables {H : Type u} [add_comm_group H] [topological_space H] [topological_add_group H] 

instance completion_extension_hom [complete_space H] [separated H] 
  {f : G → H} [is_add_group_hom f] (h : continuous f) : 
  is_add_group_hom (completion_extension f) :=
⟨begin
  
  let GG := completion G,
  let ff := completion_extension f,
  have f_uc := uniform_continuous_of_continuous h,
  have ff_c : continuous ff := completion_extension.continuity f_uc,
    
  have closed : is_closed {x : GG × GG | ff (x.1 + x.2) = ff x.1 + ff x.2 },
  { have c₀ : continuous (λ x : GG × GG, x.1 + x.2), 
      { change continuous (λ (x : GG × GG), (uncurry_add G) (x.fst, x.snd)),
        simp[completion.continuous_add'] },
    
    have c₁ : continuous (λ a : GG × GG, ff a.1) := continuous.comp continuous_fst ff_c,
    have c₂ : continuous (λ a : GG × GG, ff a.2) := continuous.comp continuous_snd ff_c,
    
    haveI t2 : t2_space H := separated_t2, -- No idea why this is needed
    exact is_closed_eq  (continuous.comp c₀ ff_c) (continuous_add c₁ c₂) },
  have eq_on_G : ∀ (a : G × G), ff (a.1 +  a.2) = ff a.1 + ff a.2,
  { rintro ⟨a, b⟩,
      dsimp[ff],
      rw completion.add_lift,
      repeat { rw ←completion_extension.lifts' f_uc },
      rw is_add_group_hom.add f },
    
  have := is_closed_property dense₂ closed eq_on_G,
  
  exact λ a b, this (a, b),
end⟩

instance completion_map_hom {f : G → H} [is_add_group_hom f] (h : continuous f) :
  is_add_group_hom (completion.map f) :=
begin
  dsimp [completion.map],
  have cont : continuous (to_completion H ∘ f) := continuous.comp h (to_completion.continuous H),
  have hom : is_add_group_hom (to_completion H ∘ f), apply_instance,
  haveI complete : complete_space (completion H) := sorry, -- dont understand why apply_instance doesn't work
  haveI sep : separated (completion H) := sorry, -- dont understand why apply_instance doesn't work
  have := completion_extension_hom cont,
  sorry -- `exact this` doesn't work, probably because of the instance nightmare above
end
end topological_add_comm_group_completion