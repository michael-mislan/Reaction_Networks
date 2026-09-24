import proofs.RAFReactionCriticality.Main

namespace RAFReactionCriticality.TargetCuts
open RAF RAFQueryCompilation FunctionalSource
variable {R : Type*} [DecidableEq R]

def Cut (E G D : Finset R) : Prop := (D ∩ E).Nonempty ∧ (D ∩ G).Nonempty
def MinimalExternal (r : R) (E G D : Finset R) : Prop :=
  r ∉ D ∧ Cut E G D ∧ ∀ H ⊆ D, Cut E G H → D ⊆ H

theorem classification (r : R) (E G D : Finset R) (hrE : r ∈ E) (hrG : r ∈ G) :
    MinimalExternal r E G D ↔
      (∃ x ∈ E ∩ G, x ≠ r ∧ D = {x}) ∨
      (∃ x ∈ E \ G, ∃ y ∈ G \ E, D = {x,y}) := by
  classical
  constructor
  · rintro ⟨hr,hcut,hmin⟩
    obtain ⟨x,hx⟩ := hcut.1
    obtain ⟨y,hy⟩ := hcut.2
    obtain ⟨hxD,hxE⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyD,hyG⟩ := Finset.mem_inter.mp hy
    by_cases hxG : x ∈ G
    · left
      refine ⟨x,Finset.mem_inter.mpr ⟨hxE,hxG⟩,?_,?_⟩
      · intro he; subst x; exact hr hxD
      · apply Finset.Subset.antisymm
        · exact hmin {x} (by simpa using hxD) (by simp [Cut,hxE,hxG])
        · simpa using hxD
    · by_cases hyE : y ∈ E
      · left
        refine ⟨y,Finset.mem_inter.mpr ⟨hyE,hyG⟩,?_,?_⟩
        · intro he; subst y; exact hr hyD
        · apply Finset.Subset.antisymm
          · exact hmin {y} (by simpa using hyD) (by simp [Cut,hyE,hyG])
          · simpa using hyD
      · right
        refine ⟨x,Finset.mem_sdiff.mpr ⟨hxE,hxG⟩,y,Finset.mem_sdiff.mpr ⟨hyG,hyE⟩,?_⟩
        apply Finset.Subset.antisymm
        · apply hmin {x,y}
          · intro z hz
            simp only [Finset.mem_insert,Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          · exact ⟨⟨x,by simp [hxE]⟩,⟨y,by simp [hyG]⟩⟩
        · intro z hz
          simp only [Finset.mem_insert,Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
  · rintro (⟨x,hx,hxr,rfl⟩ | ⟨x,hx,y,hy,rfl⟩)
    · obtain ⟨hxE,hxG⟩ := Finset.mem_inter.mp hx
      refine ⟨by simpa [eq_comm] using hxr,by simp [Cut,hxE,hxG],?_⟩
      intro H hH hcut
      obtain ⟨t,ht⟩ := hcut.1
      have htx := Finset.mem_singleton.mp (hH (Finset.mem_inter.mp ht).1)
      subst t
      simpa using (Finset.mem_inter.mp ht).1
    · obtain ⟨hxE,hxG⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨hyG,hyE⟩ := Finset.mem_sdiff.mp hy
      refine ⟨?_,⟨⟨x,by simp [hxE]⟩,⟨y,by simp [hyG]⟩⟩,?_⟩
      · simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨fun h => hxG (h ▸ hrG),fun h => hyE (h ▸ hrE)⟩
      · intro H hH hcut
        obtain ⟨a,ha⟩ := hcut.1
        obtain ⟨b,hb⟩ := hcut.2
        have haH := (Finset.mem_inter.mp ha).1
        have hbH := (Finset.mem_inter.mp hb).1
        have hax : a = x := by
          have hh := hH haH
          simp only [Finset.mem_insert,Finset.mem_singleton] at hh
          rcases hh with h | h
          · exact h
          · subst a; exact (hyE (Finset.mem_inter.mp ha).2).elim
        have hby : b = y := by
          have hh := hH hbH
          simp only [Finset.mem_insert,Finset.mem_singleton] at hh
          rcases hh with h | h
          · subst b; exact (hxG (Finset.mem_inter.mp hb).2).elim
          · exact h
        subst a; subst b
        intro z hz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption

variable [Fintype R]
theorem loss_iff_cut (f g : R → R) (v : R) (h : ∀ r, r ≠ v → f r = g r)
    (r : R) (D : Finset R) :
    r ∉ evaluate source (fun x t => catalysts f x t ∨ catalysts g x t)
      (Finset.univ \ D) ↔ Cut (orbitSet f r) (orbitSet g r) D := by
  rw [redundant_orbit_law f g v h]
  simp only [not_or,Finset.subset_sdiff,Finset.subset_univ,true_and]
  simp [Cut,Finset.not_disjoint_iff_nonempty_inter,Finset.inter_comm]

end RAFReactionCriticality.TargetCuts
