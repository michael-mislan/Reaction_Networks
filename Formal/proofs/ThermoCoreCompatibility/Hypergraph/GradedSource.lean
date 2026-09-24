import proofs.ThermoCoreCompatibility.Hypergraph.TriangleSource
import proofs.ThermoCoreCompatibility.Hypergraph.GradedGluing

namespace ThermoCoreCompatibility.Hypergraph

open scoped BigOperators

structure PairAssembly (V E : Type*) where
  src : E → V
  dst : E → V
  distinct : ∀ e, src e ≠ dst e

namespace PairAssembly

variable {V E : Type*} [DecidableEq V] [DecidableEq E] (G : PairAssembly V E)

def network : ReversibleCRN V (E × Bool) where
  reactant
    | (e,false) => atom (G.src e) 1
    | (e,true) => atom (G.dst e) 1
  product
    | (e,false) => atom (G.dst e) 1
    | (e,true) => atom (G.src e) 2
  barrier := fun _ => 1
  barrier_pos := fun _ => by norm_num

def motif (e : E) : Motif G.network where
  species := {G.src e,G.dst e}
  reactions := {(e,false),(e,true)}

theorem productive_iff (e : E) (v : E × Bool → ℝ) :
    (G.motif e).Productive v ↔ v (e,false) < 2*v (e,true) ∧ v (e,true) < v (e,false) := by
  simp [Motif.Productive,motif,network,ReversibleCRN.stoich,atom,G.distinct e,Ne.symm (G.distinct e)]

theorem current_productive_iff [Fintype V] (e : E) (z : V → ℝ) :
    (G.motif e).Productive (G.network.current z) ↔ Ring.Productive (z (G.src e)) (z (G.dst e)) := by
  rw [G.productive_iff]
  simp [ReversibleCRN.current,network,activity_atom,Ring.Productive]

private theorem endpoint {ss : Finset V} {i : V} {k : ℕ}
    (h : ∃ t ∈ ss, 0 < atom i k t) : i ∈ ss := by
  obtain ⟨t,ht,h⟩ := h
  unfold atom at h
  split_ifs at h with he
  · simpa [he] using ht
  · omega

private theorem sum_pair {α : Type*} [DecidableEq α] (s : Finset α) (a b : α)
    (hab : a ≠ b) (hs : s ⊆ {a,b}) (f : α → ℝ) :
    ∑ r ∈ s, f r = (if a ∈ s then f a else 0)+(if b ∈ s then f b else 0) := by
  calc
    _ = ∑ r ∈ s, (if r ∈ s then f r else 0) := by simp
    _ = ∑ r ∈ ({a,b} : Finset α), (if r ∈ s then f r else 0) :=
      Finset.sum_subset hs (by intro r _ hr; simp [hr])
    _ = _ := by rw [Finset.sum_insert (by simp [hab]),Finset.sum_singleton]

theorem source_isPAC (e : E) : (G.motif e).IsPAC := by
  have hne := G.distinct e
  have hside : (G.motif e).SideIncident := by
    refine ⟨⟨G.src e,by simp [motif]⟩,⟨(e,false),by simp [motif]⟩,?_⟩
    intro r hr
    simp only [motif,Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨G.src e,by simp [motif],by simp [network,atom]⟩,
        ⟨G.dst e,by simp [motif],by simp [network,atom]⟩⟩
    · exact ⟨⟨G.dst e,by simp [motif],by simp [network,atom]⟩,
        ⟨G.src e,by simp [motif],by simp [network,atom]⟩⟩
  constructor
  · refine ⟨hside,(fun r => if r.2 then 3 else 4),?_⟩
    rw [G.productive_iff]
    norm_num
  · intro small hstrict hauto
    obtain ⟨hs,v,hv⟩ := hauto
    have hend : G.src e ∈ small.species ∧ G.dst e ∈ small.species := by
      obtain ⟨r,hr⟩ := hs.2.1
      have hmem := hstrict.2.1 hr
      obtain ⟨hl,hu⟩ := hs.2.2 r hr
      simp only [motif,Finset.mem_insert,Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact ⟨endpoint hl,endpoint hu⟩
      · exact ⟨endpoint hu,endpoint hl⟩
    have hx := hv (G.src e) hend.1
    have hy := hv (G.dst e) hend.2
    rw [sum_pair small.reactions (e,false) (e,true) (by simp) hstrict.2.1] at hx hy
    simp only [network,ReversibleCRN.stoich,atom,if_neg hne,if_neg (Ne.symm hne)] at hx hy
    norm_num at hx hy
    have hr₀ : (e,false) ∈ small.reactions := by
      by_contra hh
      simp [hh] at hx hy
      split_ifs at hx hy <;> linarith
    have hr₁ : (e,true) ∈ small.reactions := by
      by_contra hh
      simp [hh] at hx hy
      split_ifs at hx hy <;> linarith
    have hr : small.reactions = (G.motif e).reactions := by
      apply Finset.Subset.antisymm hstrict.2.1
      simp [motif,Finset.insert_subset_iff,hr₀,hr₁]
    have hsp : small.species = (G.motif e).species := by
      apply Finset.Subset.antisymm hstrict.1
      simp [motif,Finset.insert_subset_iff,hend]
    exact hstrict.2.2.elim (fun h => h hsp) (fun h => h hr)

/-- Common-state gluing for any bounded rank-one incidence structure.
All reactions use the literal source network, not independent interface copies. -/
theorem graded_source_compatible [Fintype V] (rank : V → ℕ) (height : ℕ)
    (hbound : ∀ v, rank v ≤ height) (hedge : ∀ e, rank (G.dst e) = rank (G.src e)+1) :
    ∃ z : V → ℝ, (∀ v, 9/10 ≤ z v ∧ z v ≤ 1) ∧
      (∀ e, (G.motif e).IsPAC ∧ (G.motif e).Productive (G.network.current z)) ∧
      ∀ r, 0 < G.network.current z r := by
  obtain ⟨z,hbox,hz⟩ := Graded.graded_common_state G.src G.dst rank height hbound hedge
  refine ⟨z,hbox,fun e => ⟨G.source_isPAC e,(G.current_productive_iff e z).2 (hz e)⟩,?_⟩
  intro r
  rcases r with ⟨e,(_|_)⟩ <;>
    simp only [ReversibleCRN.current,network,activity_atom,pow_one,one_mul]
  · exact sub_pos.mpr (Ring.productive_decreases (hz e))
  · obtain ⟨h₁,h₂⟩ := hz e
    linarith

end PairAssembly
end ThermoCoreCompatibility.Hypergraph
