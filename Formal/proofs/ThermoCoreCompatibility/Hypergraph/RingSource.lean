import proofs.ThermoCoreCompatibility.Hypergraph.TriangleSource
import proofs.ThermoCoreCompatibility.Hypergraph.RingHyperedge

namespace ThermoCoreCompatibility.Hypergraph.Ring

open scoped BigOperators

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

def network : ReversibleCRN (ZMod n) (ZMod n × Bool) where
  reactant
    | (i,false) => atom i 1
    | (i,true) => atom (i+1) 1
  product
    | (i,false) => atom (i+1) 1
    | (i,true) => atom i 2
  barrier := fun _ => 1
  barrier_pos := fun _ => by norm_num

def motif (i : ZMod n) : Motif (network n) where
  species := {i,i+1}
  reactions := {(i,false),(i,true)}

omit [NeZero n] in
theorem distinct (i : ZMod n) : i ≠ i+1 := by
  intro h
  have hh : (1 : ZMod n) = 0 := by linear_combination -h
  exact one_ne_zero hh

omit [NeZero n] in
theorem productive_iff (i : ZMod n) (v : ZMod n × Bool → ℝ) :
    (motif n i).Productive v ↔ v (i,false) < 2*v (i,true) ∧ v (i,true) < v (i,false) := by
  have h := distinct n i
  simp [Motif.Productive,motif,network,ReversibleCRN.stoich,atom,h,Ne.symm h]

theorem current_productive_iff (i : ZMod n) (z : ZMod n → ℝ) :
    (motif n i).Productive ((network n).current z) ↔ Productive (z i) (z (i+1)) := by
  rw [productive_iff]
  simp [ReversibleCRN.current,network,activity_atom,Productive]

omit [NeZero n] [Fact (1 < n)] in
private theorem endpoint {ss : Finset (ZMod n)} {i : ZMod n} {k : ℕ}
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

omit [NeZero n] in
theorem source_isPAC (i : ZMod n) : (motif n i).IsPAC := by
  have hne := distinct n i
  have hside : (motif n i).SideIncident := by
    refine ⟨⟨i,by simp [motif]⟩,⟨(i,false),by simp [motif]⟩,?_⟩
    intro r hr
    simp only [motif,Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨i,by simp [motif],by simp [network,atom]⟩,
        ⟨i+1,by simp [motif],by simp [network,atom]⟩⟩
    · exact ⟨⟨i+1,by simp [motif],by simp [network,atom]⟩,
        ⟨i,by simp [motif],by simp [network,atom]⟩⟩
  constructor
  · refine ⟨hside,(fun r => if r.2 then 3 else 4),?_⟩
    rw [productive_iff]
    norm_num
  · intro small hstrict hauto
    obtain ⟨hs,v,hv⟩ := hauto
    have hend : i ∈ small.species ∧ i+1 ∈ small.species := by
      obtain ⟨r,hr⟩ := hs.2.1
      have hmem := hstrict.2.1 hr
      obtain ⟨hl,hu⟩ := hs.2.2 r hr
      simp only [motif,Finset.mem_insert,Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact ⟨endpoint n hl,endpoint n hu⟩
      · exact ⟨endpoint n hu,endpoint n hl⟩
    have hx := hv i hend.1
    have hy := hv (i+1) hend.2
    rw [sum_pair small.reactions (i,false) (i,true) (by simp) hstrict.2.1] at hx hy
    simp only [network,ReversibleCRN.stoich,atom,if_neg hne,if_neg (Ne.symm hne)] at hx hy
    norm_num at hx hy
    have hr₀ : (i,false) ∈ small.reactions := by
      by_contra hh
      simp [hh] at hx hy
      split_ifs at hx hy <;> linarith
    have hr₁ : (i,true) ∈ small.reactions := by
      by_contra hh
      simp [hh] at hx hy
      split_ifs at hx hy <;> linarith
    have hr : small.reactions = (motif n i).reactions := by
      apply Finset.Subset.antisymm hstrict.2.1
      simp [motif,Finset.insert_subset_iff,hr₀,hr₁]
    have hsp : small.species = (motif n i).species := by
      apply Finset.Subset.antisymm hstrict.1
      simp [motif,Finset.insert_subset_iff,hend]
    exact hstrict.2.2.elim (fun h => h hsp) (fun h => h hr)

def Compatible (F : Set (ZMod n)) : Prop :=
  ∃ z : ZMod n → ℝ, (∀ i, 9/10 ≤ z i ∧ z i ≤ 1) ∧
    ∀ i ∈ F, (motif n i).Productive ((network n).current z) ∧
      ∀ r ∈ (motif n i).reactions, 0 < (network n).current z r

theorem source_full_incompatible : ¬ Compatible n Set.univ := by
  rintro ⟨z,_,hz⟩
  apply full_incompatible n
  exact ⟨z,fun i => (current_productive_iff n i z).1 (hz i (Set.mem_univ i)).1⟩

theorem source_deletion (j : ZMod n) : Compatible n {i | i ≠ j} := by
  have hn : 2 ≤ n := by have := Fact.out (p := 1 < n); omega
  obtain ⟨z,hbox,hz⟩ := deletion_witness hn j
  refine ⟨z,hbox,?_⟩
  intro i hi
  have hp := hz i hi
  refine ⟨(current_productive_iff n i z).2 hp,?_⟩
  intro r hr
  simp only [motif,Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with rfl | rfl <;>
    simp only [ReversibleCRN.current,network,activity_atom,pow_one,one_mul]
  · exact sub_pos.mpr (productive_decreases hp)
  · obtain ⟨h₁,h₂⟩ := hp
    linarith

end ThermoCoreCompatibility.Hypergraph.Ring
