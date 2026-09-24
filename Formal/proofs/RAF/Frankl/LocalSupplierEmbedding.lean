import proofs.RAF.Frankl.LocallyRankedSupplierCore

namespace RAF.Frankl
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

omit [Fintype R] [DecidableEq R] in
theorem local_certificate_transport (Q Q' : CRS M R) (C C' : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank)
    (hU : SupplierCore Q C U)
    (hf : Q.food ⊆ Q'.food)
    (hi : ∀ r ∈ U, Q'.inputs r = Q.inputs r)
    (ho : ∀ r ∈ U, Q'.outputs r = Q.outputs r)
    (hc : ∀ x r, C x r → C' x r) :
    InternalSubstrateRank Q' U rank ∧ SupplierCore Q' C' U := by
  refine ⟨?_,hU.1,?_⟩
  · intro p hp r hr x hx hy hn
    apply hrank p hp r hr x
    · simpa only [ho p hp] using hx
    · simpa only [hi r hr] using hy
    · exact fun hx => hn (hf hx)
  · intro r hr
    obtain ⟨p,hp,hs⟩ := hU.2 r hr
    refine ⟨p,hp,?_,?_⟩
    · intro x hx
      rw [ho p hp]
      apply hs.1
      obtain ⟨hx,hn⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨by simpa only [hi r hr] using hx,fun hx => hn (hf hx)⟩
    · rcases hs.2 with ⟨x,hx,hy⟩ | ⟨x,hx,hy⟩
      · exact Or.inl ⟨x,hf hx,hc x r hy⟩
      · exact Or.inr ⟨x,by simpa only [ho p hp] using hx,hc x r hy⟩

theorem disjoint_local_cores_witnesses {I : Type*} (Q : CRS M R) (C : Catalysis M R)
    (U : I → Finset R) (rank : I → R → ℕ)
    (hrank : ∀ i, InternalSubstrateRank Q (U i) (rank i))
    (hU : ∀ i, SupplierCore Q C (U i))
    (hd : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    ∃ f : I → R, Function.Injective f ∧ ∀ i, f i ∈ U i ∧
      (fixedFamily Q C).card ≤ 2*((fixedFamily Q C).filter (fun W => f i ∈ W)).card := by
  classical
  choose f hf using fun i => local_supplier_core_exists_abundant Q C (U i) (rank i) (hrank i) (hU i)
  refine ⟨f,?_,hf⟩
  intro i j he
  by_contra hn
  exact Finset.disjoint_left.mp (hd i j hn) (hf i).1 (he.symm ▸ (hf j).1)

end RAF.Frankl
