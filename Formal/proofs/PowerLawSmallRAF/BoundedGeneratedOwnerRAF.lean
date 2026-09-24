import proofs.PowerLawSmallRAF.SourceOwnerStage

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section

/-- A covered support generating its catalyst owners and a nonfood molecule
contains an actual RAF. Unenabled channels are discarded, never added. -/
theorem exists_source_boundedRAF_of_generated_owners {n : Nat}
    (config : SourceMoleculeFibreConfig n) (S : Finset (Reaction n))
    (H : Finset (Molecule n))
    (hcover : ∀ r ∈ S, ∃ x ∈ H, r ∈ config x)
    (hgen : ∀ x ∈ H, ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k)
    (hnew : ∃ y k, y ∉ (binaryPolymerCRS n 2).food ∧
      y ∈ revClosureAt (binaryPolymerCRS n 2) S k) :
    ∃ T : Finset (Reaction n), T ⊆ S ∧ T.card ≤ S.card ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) T := by
  classical
  let restricted : SourceMoleculeFibreConfig n := fun x => config x ∩ S
  have hcloud : H.biUnion restricted = S := by
    apply Finset.Subset.antisymm
    · intro r hr
      obtain ⟨x,_,hr⟩ := Finset.mem_biUnion.mp hr
      exact (Finset.mem_inter.mp hr).2
    · intro r hr
      obtain ⟨x,hx,hcat⟩ := hcover r hr
      exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_inter.mpr ⟨hcat,hr⟩⟩
  obtain ⟨y,ky,hyfood,hy⟩ := hnew
  let depth : Molecule n → Nat := fun x => if hx : x ∈ H then Classical.choose (hgen x hx) else 0
  have hd (x : Molecule n) (hx : x ∈ H) :
      x ∈ revClosureAt (binaryPolymerCRS n 2) S (depth x) := by
    simpa only [depth,dif_pos hx] using Classical.choose_spec (hgen x hx)
  let K := ky + ∑ x ∈ H, depth x
  let T := sourceOwnerStage restricted H K
  have hTsub : T ⊆ S := by
    intro r hr
    have hh := (Finset.mem_filter.mp hr).1
    rwa [hcloud] at hh
  have hclosure (j : Nat) (hj : j ≤ K+1) :
      revClosureAt (binaryPolymerCRS n 2) T j =
        revClosureAt (binaryPolymerCRS n 2) S j := by
    rw [revClosureAt_sourceOwnerStage_eq_of_le restricted H K j hj,hcloud]
  have hTne : T.Nonempty := by
    by_contra he
    have heq := Finset.not_nonempty_iff_eq_empty.mp he
    have hempty (k : Nat) : revClosureAt (binaryPolymerCRS n 2) T k =
        (binaryPolymerCRS n 2).food := by
      rw [heq]
      induction k with
      | zero => rfl
      | succ k ih => simpa only [revClosureAt,revClosureStep,Finset.biUnion_empty,
          Finset.union_empty] using ih
    have hyT : y ∈ revClosureAt (binaryPolymerCRS n 2) T ky := by
      rw [hclosure ky (by dsimp [K]; omega)]
      exact hy
    rw [hempty] at hyT
    exact hyfood hyT
  have howners : ∀ x ∈ H, x ∈ revClosureAt (binaryPolymerCRS n 2) (H.biUnion restricted) K := by
    intro x hx
    rw [hcloud]
    have hb : depth x ≤ ∑ z ∈ H, depth z := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
    exact revClosureAt_mono_time _ _ (by dsimp [K]; omega) (hd x hx)
  have hH : H.Nonempty := by
    obtain ⟨r,hr⟩ := hTne
    obtain ⟨x,hx,_⟩ := hcover r (hTsub hr)
    exact ⟨x,hx⟩
  have hraf := sourceOwnerScaffoldOn_isRevRAF (sourceOwnerStage_is_scaffold hH hTne howners)
  refine ⟨T,hTsub,Finset.card_le_card hTsub,hraf.1,hraf.2.1,?_⟩
  intro r hr
  obtain ⟨x,k,hx,hcat⟩ := hraf.2.2 r hr
  exact ⟨x,k,hx,(Finset.mem_inter.mp hcat).1⟩

end
end PowerLawSmallRAF
