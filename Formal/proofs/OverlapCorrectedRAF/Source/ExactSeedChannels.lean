import proofs.OverlapCorrectedRAF.Source.ActualGatewayDock

namespace OverlapCorrectedRAF.Source

open RAF RAF.Polymer RAF.Concrete

/-- Embed a food molecule into a larger ambient polymer universe without
changing either its length or its binary code. -/
def liftFoodMolecule {n : Nat} (hn : 2 ≤ n) (x : Molecule 2) : Molecule n :=
  ⟨⟨x.1.val, lt_of_lt_of_le x.1.2 hn⟩, x.2⟩

@[simp] theorem molLength_liftFoodMolecule {n : Nat} (hn : 2 ≤ n)
    (x : Molecule 2) :
    molLength (liftFoodMolecule hn x) = molLength x := by
  rfl

@[simp] theorem liftFoodMolecule_code {n : Nat} (hn : 2 ≤ n)
    (x : Molecule 2) :
    (liftFoodMolecule hn x).2.val = x.2.val := by
  rfl

theorem liftFoodMolecule_injective {n : Nat} (hn : 2 ≤ n) :
    Function.Injective (liftFoodMolecule hn) := by
  intro x y hxy
  rcases x with ⟨xi, xv⟩
  rcases y with ⟨yi, yv⟩
  have hi : xi = yi := by
    apply Fin.ext
    exact congrArg (fun z : Molecule n => z.1.val) hxy
  subst yi
  have hv : xv = yv := by
    apply Fin.ext
    exact congrArg (fun z : Molecule n => z.2.val) hxy
  exact congrArg (Sigma.mk xi) hv

theorem molLength_le_two (x : Molecule 2) : molLength x ≤ 2 := by
  simp [molLength]
  omega

/-- Every intrinsic binary-food gateway is realized by a repository seed
channel once products of two food molecules fit in the ambient universe. -/
def repositoryGatewayToSeedChannel {n : Nat} (hn : 4 ≤ n)
    (g : RepositoryGateway 2) :
    {r : RepositoryChannel n // RevSeedReaction (repositoryCRS n 2) r} := by
  let u := liftFoodMolecule (by omega : 2 ≤ n) g.1.1
  let v := liftFoodMolecule (by omega : 2 ≤ n) g.1.2
  have hsum : molLength u + molLength v ≤ n := by
    have hu : molLength g.1.1 ≤ 2 := molLength_le_two g.1.1
    have hv : molLength g.1.2 ≤ 2 := molLength_le_two g.1.2
    simp only [u, v, molLength_liftFoodMolecule]
    omega
  have hcanonical :
      displayedConcat u v ≠ displayedConcat v u ∨ moleculePrecedes u v := by
    simpa [u, v, displayedConcat, moleculePrecedes] using g.2
  let r : RepositoryChannel n := ⟨(u, v), hsum, hcanonical⟩
  refine ⟨r, Or.inl ?_⟩
  intro x hx
  simp only [repositoryCRS, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simpa [repositoryCRS, binaryFood, r, u] using molLength_le_two g.1.1
  · simpa [repositoryCRS, binaryFood, r, v] using molLength_le_two g.1.2

theorem repositoryGatewayToSeedChannel_injective {n : Nat} (hn : 4 ≤ n) :
    Function.Injective (repositoryGatewayToSeedChannel hn) := by
  intro g h hgh
  apply Subtype.ext
  apply Prod.ext
  · apply liftFoodMolecule_injective (by omega : 2 ≤ n)
    exact congrArg
      (fun r : {r : RepositoryChannel n // RevSeedReaction (repositoryCRS n 2) r} =>
        r.1.1.1) hgh
  · apply liftFoodMolecule_injective (by omega : 2 ≤ n)
    exact congrArg
      (fun r : {r : RepositoryChannel n // RevSeedReaction (repositoryCRS n 2) r} =>
        r.1.1.2) hgh

/-- Exact stabilization of the source-gateway count. -/
theorem repositorySeedChannels_card_eq_34 {n : Nat} (hn : 4 ≤ n) :
    (repositorySeedChannels n 2).card = 34 := by
  apply Nat.le_antisymm (repositorySeedChannels_card_le_34 n)
  rw [← card_repository_gateway_binary_t2]
  rw [repositorySeedChannels, ← Fintype.card_subtype]
  exact Fintype.card_le_of_injective (repositoryGatewayToSeedChannel hn)
    (repositoryGatewayToSeedChannel_injective hn)

end OverlapCorrectedRAF.Source
