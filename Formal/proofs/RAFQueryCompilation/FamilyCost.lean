import proofs.RAFQueryCompilation.FamilyIndex
import proofs.RAFQueryCompilation.FamilyCertificate
import proofs.RAFQueryCompilation.ChargedLocal

namespace RAFQueryCompilation.ModuleFamily
open RAF

def familyCats {n : ℕ} (r : Reaction n) : Finset (Molecule n) :=
  {match r with | none => none | some (i,b) => some (some (i,!b))}

theorem familyCats_correct {n : ℕ} (r : Reaction n) (x : Molecule n) :
    x ∈ familyCats r ↔ catalysis x r := by
  cases r with
  | none => simp [familyCats, catalysis]
  | some r => rcases r with ⟨i,b⟩; simp [familyCats, catalysis]

theorem pair_region_charge {n : ℕ} (i : Fin n) (D : Finset (Reaction n))
    (hd : D ⊆ region i) :
    regionCharge (sourceSuccessors (source n) catalysis) D (region i) ≤ 19 := by
  have hc := Finset.card_le_card hd
  rw [region_card] at hc
  simp only [regionCharge, region_card]
  have hs : (∑ r ∈ region i, (sourceSuccessors (source n) catalysis r).card) = 2 := by
    simp [region, pair_successors]
  rw [hs]
  omega

theorem pair_boundary_charge {n : ℕ} (i : Fin n) :
    boundaryCharge (source n) (sourceNeeds (source n) catalysis) (region i) = 155 := by
  have hn : (∑ r ∈ region i, (sourceNeeds (source n) catalysis r).card) = 4 := by
    simp [region, pair_needs]
  have ho : (∑ r ∈ region i, ((source n).outputs r).card) = 2 := by
    simp [region, source]
  simp only [boundaryCharge, hn, ho, region_card]
  simp [source]

theorem pair_region_accepts {n : ℕ} (i : Fin n) (D : Finset (Reaction n))
    (hd : D ⊆ region i) :
    checkRegion (sourceSuccessors (source n) catalysis) D (region i) = true := by
  simp only [checkRegion, decide_eq_true_eq]
  refine ⟨hd, ?_⟩
  intro r hr s hs
  simp only [region, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with hr | hr <;> subst r <;> rw [pair_successors] at hs <;>
    simp only [Finset.mem_singleton] at hs <;> subst s <;> simp [region]

theorem pair_local_answer {n : ℕ} (i : Fin n) (D : Finset (Reaction n))
    (hd : D ⊆ region i) (oldMask availableMask : Reaction n → Bool)
    (counts : Molecule n → ℕ) :
    (chargedLocal (source n) familyCats (sourceSuccessors (source n) catalysis)
      (sourceNeeds (source n) catalysis) oldMask availableMask D (region i) counts
      (pairCertificate i)).1 =
    some (evaluate (withFood (source n)
      (maskFood (source n) (sourceNeeds (source n) catalysis) (region i) oldMask counts))
      catalysis (maskRegion (region i) availableMask)) := by
  rw [chargedLocal_refines]
  have he : (fun x r => x ∈ familyCats (n := n) r) = catalysis := by
    funext x r
    exact propext (familyCats_correct r x)
  simp only [he]
  unfold checkMaskedLocal
  rw [pair_region_accepts i D hd]
  exact pairCertificate_correct i _ _ (Finset.filter_subset _ _)

/-- Uniform local consumer bound in the declared comparison/copy charge model. -/
theorem pair_local_charge {n : ℕ} (i : Fin n) (D : Finset (Reaction n))
    (hd : D ⊆ region i) (oldMask availableMask : Reaction n → Bool)
    (counts : Molecule n → ℕ) :
    (chargedLocal (source n) familyCats (sourceSuccessors (source n) catalysis)
      (sourceNeeds (source n) catalysis) oldMask availableMask D (region i) counts
      (pairCertificate i)).2 ≤ 818 := by
  have hb := chargedLocal_bound (source n) familyCats
    (sourceSuccessors (source n) catalysis) (sourceNeeds (source n) catalysis)
    oldMask availableMask D (region i) counts (pairCertificate i) 1 1 1
    (by intro r _; simp [source]) (by intro r _; simp [source])
    (by intro r _; simp [familyCats])
  have hg := pair_region_charge i D hd
  rw [pair_boundary_charge, pair_envelope_card, region_card] at hb
  simp only [pairCertificate, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.length_cons, List.length_nil, replayCap, pruningRoundCap] at hb
  change (chargedLocal (source n) familyCats (sourceSuccessors (source n) catalysis)
    (sourceNeeds (source n) catalysis) oldMask availableMask D (region i) counts
    [[some (i,false), some (i,true)], []]).2 ≤ 818
  omega

end RAFQueryCompilation.ModuleFamily
