import proofs.RAFQueryCompilation.ResidualRAF

namespace RAFQueryCompilation
open RAF RAF.Frankl

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Generation ranks constrain reactant witnesses; catalytic witnesses may be cyclic. -/
def RankedSupport (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (parents : R → Finset R) (rank : R → ℕ) : Prop :=
  (∀ r ∈ S, ∀ x ∈ Q.inputs r, x ∈ Q.food ∨
    ∃ p ∈ S, p ∈ parents r ∧ rank p < rank r ∧ x ∈ Q.outputs p) ∧
  (∀ r ∈ S, ∃ x ∈ cats r, x ∈ Q.food ∨
    ∃ p ∈ S, p ∈ parents r ∧ x ∈ Q.outputs p)

instance instDecidableRankedSupport (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (parents : R → Finset R) (rank : R → ℕ) : Decidable (RankedSupport Q cats S parents rank) := by
  unfold RankedSupport
  infer_instance

def checkRankedSupport (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (parents : R → Finset R) (rank : R → ℕ) : Bool :=
  decide (RankedSupport Q cats S parents rank)

theorem checkRankedSupport_sound (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (parents : R → Finset R) (rank : R → ℕ)
    (h : checkRankedSupport Q cats S parents rank = true) :
    RankedSupport Q cats S parents rank := of_decide_eq_true h

variable [Fintype M]

/-- A subset closed under the selected witnesses remains supported and food-generated. -/
theorem ranked_retained_fixed (Q : CRS M R) (cats : R → Finset M) (S O : Finset R)
    (parents : R → Finset R) (rank : R → ℕ)
    (hw : RankedSupport Q cats S parents rank) (hos : O ⊆ S)
    (closed : ∀ r ∈ O, parents r ∩ S ⊆ O) :
    prune Q (fun x r => x ∈ cats r) O = O := by
  have generated : ∀ k, ∀ r ∈ O, rank r = k → Q.inputs r ⊆ finiteClosure Q O := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro r hr hk x hx
      rcases hw.1 r (hos hr) x hx with hf | ⟨p, hp, hparent, hlt, hout⟩
      · exact food_subset_finiteClosure Q O hf
      · have hpO := closed r hr (Finset.mem_inter.mpr ⟨hparent, hp⟩)
        exact outputs_subset_finiteClosure Q O hpO
          (ih (rank p) (by omega) p hpO rfl) hout
  apply Finset.Subset.antisymm (prune_subset Q (fun x r => x ∈ cats r) O)
  intro r hr
  apply (mem_prune Q (fun x r => x ∈ cats r) O r).mpr
  refine ⟨hr, (supported_iff_finite Q (fun x r => x ∈ cats r) O r).mpr ⟨
    generated (rank r) r hr rfl, ?_⟩⟩
  obtain ⟨x, hc, hx⟩ := hw.2 r (hos hr)
  refine ⟨x, ?_, hc⟩
  rcases hx with hf | ⟨p, hp, hparent, hout⟩
  · exact food_subset_finiteClosure Q O hf
  · have hpO := closed r hr (Finset.mem_inter.mpr ⟨hparent, hp⟩)
    exact outputs_subset_finiteClosure Q O hpO (generated (rank p) p hpO rfl) hout

/-- Deletion monotonicity supplies the upper bound; selected witnesses retain the outside.
No independence from every possible producer is required. -/
theorem ranked_deletion_localization (Q : CRS M R) (cats : R → Finset M)
    (A D E : Finset R) (parents : R → Finset R) (rank : R → ℕ)
    (hw : RankedSupport Q cats (evaluate Q (fun x r => x ∈ cats r) A) parents rank)
    (hd : D ⊆ E)
    (closed : ∀ r ∈ evaluate Q (fun x r => x ∈ cats r) A \ E,
      parents r ∩ evaluate Q (fun x r => x ∈ cats r) A ⊆
        evaluate Q (fun x r => x ∈ cats r) A \ E) :
    evaluate Q (fun x r => x ∈ cats r) (A \ D) =
      (evaluate Q (fun x r => x ∈ cats r) A \ E) ∪
      evaluate (residualSource Q (evaluate Q (fun x r => x ∈ cats r) A \ E))
        (fun x r => x ∈ cats r) ((evaluate Q (fun x r => x ∈ cats r) A \ D) ∩ E) := by
  let S := evaluate Q (fun x r => x ∈ cats r) A
  have hs : S ⊆ A := evaluate_subset Q (fun x r => x ∈ cats r) A
  apply evaluate_residual Q (fun x r => x ∈ cats r) (A \ D) (S \ E) ((S \ D) ∩ E)
  · exact ranked_retained_fixed Q cats S (S \ E) parents rank hw Finset.sdiff_subset closed
  · intro r hr
    obtain ⟨hrS, hrE⟩ := Finset.mem_sdiff.mp hr
    exact Finset.mem_sdiff.mpr ⟨hs hrS, fun h => hrE (hd h)⟩
  · intro r hr
    obtain ⟨hrS, hrD⟩ := Finset.mem_sdiff.mp (Finset.mem_inter.mp hr).1
    exact Finset.mem_sdiff.mpr ⟨hs hrS, hrD⟩
  · intro r hr
    have hrS : r ∈ S := evaluate_mono Q (fun x r => x ∈ cats r) Finset.sdiff_subset hr
    have hrD := (Finset.mem_sdiff.mp (evaluate_subset Q (fun x r => x ∈ cats r) (A \ D) hr)).2
    by_cases he : r ∈ E
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hrS,hrD⟩,he⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hrS,he⟩)

end RAFQueryCompilation
