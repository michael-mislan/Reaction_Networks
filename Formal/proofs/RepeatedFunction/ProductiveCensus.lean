import proofs.RepeatedFunction.FiniteConverse

namespace RandomViability
open RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

instance productiveIncidenceDecidable {n : ℕ} (r : Reaction n) (z : Molecule n) :
    Decidable (ProductiveSingletonIncidence r z) := by
  unfold ProductiveSingletonIncidence
  infer_instance

def ProductiveLabel (n : ℕ) := {p : Reaction n × Molecule n // ProductiveSingletonIncidence p.1 p.2}
instance (n : ℕ) : Fintype (ProductiveLabel n) := inferInstanceAs (Fintype {p : Reaction n × Molecule n // ProductiveSingletonIncidence p.1 p.2})

theorem productive_labels_four : Fintype.card (ProductiveLabel 4) = 224 := by
  decide

theorem productive_label_lengths {n : ℕ} (p : ProductiveLabel n) :
    reactionProductLength p.val.1 ≤ 4 ∧ molLength p.val.2 ≤ 4 := by
  have hp := p.property
  have hl := hp.1
  have hr := hp.2.1
  have hh := reaction_length_add p.val.1
  rw [← molLength_reactionLeft,← molLength_reactionRight] at hh
  have hprod : reactionProductLength p.val.1 ≤ 4 := by omega
  refine ⟨hprod,?_⟩
  rcases hp.2.2.2 with h | h
  · omega
  · rw [h,molLength_reactionProduct]
    exact hprod

theorem molecule_eq_from_codes {n : ℕ} (u v : Molecule n)
    (hi : u.1.val = v.1.val) (hw : u.2.val = v.2.val) : u = v := by
  rcases u with ⟨ui,uw⟩
  rcases v with ⟨vi,vw⟩
  have he : ui = vi := Fin.ext hi
  subst vi
  exact congrArg (Sigma.mk ui) (Fin.ext hw)

def productiveLabelToFour {n : ℕ} (p : ProductiveLabel n) : ProductiveLabel 4 := by
  let r : Reaction 4 := ⟨⟨p.val.1.1.val,by have h := (productive_label_lengths p).1; dsimp [reactionProductLength] at h; omega⟩,p.val.1.2⟩
  let z : Molecule 4 := ⟨⟨p.val.2.1.val,by have h := (productive_label_lengths p).2; dsimp [molLength] at h; omega⟩,p.val.2.2⟩
  refine ⟨(r,z),p.property.1,p.property.2.1,p.property.2.2.1,?_⟩
  rcases p.property.2.2.2 with h | h
  · exact Or.inl h
  · right
    dsimp [z,r]
    have hi := congrArg (fun q : Molecule n => q.1.val) h
    have hw := congrArg (fun q : Molecule n => q.2.val) h
    exact molecule_eq_from_codes _ _ hi hw

theorem productive_labels_card_le (n : ℕ) : Fintype.card (ProductiveLabel n) ≤ 224 := by
  rw [← productive_labels_four]
  apply Fintype.card_le_of_injective (productiveLabelToFour (n := n))
  intro a b h
  apply Subtype.ext
  have hr := congrArg (fun p : ProductiveLabel 4 => p.val.1) h
  have hz := congrArg (fun p : ProductiveLabel 4 => p.val.2) h
  apply Prod.ext
  · have hi : a.val.1.1 = b.val.1.1 := Fin.ext (congrArg (fun r : Reaction 4 => r.1.val) hr)
    apply Sigma.ext hi
    have hword := congrArg (fun r : Reaction 4 => r.2.1.val) hr
    have hsplit := congrArg (fun r : Reaction 4 => r.2.2.val) hr
    cases a with | mk a ha =>
      cases b with | mk b hb =>
        rcases a with ⟨⟨ai,aw⟩,az⟩
        rcases b with ⟨⟨bi,bw⟩,bz⟩
        dsimp only at hi hword hsplit ⊢
        subst bi
        exact heq_of_eq (Prod.ext (Fin.ext hword) (Fin.ext hsplit))
  · have hi := congrArg (fun z : Molecule 4 => z.1.val) hz
    have hw := congrArg (fun z : Molecule 4 => z.2.val) hz
    exact molecule_eq_from_codes _ _ hi hw

theorem productive_union_iff {n : ℕ} (c : SourceMoleculeFibreConfig n) :
    (¬noProductiveSingleton c) ↔ ∃ p : ProductiveLabel n,p.val.1 ∈ c p.val.2 := by
  classical
  unfold noProductiveSingleton
  push Not
  constructor
  · rintro ⟨z,r,hs,hp⟩
    exact ⟨⟨(r,z),hp⟩,hs⟩
  · rintro ⟨p,hs⟩
    exact ⟨p.val.2,p.val.1,hs,p.property⟩

end
end RandomViability
