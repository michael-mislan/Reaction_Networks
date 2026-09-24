import proofs.IrrRAFEnumeration.PrivateEdges

namespace IrrRAFEnumeration

abbrev TraceWitnessVertex (k : Nat) := Fin (k + 1) × Bool

def traceLeft {k : Nat} (i : Fin (k + 1)) : TraceWitnessVertex k := (i, false)

def traceRight {k : Nat} (i : Fin (k + 1)) : TraceWitnessVertex k := (i, true)

def traceMatchingEdge {k : Nat} (i : Fin (k + 1)) :
    Finset (TraceWitnessVertex k) := {traceLeft i, traceRight i}

def traceMatchingFamily (k : Nat) :
    Finset (Finset (TraceWitnessVertex k)) :=
  Finset.univ.image traceMatchingEdge

def traceRequired (k : Nat) : Finset (TraceWitnessVertex k) :=
  Finset.univ.image traceLeft

def traceResidual (k : Nat) : Finset (TraceWitnessVertex k) :=
  Finset.univ.image traceRight

def traceWitnessFamily (k : Nat) :
    Finset (Finset (TraceWitnessVertex k)) :=
  insert (traceResidual k) (traceMatchingFamily k)

@[simp] theorem traceLeft_in_required {k : Nat} (i : Fin (k + 1)) :
    traceLeft i ∈ traceRequired k := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

@[simp] theorem traceRight_in_residual {k : Nat} (i : Fin (k + 1)) :
    traceRight i ∈ traceResidual k := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem traceRequired_inter_matchingEdge {k : Nat} (i : Fin (k + 1)) :
    traceRequired k ∩ traceMatchingEdge i = {traceLeft i} := by
  classical
  ext vertex
  rcases vertex with ⟨j, value⟩
  simp [traceRequired, traceMatchingEdge, traceLeft, traceRight]

theorem hits_traceWitnessFamily_iff {k : Nat}
    (A : Finset (TraceWitnessVertex k)) :
    Hits (traceWitnessFamily k) A ↔
      (∃ i, traceRight i ∈ A) ∧
      ∀ i, traceLeft i ∈ A ∨ traceRight i ∈ A := by
  classical
  constructor
  · intro h
    constructor
    · have hresidual := h (traceResidual k) (by simp [traceWitnessFamily])
      obtain ⟨vertex, hvertexA, hvertexResidual⟩ :=
        Finset.not_disjoint_iff.mp hresidual
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hvertexResidual
      exact ⟨i, hvertexA⟩
    · intro i
      have hedge : traceMatchingEdge i ∈ traceWitnessFamily k := by
        simp [traceWitnessFamily, traceMatchingFamily]
      obtain ⟨vertex, hvertexA, hvertexEdge⟩ :=
        Finset.not_disjoint_iff.mp (h _ hedge)
      simpa [traceMatchingEdge] using
        (show vertex = traceLeft i ∨ vertex = traceRight i by simpa [traceMatchingEdge] using hvertexEdge)
          |>.elim (fun h => Or.inl (h ▸ hvertexA)) (fun h => Or.inr (h ▸ hvertexA))
  · rintro ⟨⟨j, hj⟩, hall⟩ E hE
    rw [traceWitnessFamily, Finset.mem_insert] at hE
    rcases hE with rfl | hmatching
    · exact Finset.not_disjoint_iff.mpr ⟨traceRight j, hj,
        traceRight_in_residual j⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmatching
      rcases hall i with hi | hi
      · exact Finset.not_disjoint_iff.mpr ⟨traceLeft i, hi, by simp [traceMatchingEdge]⟩
      · exact Finset.not_disjoint_iff.mpr ⟨traceRight i, hi, by simp [traceMatchingEdge]⟩

/-- Although every required vertex has an explicit private-edge candidate,
the whole required trace extends to no minimal transversal. -/
theorem no_minimal_traceWitness_contains_required {k : Nat}
    {A : Finset (TraceWitnessVertex k)}
    (hrequired : traceRequired k ⊆ A) :
    ¬ Minimal (Hits (traceWitnessFamily k)) A := by
  classical
  intro hminimal
  obtain ⟨j, hj⟩ := (hits_traceWitnessFamily_iff A).mp hminimal.1 |>.1
  let K := A.erase (traceLeft j)
  have hK : Hits (traceWitnessFamily k) K :=
    (hits_traceWitnessFamily_iff K).mpr ⟨
      ⟨j, Finset.mem_erase.mpr ⟨by simp [traceLeft, traceRight], hj⟩⟩,
      fun i => by
        by_cases hij : i = j
        · subst i
          exact Or.inr (Finset.mem_erase.mpr
            ⟨by simp [traceLeft, traceRight], hj⟩)
        · exact Or.inl (Finset.mem_erase.mpr ⟨by
            intro heq
            exact hij (congrArg Prod.fst heq), hrequired (traceLeft_in_required i)⟩)⟩
  have hAK : A ⊆ K := hminimal.2 hK (Finset.erase_subset _ _)
  have hleftK := hAK (hrequired (traceLeft_in_required j))
  simp [K] at hleftK

/-- Every proper subcollection of the private-edge forbidden partners fails to
cover the residual edge.  Hence consistency checks of any fixed order below
the trace size accept even though the full extension is impossible. -/
theorem proper_privatePartners_not_cover_residual {k : Nat}
    (S : Finset (Fin (k + 1))) (hproper : S ≠ Finset.univ) :
    ¬ traceResidual k ⊆ S.image traceRight := by
  classical
  intro hcover
  apply hproper
  apply Finset.eq_univ_of_forall
  intro i
  have hright := hcover (traceRight_in_residual i)
  obtain ⟨j, hjS, hji⟩ := Finset.mem_image.mp hright
  have : j = i := congrArg Prod.fst hji
  simpa [this] using hjS

end IrrRAFEnumeration
