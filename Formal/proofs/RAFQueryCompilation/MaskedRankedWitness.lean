import proofs.RAFQueryCompilation.RankedWitness

namespace RAFQueryCompilation
open RAF

/-- Search the supplied parent rows and authenticate membership by the baseline mask. -/
def checkMaskedRankedSupport {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (mask : Fin m → Bool)
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ) : Bool :=
  (List.finRange m).all fun r => if mask r then
    (((Q.inputs r).sort (· ≤ ·)).all fun x => decide (x ∈ Q.food) ||
      ((parents r).sort (· ≤ ·)).any fun p => mask p && decide (rank p < rank r) && decide (x ∈ Q.outputs p)) &&
    (((cats r).sort (· ≤ ·)).any fun x => decide (x ∈ Q.food) ||
      ((parents r).sort (· ≤ ·)).any fun p => mask p && decide (x ∈ Q.outputs p))
    else true

theorem checkMaskedRankedSupport_sound {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (mask : Fin m → Bool) (S : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ)
    (hm : ∀ r, mask r = true ↔ r ∈ S)
    (h : checkMaskedRankedSupport Q cats mask parents rank = true) :
    checkRankedSupport Q cats S parents rank = true := by
  simp only [checkMaskedRankedSupport, List.all_eq_true] at h
  change decide (RankedSupport Q cats S parents rank) = true
  apply decide_eq_true
  constructor
  · intro r hr x hx
    have hrow := h r (by simp)
    have hrMask := (hm r).mpr hr
    simp [hrMask, List.all_eq_true, List.any_eq_true] at hrow
    rcases hrow.1 x hx with hf | ⟨p, hp, ⟨hmask, hlt⟩, hout⟩
    · exact Or.inl hf
    · exact Or.inr ⟨p, (hm p).mp hmask, hp, hlt, hout⟩
  · intro r hr
    have hrow := h r (by simp)
    have hrMask := (hm r).mpr hr
    simp [hrMask, List.all_eq_true, List.any_eq_true] at hrow
    obtain ⟨x, hx, hs⟩ := hrow.2
    refine ⟨x, hx, ?_⟩
    rcases hs with hf | ⟨p, hp, hmask, hout⟩
    · exact Or.inl hf
    · exact Or.inr ⟨p, (hm p).mp hmask, hp, hout⟩

end RAFQueryCompilation
