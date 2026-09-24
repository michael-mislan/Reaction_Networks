import proofs.IrrRAFEnumeration.FiniteDuality

namespace IrrRAFEnumeration

def bipLeft (k : Nat) : Finset (Bool × Fin k) :=
  Finset.univ.image fun i => (false, i)

def bipRight (k : Nat) : Finset (Bool × Fin k) :=
  Finset.univ.image fun i => (true, i)

def bipEdge {k : Nat} (i j : Fin k) : Finset (Bool × Fin k) :=
  {(false, i), (true, j)}

def completeBipartiteFamily (k : Nat) :
    Finset (Finset (Bool × Fin k)) :=
  (Finset.univ ×ˢ Finset.univ).image fun ij => bipEdge ij.1 ij.2

@[simp] theorem mem_bipLeft {k : Nat} (x : Bool × Fin k) :
    x ∈ bipLeft k ↔ x.1 = false := by
  constructor
  · intro hx
    obtain ⟨i, -, hix⟩ := Finset.mem_image.mp hx
    simp [← hix]
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨x.2, Finset.mem_univ _, by
      apply Prod.ext
      · exact hx.symm
      · rfl⟩

@[simp] theorem mem_bipRight {k : Nat} (x : Bool × Fin k) :
    x ∈ bipRight k ↔ x.1 = true := by
  constructor
  · intro hx
    obtain ⟨i, -, hix⟩ := Finset.mem_image.mp hx
    simp [← hix]
  · intro hx
    apply Finset.mem_image.mpr
    exact ⟨x.2, Finset.mem_univ _, by
      apply Prod.ext
      · exact hx.symm
      · rfl⟩

theorem bipEdge_mem {k : Nat} (i j : Fin k) :
    bipEdge i j ∈ completeBipartiteFamily k := by
  apply Finset.mem_image.mpr
  exact ⟨(i, j), by simp, rfl⟩

/-- Every left-shore element has a distinct diagonal private edge whose
outside repair is its matching right-shore element. -/
theorem bipDiagonal_private_repair {k : Nat} (i : Fin k) :
    bipEdge i i ∈ completeBipartiteFamily k ∧
      bipEdge i i ∩ bipLeft k = {(false, i)} ∧
      (true, i) ∈ bipEdge i i := by
  refine ⟨bipEdge_mem i i, ?_, by simp [bipEdge]⟩
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton, mem_bipLeft]
  constructor
  · rintro ⟨hx, hleft⟩
    simp only [bipEdge, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rfl
    · simp at hleft
  · rintro rfl
    simp [bipEdge]

theorem bipDiagonal_repair_injective {k : Nat} :
    Function.Injective (fun i : Fin k => (true, i)) := by
  intro i j hij
  exact congrArg Prod.snd hij

/-- A set hits every edge of the complete bipartite graph exactly when it
contains one whole shore. -/
theorem hits_completeBipartite_iff {k : Nat} (T : Finset (Bool × Fin k)) :
    Hits (completeBipartiteFamily k) T ↔
      bipLeft k ⊆ T ∨ bipRight k ⊆ T := by
  constructor
  · intro hT
    by_contra hneither
    push Not at hneither
    obtain ⟨xl, hxlL, hxlT⟩ := Finset.not_subset.mp hneither.1
    obtain ⟨xr, hxrR, hxrT⟩ := Finset.not_subset.mp hneither.2
    have hxl : xl = (false, xl.2) := by
      apply Prod.ext
      · simpa using (mem_bipLeft xl).mp hxlL
      · rfl
    have hxr : xr = (true, xr.2) := by
      apply Prod.ext
      · simpa using (mem_bipRight xr).mp hxrR
      · rfl
    have hhit := hT (bipEdge xl.2 xr.2) (bipEdge_mem xl.2 xr.2)
    apply hhit
    rw [Finset.disjoint_left]
    intro x hxT hxEdge
    simp only [bipEdge, Finset.mem_insert, Finset.mem_singleton] at hxEdge
    rcases hxEdge with rfl | rfl
    · exact hxlT (hxl.symm ▸ hxT)
    · exact hxrT (hxr.symm ▸ hxT)
  · rintro (hleft | hright) E hE
    · obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp hE
      exact Finset.not_disjoint_iff.mpr
        ⟨(false, i), hleft (by simp [bipLeft]), by simp [bipEdge]⟩
    · obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp hE
      exact Finset.not_disjoint_iff.mpr
        ⟨(true, j), hright (by simp [bipRight]), by simp [bipEdge]⟩

theorem bipLeft_minimal {k : Nat} (hk : 0 < k) :
    Minimal (Hits (completeBipartiteFamily k)) (bipLeft k) := by
  refine ⟨(hits_completeBipartite_iff _).mpr (Or.inl Finset.Subset.rfl), ?_⟩
  intro B hB hBL
  rcases (hits_completeBipartite_iff B).mp hB with hLB | hRB
  · exact hLB
  · let i : Fin k := ⟨0, hk⟩
    have hiB : (true, i) ∈ B := hRB (by simp [bipRight])
    have hiL := hBL hiB
    simp at hiL

theorem bipRight_minimal {k : Nat} (hk : 0 < k) :
    Minimal (Hits (completeBipartiteFamily k)) (bipRight k) := by
  refine ⟨(hits_completeBipartite_iff _).mpr (Or.inr Finset.Subset.rfl), ?_⟩
  intro B hB hBR
  rcases (hits_completeBipartite_iff B).mp hB with hLB | hRB
  · let i : Fin k := ⟨0, hk⟩
    have hiB : (false, i) ∈ B := hLB (by simp [bipLeft])
    have hiR := hBR hiB
    simp at hiR
  · exact hRB

theorem completeBipartite_blocker_eq {k : Nat} (hk : 0 < k) :
    blocker (completeBipartiteFamily k) = {bipLeft k, bipRight k} := by
  classical
  ext T
  rw [mem_blocker]
  constructor
  · intro hT
    rcases (hits_completeBipartite_iff T).mp hT.1 with hL | hR
    · have hTL : T ⊆ bipLeft k :=
        hT.2 (bipLeft_minimal hk).1 hL
      have : T = bipLeft k := Finset.Subset.antisymm hTL hL
      simp [this]
    · have hTR : T ⊆ bipRight k :=
        hT.2 (bipRight_minimal hk).1 hR
      have : T = bipRight k := Finset.Subset.antisymm hTR hR
      simp [this]
  · intro hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact bipLeft_minimal hk
    · exact bipRight_minimal hk

theorem bipEdge_injective {k : Nat} :
    Function.Injective (fun ij : Fin k × Fin k => bipEdge ij.1 ij.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hleft := Finset.ext_iff.mp h (false, i)
  have hright := Finset.ext_iff.mp h (true, j)
  simp [bipEdge] at hleft hright
  exact Prod.ext hleft hright

/-- The obstruction has quadratic input size. -/
theorem completeBipartiteFamily_card (k : Nat) :
    (completeBipartiteFamily k).card = k * k := by
  classical
  rw [completeBipartiteFamily,
    Finset.card_image_iff.mpr fun a _ b _ h => bipEdge_injective h]
  simp

/-- Yet it has exactly two minimal transversals for every nontrivial size. -/
theorem completeBipartite_blocker_card {k : Nat} (hk : 0 < k) :
    (blocker (completeBipartiteFamily k)).card = 2 := by
  rw [completeBipartite_blocker_eq hk]
  have hne : bipLeft k ≠ bipRight k := by
    intro h
    let i : Fin k := ⟨0, hk⟩
    have hi : (false, i) ∈ bipLeft k := by simp
    rw [h] at hi
    simp at hi
  simp [hne]

end IrrRAFEnumeration
