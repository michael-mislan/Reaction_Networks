import proofs.RAFQueryCompilation.ModuleFamily

namespace RAFQueryCompilation.ModuleFamily
open RAF

def pairCertificate {n : ℕ} (i : Fin n) : List (List (Reaction n)) :=
  [[some (i,false), some (i,true)], []]

/-- A uniform certificate, independent of network size and boundary food. -/
theorem pairCertificate_accepts {n : ℕ} (i : Fin n) (food : Finset (Molecule n))
    (A : Finset (Reaction n)) (hA : A ⊆ region i) :
    ∃ L, checkPruning {source n with food := food} catalysis A (pairCertificate i) = some L := by
  have he : A = (if some (i,false) ∈ A then {some (i,false)} else ∅) ∪
      (if some (i,true) ∈ A then {some (i,true)} else ∅) := by
    ext r
    by_cases hr₁ : r = some (i,false)
    · subst r
      by_cases ha : some (i,false) ∈ A <;> by_cases hb : some (i,true) ∈ A <;>
        simp [ha, hb]
    · by_cases hr₂ : r = some (i,true)
      · subst r
        by_cases ha : some (i,false) ∈ A <;> by_cases hb : some (i,true) ∈ A <;>
          simp [ha, hb]
      · have hn : r ∉ A := by
          intro h
          have := hA h
          simp [region, hr₁, hr₂] at this
        by_cases ha : some (i,false) ∈ A <;> by_cases hb : some (i,true) ∈ A <;>
          simp [ha, hb, hn, hr₁, hr₂]
  rw [he]
  by_cases ha : some (i,false) ∈ A <;>
    by_cases hb : some (i,true) ∈ A <;>
    by_cases hh : some none ∈ food <;>
    by_cases hl : some (some (i,false)) ∈ food <;>
    by_cases hr : some (some (i,true)) ∈ food <;>
    simp [ha, hb, hh, hl, hr, pairCertificate, checkPruning, checkClosure,
      replaySchedule, scheduleStep, closureStep, Enabled, pruneWithPool, source, catalysis]

theorem pairCertificate_correct {n : ℕ} (i : Fin n) (food : Finset (Molecule n))
    (A : Finset (Reaction n)) (hA : A ⊆ region i) :
    checkPruning {source n with food := food} catalysis A (pairCertificate i) =
      some (evaluate {source n with food := food} catalysis A) := by
  obtain ⟨L,hL⟩ := pairCertificate_accepts i food A hA
  rw [← checkPruning_sound _ catalysis (pairCertificate i) A hL]
  exact hL

theorem pairCertificate_size {n : ℕ} (i : Fin n) :
    (pairCertificate i).length = 2 ∧ (pairCertificate i).flatten.length = 2 := by
  simp [pairCertificate]

end RAFQueryCompilation.ModuleFamily
