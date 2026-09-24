import proofs.RAFQueryCompilation.ModuleFamily
import proofs.RAFQueryCompilation.LocalWorkspace

namespace RAFQueryCompilation.ModuleFamily
open RAF

theorem pair_needs {n : ℕ} (i : Fin n) (b : Bool) :
    sourceNeeds (source n) catalysis (some (i,b)) =
      {some none, some (some (i,!b))} := by
  ext x
  simp [sourceNeeds, source, catalysis]

theorem pair_successors {n : ℕ} (i : Fin n) (b : Bool) :
    sourceSuccessors (source n) catalysis (some (i,b)) = {some (i,!b)} := by
  ext r
  cases r with
  | none => simp [sourceSuccessors, source, catalysis]
  | some r =>
    rcases r with ⟨j,c⟩
    cases b <;> cases c <;> simp [sourceSuccessors, source, catalysis, eq_comm]

theorem pair_envelope {n : ℕ} (i : Fin n) :
    sourceEnvelope (source n) (sourceNeeds (source n) catalysis) (region i) =
      {none, some none, some (some (i,false)), some (some (i,true))} := by
  ext x
  simp [sourceEnvelope, region, sourceNeeds, source, catalysis]
  tauto

theorem pair_envelope_card {n : ℕ} (i : Fin n) :
    (sourceEnvelope (source n) (sourceNeeds (source n) catalysis) (region i)).card = 4 := by
  rw [pair_envelope]
  simp

end RAFQueryCompilation.ModuleFamily
