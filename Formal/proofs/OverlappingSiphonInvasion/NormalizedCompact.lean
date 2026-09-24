import proofs.OverlappingSiphonInvasion.NormalizedSource
import proofs.OverlappingSiphonInvasion.GeneralFlow

noncomputable section
open Set
namespace OverlappingSiphonInvasion

def physicalLiftSet (ru rv rj R : ℝ) : Set LiftState :=
  normalizedEmbedding ru rv rj '' {x : State | (∀ i, 0 < x i) ∧ total x ≤ R}
def physicalLiftClosure (ru rv rj R : ℝ) : Set LiftState := closure (physicalLiftSet ru rv rj R)

theorem positive_masses (ru rv rj : ℝ) (x : State)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (hx : ∀ i, 0 < x i) :
    0 < massU ru x ∧ 0 < massV rv x ∧ 0 < massJ rj x := by
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  dsimp [massU,massV,massJ]
  exact ⟨by positivity,by positivity,by positivity⟩

theorem normalized_direction_bounds (ru rv rj : ℝ) (x : State)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (hx : ∀ i, 0 < x i) :
    ∀ i, 0 ≤ (normalizedEmbedding ru rv rj x).2 i ∧ (normalizedEmbedding ru rv rj x).2 i ≤ 1 := by
  obtain ⟨hU,hV,hJ⟩ := positive_masses ru rv rj x hru hrv hrj hx
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  intro i
  fin_cases i
  · exact ⟨(div_pos h1 hU).le,(div_le_one hU).mpr (by dsimp [massU]; nlinarith [mul_pos hru h3])⟩
  · exact ⟨(div_pos h2 hV).le,(div_le_one hV).mpr (by dsimp [massV]; nlinarith [mul_pos hrv h3])⟩
  · exact ⟨(div_pos h1 hJ).le,(div_le_one hJ).mpr (by dsimp [massJ]; nlinarith [mul_pos hrj h3])⟩
  · exact ⟨(div_pos h2 hJ).le,(div_le_one hJ).mpr (by dsimp [massJ]; nlinarith [mul_pos hrj h3])⟩

theorem normalizedEmbedding_norm_le (ru rv rj R : ℝ) (x : State)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (hx : ∀ i, 0 < x i) (hN : total x ≤ R) :
    ‖normalizedEmbedding ru rv rj x‖ ≤ max R 1 := by
  have hs := (nonnegative_norm_le_total x (fun i => (hx i).le)).trans hN
  have hb := normalized_direction_bounds ru rv rj x hru hrv hrj hx
  have hd : ‖(normalizedEmbedding ru rv rj x).2‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).2
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hb i).1]
    exact (hb i).2
  rw [Prod.norm_def]
  exact max_le (hs.trans (le_max_left _ _)) (hd.trans (le_max_right _ _))

theorem physicalLiftClosure_isCompact (ru rv rj R : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) :
    IsCompact (physicalLiftClosure ru rv rj R) := by
  have hs : physicalLiftSet ru rv rj R ⊆ Metric.closedBall (0:LiftState) (max R 1) := by
    rintro _ ⟨x,⟨hx,hN⟩,rfl⟩
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      normalizedEmbedding_norm_le ru rv rj R x hru hrv hrj hx hN
  exact (isCompact_closedBall (0:LiftState) (max R 1)).of_isClosed_subset
    isClosed_closure (closure_minimal hs (isCompact_closedBall (0:LiftState) (max R 1)).isClosed)

theorem physicalLiftClosure_norm_le (ru rv rj R : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (z : LiftState)
    (hz : z ∈ physicalLiftClosure ru rv rj R) : ‖z‖ ≤ max R 1 := by
  have hs : physicalLiftSet ru rv rj R ⊆ Metric.closedBall (0:LiftState) (max R 1) := by
    rintro _ ⟨x,⟨hx,hN⟩,rfl⟩
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      normalizedEmbedding_norm_le ru rv rj R x hru hrv hrj hx hN
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    (closure_minimal hs (isCompact_closedBall (0:LiftState) (max R 1)).isClosed) hz

theorem physicalLiftClosure_projection (ru rv rj R : ℝ) (z : LiftState)
    (hz : z ∈ physicalLiftClosure ru rv rj R) : z.1 ∈ populationBox R := by
  have hs : physicalLiftSet ru rv rj R ⊆ Prod.fst ⁻¹' populationBox R := by
    rintro _ ⟨x,⟨hx,hN⟩,rfl⟩
    exact ⟨fun i => (hx i).le,hN⟩
  have hc : IsClosed (Prod.fst ⁻¹' populationBox R : Set LiftState) :=
    (populationBox_isCompact R).isClosed.preimage continuous_fst
  exact (closure_minimal hs hc) hz

end OverlappingSiphonInvasion
