import proofs.AssayInformation.RescueCertificates

noncomputable section
namespace AssayInformation
open DiagnosticWindows FiniteCopy

/-- Occupied loaded reactions that have hit; zero-load hits are subtracted. -/
def occupiedHit (t : NNReal) : ℝ := 1 - miss5 t - Real.exp (-4) * blank5 t

theorem blank5_nonneg (t : NNReal) : 0 ≤ blank5 t := by
  have h := kernel5.poissonized_event_bounds ((5/2)*t) {x : Fin 6 | x ≠ 5} 0
  rw [← uncalled_indicator] at h
  unfold blank5
  linarith [h.2]

theorem occupiedHit_seven : 96743/100000 < occupiedHit 7 := by
  obtain ⟨hb,hm,he⟩ := rescue_source_bounds
  have hb0 := blank5_nonneg 7
  have hp := Real.exp_pos (-4)
  unfold occupiedHit
  nlinarith [mul_nonneg (sub_nonneg.mpr he.le) hb0,
    mul_pos (by norm_num : (0:ℝ) < 19/1000) (sub_pos.mpr hb)]

/-- Explicit conditional-channel premises; no independence of marker and time.
The source probabilities and numerical enclosures are proved, not assumed. -/
theorem identity_rescue (jointBlank jointMiss : ℝ)
    (hblank : jointBlank ≤ (1/100) * blank5 7)
    (hmiss : jointMiss ≤ 1 - (99/100) * occupiedHit 7) :
    jointBlank < 3/10000 ∧ jointMiss < 422443/10000000 := by
  constructor
  · linarith [rescue_source_bounds.1]
  · linarith [occupiedHit_seven]

theorem rescue_against_deadlines (jointBlank jointMiss : ℝ)
    (hblank : jointBlank ≤ (1/100) * blank5 7)
    (hmiss : jointMiss ≤ 1 - (99/100) * occupiedHit 7) :
    (jointBlank ≤ 1/100 ∧ jointMiss ≤ 1/20) ∧
    ∀ t : NNReal, ¬(blank5 t ≤ 1/100 ∧ miss5 t ≤ 1/20) := by
  have h := identity_rescue jointBlank jointMiss hblank hmiss
  exact ⟨⟨by linarith [h.1],by linarith [h.2]⟩,capacity5_no_deadline⟩

end AssayInformation
