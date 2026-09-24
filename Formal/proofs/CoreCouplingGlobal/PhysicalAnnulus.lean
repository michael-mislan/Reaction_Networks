import proofs.CoreCouplingGlobal.UnstableSublevel
import proofs.CoreCouplingGlobal.AnnularEnergy

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology

theorem positive_stationary_isolated (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) (s : State) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : State, x.Positive → Stationary (flagshipRates e) x →
      dist (encodeState x) (encodeState s) < r → x=s := by
  obtain ⟨a,b,c,_ha,_hb,_hc,_hsa,_hsb,_hsc,_hab,_hbc,hall⟩ :=
    exactly_three_positive_equilibria e hl hu
  let S : Set ResponseVector := {encodeState a,encodeState b,encodeState c}
  have hS : S.Finite := by simp [S]
  have ho : IsOpen (S \ {encodeState s})ᶜ := (show (S \ {encodeState s}).Finite from hS.diff).isClosed.isOpen_compl
  have hm : encodeState s ∈ (S \ {encodeState s})ᶜ := by simp
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.1 ho (encodeState s) hm
  refine ⟨r,hr,?_⟩
  intro x hx hss hdist
  have hxS : encodeState x ∈ S := by
    have hcases := (hall x hx hss).1
    rcases hcases with rfl | rfl | rfl <;> simp [S]
  have hnot := hball hdist
  have henc : encodeState x=encodeState s := by
    by_contra hn
    exact hnot ⟨hxS,by simpa using hn⟩
  simpa only [decode_encodeState] using congrArg decodeState henc

/-- Compact physical annuli around the middle have a positive residual cost.
All bounds are constructed for the literal field, not assumed certificates. -/
theorem middle_physical_annulus (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) (s : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s) (hz : s.z ∈ Icc (19/10:ℝ) (21/10))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r M d : ℝ, 0 < r ∧ r < ε ∧ 0 < M ∧ 0 < d ∧
      (∀ x : ResponseVector, dist x (encodeState s) ≤ r →
        x ∈ positiveDomain ∧ InSelectionRegion (decodeState x)) ∧
      (∀ x : ResponseVector, dist x (encodeState s) ≤ r → ‖responseVectorField e x‖ ≤ M) ∧
      ∀ x : ResponseVector, r/2 ≤ dist x (encodeState s) → dist x (encodeState s) ≤ r →
        d ≤ responseResidualNorm e (decodeState x) := by
  have he : 0 ≤ e := by linarith
  obtain ⟨a,ha,hsel⟩ := middle_physical_selection_neighborhood e he hu s hs hss hz
  have hsp : encodeState s ∈ positiveDomain := by
    simpa only [positiveDomain,mem_setOf_eq,decode_encodeState] using hs
  obtain ⟨b,hb,hpos⟩ := Metric.isOpen_iff.1 positiveDomain_isOpen (encodeState s) hsp
  obtain ⟨c,hc,hiso⟩ := positive_stationary_isolated e hl hu s
  let r := min ε (min a (min b c))/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by dsimp [r]; have hh := min_le_left ε (min a (min b c)); linarith
  have hra : r < a := by
    have hh := (min_le_right ε (min a (min b c))).trans (min_le_left a (min b c))
    dsimp [r]; linarith
  have hrb : r < b := by
    have hh := (min_le_right ε (min a (min b c))).trans
      ((min_le_right a (min b c)).trans (min_le_left b c))
    dsimp [r]; linarith
  have hrc : r < c := by
    have hh := (min_le_right ε (min a (min b c))).trans
      ((min_le_right a (min b c)).trans (min_le_right b c))
    dsimp [r]; linarith
  have hreg : ∀ x : ResponseVector, dist x (encodeState s) ≤ r →
      x ∈ positiveDomain ∧ InSelectionRegion (decodeState x) := by
    intro x hx
    exact ⟨hpos (hx.trans_lt hrb),hsel x (hx.trans_lt hra)⟩
  let K := Metric.closedBall (encodeState s) r ∩ {x : ResponseVector | r/2 ≤ dist x (encodeState s)}
  have hK : IsCompact K := (isCompact_closedBall (encodeState s) r).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hqpos : ∀ x ∈ K, 0 < responseResidualNorm e (decodeState x) := by
    intro x hx
    have hxr : dist x (encodeState s) ≤ r := hx.1
    obtain ⟨hxp,hxsel⟩ := hreg x hxr
    have hbox := positive_selection_response_box (decodeState x) hxp hxsel
    apply lt_of_le_of_ne (responseResidualNorm_nonneg e _)
    intro hzero
    have hstat := stationary_of_responseResidualNorm_zero e (decodeState x) he hu hbox hzero.symm
    have heq := hiso (decodeState x) hxp hstat (by
      simpa only [encode_decodeState] using hxr.trans_lt hrc)
    have hxs : x=encodeState s := by simpa only [encode_decodeState] using congrArg encodeState heq
    have hh : r/2 ≤ dist x (encodeState s) := hx.2
    rw [hxs,dist_self] at hh
    linarith
  obtain ⟨d,hd,hdall⟩ := hK.exists_forall_le' (residualNorm_continuous e).continuousOn hqpos
  obtain ⟨M,hM⟩ := (isCompact_closedBall (encodeState s) r).bddAbove_image
    (responseVectorField_contDiff e).continuous.continuousOn.norm
  refine ⟨r,max M 0+1,d,hr,hrε,by positivity,hd,hreg,?_,?_⟩
  · intro x hx
    have hh := hM (mem_image_of_mem _ hx)
    exact hh.trans (by linarith [le_max_left M 0])
  · intro x hxlo hxhi
    exact hdall x ⟨hxhi,hxlo⟩

end CoreCouplingGlobal
