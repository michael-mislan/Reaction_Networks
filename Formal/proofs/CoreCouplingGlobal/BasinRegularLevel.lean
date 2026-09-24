import proofs.CoreCouplingGlobal.StableGraphNormal
import proofs.CoreCouplingGlobal.FiniteBasinTransport

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

/-- At every point of the actual middle basin, that basin is locally the zero
set of an analytic scalar function with nonzero derivative. -/
theorem middle_basin_regular_level (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) (s : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s) (hz : s.z ∈ Icc (19/10:ℝ) (21/10))
    (x : ResponseVector) (hx : x ∈ positiveBasin e s) :
    ∃ N : Set ResponseVector, ∃ ρ : ResponseVector → ℝ,
      IsOpen N ∧ x ∈ N ∧ ContDiffOn ℝ ω ρ N ∧
      (∀ y ∈ N, y ∈ positiveDomain ∧ (y ∈ positiveBasin e s ↔ ρ y=0)) ∧
      ∃ n : ResponseVector →L[ℝ] ℝ, HasFDerivAt ρ n x ∧ n ≠ 0 := by
  have he : 0 ≤ e := by linarith
  obtain ⟨μ,C,_hC,φ,U,O,hU,_hU0,hO,hsO,_hφ0,_hd,hφ,_hinj,hleft,_hbasin,hgraph⟩ :=
    middle_basin_local_graph e hl hu s hs hss hz
  obtain ⟨X,hX,hX0,hlim⟩ := hx
  have hinit : encodeState (X 0)=x := by rw [hX0,encode_decodeState]
  have hOevent := hlim.eventually (hO.mem_nhds hsO)
  obtain ⟨T,hTall⟩ := eventually_atTop.1 (hOevent.and (eventually_ge_atTop (0:ℝ)))
  have hT : 0 ≤ T := (hTall T le_rfl).2
  have hXT : encodeState (X T) ∈ O := (hTall T le_rfl).1
  obtain ⟨F,R,hF0,_hR0,hF,_hR,_hleft,_hright,hbij,hpres⟩ :=
    positive_finite_analytic_basin_transport e he hu X hX T hT
  rw [hinit] at hF0 hF hbij hpres
  have hFxO : F x ∈ O := hF0 ▸ hXT
  have hFxU := (hgraph (F x) hFxO).1
  have hreg := stableGraphResidual_regular C s φ (F x) (hφ.contDiffAt (hU.mem_nhds hFxU))
  let ρ := stableGraphResidual C s φ ∘ F
  have hρ : ContDiffAt ℝ ω ρ x := hreg.1.comp x hF
  obtain ⟨n,hn,hnone⟩ := hreg.2
  have hder := hn.comp x ((hF.differentiableAt (by simp)).hasFDerivAt)
  have hnnonzero : n.comp (fderiv ℝ F x) ≠ 0 := by
    intro hzero
    obtain ⟨v,hv⟩ := hbij.2 (C (unstableInclusion 1))
    have hh := congrArg (fun L : ResponseVector →L[ℝ] ℝ => L v) hzero
    change n (fderiv ℝ F x v)=0 at hh
    rw [hv,hnone] at hh
    norm_num at hh
  have hFinO : ∀ᶠ y in 𝓝 x, F y ∈ O :=
    hF.continuousAt.preimage_mem_nhds (hO.mem_nhds hFxO)
  have hρevent := hρ.eventually (by simp : (ω:ℕ∞ω) ≠ ∞)
  obtain ⟨N,hNsub,hN,hNx⟩ := mem_nhds_iff.1 ((hpres.and hFinO).and hρevent)
  refine ⟨N,ρ,hN,hNx,?_,?_,n.comp (fderiv ℝ F x),hder,hnnonzero⟩
  · intro y hy
    exact (hNsub hy).2.contDiffWithinAt
  · intro y hy
    obtain ⟨⟨hyp,hFyp,hbas⟩,hFyO⟩ := (hNsub hy).1
    have hlocal := hgraph (F y) hFyO
    refine ⟨hyp,?_⟩
    exact (hbas s).trans (hlocal.2.trans
      (stableGraphResidual_zero_iff C s φ U hleft (F y) hlocal.1).symm)

end CoreCouplingGlobal
