import proofs.CoreCouplingGlobal.GraphFlatten
import proofs.CoreCouplingGlobal.AnalyticGermChart
import proofs.CoreCouplingGlobal.FiniteBasinTransport

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

/-- Every point of the actual middle basin has an analytic ambient chart,
with analytic inverse, carrying that basin exactly to the coordinate plane v3=0.
This is an explicit embedded analytic hypersurface chart, not an assumed
stable-manifold predicate or only a parametrized subset of the basin. -/
theorem middle_basin_analytic_manifold_chart (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) (s : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s) (hz : s.z ∈ Icc (19/10:ℝ) (21/10))
    (x : ResponseVector) (hx : x ∈ positiveBasin e s) :
    ∃ H : OpenPartialHomeomorph ResponseVector ResponseVector,
      x ∈ H.source ∧ ContDiffOn ℝ ω H H.source ∧ ContDiffOn ℝ ω H.symm H.target ∧
      ∀ y ∈ H.source, y ∈ positiveDomain ∧ (y ∈ positiveBasin e s ↔ H y 3=0) := by
  have he : 0 ≤ e := by linarith
  obtain ⟨μ,C,_hC,φ,U,O,hU,_hU0,hO,hsO,_hφ0,_hd,hφ,_hinj,hleft,_hbasin,hgraph⟩ :=
    middle_basin_local_graph e hl hu s hs hss hz
  obtain ⟨X,hX,hX0,hlim⟩ := hx
  have hinit : encodeState (X 0)=x := by rw [hX0,encode_decodeState]
  obtain ⟨T,hTall⟩ := eventually_atTop.1
    ((hlim.eventually (hO.mem_nhds hsO)).and (eventually_ge_atTop (0:ℝ)))
  have hT := (hTall T le_rfl).2
  have hXT := (hTall T le_rfl).1
  obtain ⟨F,R,hF0,hR0,hF,hR,hRF,hFR,_hbij,hpres⟩ :=
    positive_finite_analytic_basin_transport e he hu X hX T hT
  rw [hinit] at hF0 hR0 hF hRF hpres
  have hFxO : F x ∈ O := by rw [hF0]; exact hXT
  have hFxU := (hgraph (F x) hFxO).1
  let B := physicalGraphFlatten C s φ
  let D := physicalGraphUnflatten C s φ
  have hBD : ∀ y, D (B y)=y := fun y => (physical_graph_flatten_inverse C s φ y 0).1
  have hDB : ∀ y, B (D y)=y := fun y => (physical_graph_flatten_inverse C s φ 0 y).2
  obtain ⟨hB,hD⟩ := physical_graph_flatten_analytic C s φ (F x)
    (hφ.contDiffAt (hU.mem_nhds hFxU))
  let K := B ∘ F
  let L := R ∘ D
  have hK : ContDiffAt ℝ ω K x := hB.comp x hF
  have hR' : ContDiffAt ℝ ω R (D (K x)) := by
    change ContDiffAt ℝ ω R (D (B (F x)))
    rw [hBD,hF0]
    exact hR
  have hL : ContDiffAt ℝ ω L (K x) := hR'.comp (K x) hD
  have hLK : ∀ᶠ y in 𝓝 x, L (K y)=y := by
    filter_upwards [hRF] with y hy
    change R (D (B (F y)))=y
    rw [hBD]
    exact hy
  have hDlim : Tendsto D (𝓝 (K x)) (𝓝 (encodeState (X T))) := by
    have hh := hD.continuousAt.tendsto
    change Tendsto D (𝓝 (K x)) (𝓝 (D (B (F x)))) at hh
    simpa only [hBD,hF0] using hh
  have hKL : ∀ᶠ y in 𝓝 (K x), K (L y)=y := by
    filter_upwards [hDlim.eventually hFR] with y hy
    change B (F (R (D y)))=y
    rw [hy,hDB]
  have hFinO : ∀ᶠ y in 𝓝 x, F y ∈ O :=
    hF.continuousAt.preimage_mem_nhds (hO.mem_nhds hFxO)
  let A : Set ResponseVector := {y | y ∈ positiveDomain ∧
    (y ∈ positiveBasin e s ↔ K y 3=0)}
  have hA : A ∈ 𝓝 x := by
    filter_upwards [hpres,hFinO] with y hy hyO
    have hg := hgraph (F y) hyO
    refine ⟨hy.1,(hy.2.2 s).trans (hg.2.trans ?_)⟩
    have hziff := (stableGraphResidual_zero_iff C s φ U hleft (F y) hg.1).symm
    simpa only [K,Function.comp_apply,B,physicalGraphFlatten_last] using hziff
  obtain ⟨H,hHK,_hHL,hxH,hHA,hH,hHi⟩ :=
    analytic_inverse_germs_chart K L x (K x) rfl hK hL hLK hKL A hA
  refine ⟨H,hxH,hH,hHi,?_⟩
  intro y hy
  have hh := hHA hy
  simpa only [hHK] using hh

end CoreCouplingGlobal
