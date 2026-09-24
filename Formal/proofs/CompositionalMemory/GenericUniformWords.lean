import proofs.CompositionalMemory.GenericUniformArchitecture
import proofs.CompositionalMemory.GenericReadout

namespace CompositionalMemory
open FiniteCopy

/-- All binary words use the same reaction mechanism and uniform constants.
Their integer initializations are distinguishable by one fixed readout, and
their actual certified generations satisfy the uniform lineage bound. -/
theorem general_uniform_word_architecture (d C : ℕ) (hC : 0 < C)
    (c radius outer recover parent birth lam rho M A P R U Z L D rmax lo : ℝ)
    (hc : 0 < c) (hradius : 0 ≤ radius) (houter : outer ≤ c*radius^2)
    (hlam : 0 < lam) (hrho : 0 < rho) (hM : 0 < M)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hrmax : 0 ≤ rmax)
    (hcore : M*rho < recover) (hgap : recover < parent)
    (hparent : parent < birth) (hbirth : birth < outer) (hlo : 0 < lo) :
    ∃ coupling N0 γ cgen : ℝ, ∃ (t₀ t₁ : NNReal) (hγ : 0 < γ),
      0 < coupling ∧ γ ≤ coupling ∧ 1 ≤ N0 ∧ 0 < cgen ∧
      0 < (t₀:ℝ) ∧ 0 < (t₁:ℝ) ∧
    ∀ {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (_ : N0 ≤ (N:ℝ))
      {ι : Type*} [Fintype ι]
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (w : Fin k → Fin k → ℝ)
    (hcoeff : ∀ i j, 0 ≤ coeff i j) (hw : ∀ i j, 0 ≤ w i j)
    (_hdiag : ∀ j, w j j=0) (_hsym : ∀ j l, w j l=w l j)
    (centers : (Fin k → Bool) → Fin k → Fin d → ℝ)
    (forms : (Fin k → Bool) → Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (κ : ℝ) (_hκ : 0 ≤ κ) (_hκmax : κ ≤ coupling)
    (_hcenter0 : ∀ σ, ∀ i j, 0 ≤ (centers σ) i j)
    (hcenter : ∀ σ, ∀ i j, (centers σ) i j ≤ (C:ℝ)-radius)
    (_hQ : ∀ σ, ∀ i x y, (forms σ) i x y=(forms σ) i y x)
    (_hop : ∀ σ, ∀ i x y, |(forms σ) i x y| ≤ L*‖x‖*‖y‖)
    (_hactivity : ∀ i, (∑ j, coeff i j*U^(∑ a, consume i j a)) ≤ A)
    (_hbias : ∀ i, (∑ j, (coeff i j*(∑ a, consume i j a:ℕ)^2*(U+1)^(∑ a, consume i j a))*
      ‖fun a => (produce i j a:ℝ)-(consume i j a:ℝ)‖) ≤ D)
    (_hrow : ∀ i, (∑ j, w i j) ≤ κ)
    (_hquality : ∀ σ, ∀ s ∈ generalProductDomain N C (centers σ) (fun i y => (forms σ) i y y) outer, ∀ i,
      let v := (s.2:ℝ)/k
      let u := generalConcentration s i
      let y := u-(centers σ) i
      let ν := fun j a => (produce i j a:ℝ)-(consume i j a:ℝ)
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ rmax ∧ ‖y‖ ≤ r ∧ ‖u‖ ≤ U ∧
        (∀ a, (s.1 i a:ℝ)/v ≤ U) ∧
        (∀ j, |(forms σ) i y (ν j)| ≤ P*r) ∧ (∀ j, |(forms σ) i (ν j) (ν j)| ≤ R) ∧
        2*(forms σ) i y (∑ j, (coeff i j*(∏ a, ((s.1 i a:ℝ)/v)^(consume i j a))) • ν j) ≤ -lam*r^2 ∧
        (forms σ) i y y ≤ M*r^2)
    (_hz : ∀ σ, ∀ s ∈ generalProductDomain N C (centers σ) (fun i y => (forms σ) i y y) outer,
      ∀ j, 0 ≤ generalConcentration s j z ∧ generalConcentration s j z ≤ Z)
    (hcoerc : ∀ σ, ∀ i y, c*‖y‖^2 ≤ (forms σ) i y y)
    (_hzlo : ∀ σ, ∀ s ∈ generalProductDomain N C (centers σ) (fun i y => (forms σ) i y y) outer,
      ∀ j, lo ≤ generalConcentration s j z)
    (a : Fin k → Fin d) (threshold : Fin k → ℝ)
    (_hmargin : ∀ σ i, if σ i then threshold i+radius ≤ centers σ i (a i)
      else centers σ i (a i)+radius ≤ threshold i),
    (∃ initial : (Fin k → Bool) → Fin k → Fin d → ℕ,
      (∀ σ, initial σ ∈ generalBirthCounts N C (centers σ) (fun i y => forms σ i y y) birth) ∧
      (∀ σ, generalWordReadout N a threshold (initial σ)=σ) ∧ Function.Injective initial) ∧
    ∀ σ : Fin k → Bool,
    let center := centers σ
    let Q := forms σ
    let next := generalGlobalNext consume produce z
    let rate := generalGlobalRate consume coeff z γ w
    let hrate := general_global_rate_nonneg consume coeff z γ w hcoeff hγ.le hw
    let domain₀ := generalProductDomain N C center (fun i y => Q i y y) outer
    let domain₁ := generalProductDomain N C center (fun i y => Q i y y) parent
    ∃ (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
      (hclock₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₀).total s ≤ q₀)
      (hclock₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₁).total s ≤ q₁),
    let K := generalGenerationLaw hk next rate hrate N C hN Q center c radius birth outer parent recover
      hc hradius hbirth.le houter hgap (hcenter σ) (hcoerc σ) q₀ t₀ q₁ t₁ hq₀ hq₁ hclock₀ hclock₁
    let ε := (k:ℝ)*(7+2*(d:ℝ)+(lam*rho/2)*((t₀:ℝ)/(outer-birth)+(t₁:ℝ)/(parent-recover)))*Real.exp (-cgen*N)
    (∀ n, (K n).mass none ≤ ε) ∧
    ∀ (G : ℕ) n, 1-(G:ℝ)*ε ≤ wordLineageSuccess K G n := by
  classical
  obtain ⟨coupling,N0,γ,cgen,t₀,t₁,hγ,hcoupling,hγc,hN0,hcgen,ht₀,ht₁,harch⟩ :=
    general_uniform_architecture d C hC c radius outer recover parent birth lam rho M A P R U Z L D rmax lo
      hc hradius houter hlam hrho hM hA hP hR hD hU hZ hL hrmax hcore hgap hparent hbirth hlo
  refine ⟨coupling,N0,γ,cgen,t₀,t₁,hγ,hcoupling,hγc,hN0,hcgen,ht₀,ht₁,?_⟩
  intro k hk N hN hlarge ι inst consume produce coeff z w hcoeff hw hdiag hsym centers forms κ hκ hκmax
    hcenter0 hcenter hQ hop hactivity hbias hrow hquality hz hcoerc hzlo a threshold hmargin
  have hresult (σ : Fin k → Bool) := harch hk N hN hlarge consume produce coeff z w hcoeff hw
    hdiag hsym (centers σ) (forms σ) κ hκ hκmax (hcenter0 σ) (hcenter σ) (hQ σ) (hop σ)
    hactivity hbias hrow (hquality σ) (hz σ) (hcoerc σ) (hzlo σ)
  let chosen := fun σ => Classical.choice (hresult σ).1
  let initial := fun σ => (chosen σ).val
  have hmem : ∀ σ, initial σ ∈ generalBirthCounts N C (centers σ) (fun i y => forms σ i y y) birth :=
    fun σ => (chosen σ).property
  have hdecode : ∀ σ, generalWordReadout N a threshold (initial σ)=σ := by
    intro σ
    exact general_birth_readout N C (centers σ) (forms σ) c radius birth hc hradius
      (hbirth.le.trans houter) (hcoerc σ) σ a threshold (hmargin σ) (chosen σ)
  refine ⟨⟨initial,hmem,hdecode,general_word_initialization_injective N a threshold initial hdecode⟩,?_⟩
  intro σ
  exact (hresult σ).2

/-- One growth interval, one exponent and copy floor, uniformly over every word and architecture. -/
theorem general_uniform_word_interval (d C : ℕ) (hC : 0 < C)
    (c radius outer recover parent birth lam rho M A P R U Z L D rmax lo : ℝ)
    (hc : 0 < c) (hradius : 0 ≤ radius) (houter : outer ≤ c*radius^2)
    (hlam : 0 < lam) (hrho : 0 < rho) (hM : 0 < M)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hrmax : 0 ≤ rmax)
    (hcore : M*rho < recover) (hgap : recover < parent)
    (hparent : parent < birth) (hbirth : birth < outer) (hlo : 0 < lo) :
    ∃ coupling N0 γ₀ cgen : ℝ, ∃ t₀ : NNReal,
      0 < coupling ∧ 0 < γ₀ ∧ γ₀ ≤ coupling ∧ 1 ≤ N0 ∧ 0 < cgen ∧
      0 < (t₀:ℝ) ∧ ∀ (γ : ℝ) (hγ : 0 < γ), γ ≤ γ₀ →
    ∃ t₁ : NNReal, 0 < (t₁:ℝ) ∧
    ∀ {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (_ : N0 ≤ (N:ℝ))
      {ι : Type*} [Fintype ι]
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (w : Fin k → Fin k → ℝ)
    (hcoeff : ∀ i j, 0 ≤ coeff i j) (hw : ∀ i j, 0 ≤ w i j)
    (_hdiag : ∀ j, w j j=0) (_hsym : ∀ j l, w j l=w l j)
    (centers : (Fin k → Bool) → Fin k → Fin d → ℝ)
    (forms : (Fin k → Bool) → Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (κ : ℝ) (_hκ : 0 ≤ κ) (_hκmax : κ ≤ coupling)
    (_hcenter0 : ∀ σ, ∀ i j, 0 ≤ (centers σ) i j)
    (hcenter : ∀ σ, ∀ i j, (centers σ) i j ≤ (C:ℝ)-radius)
    (_hQ : ∀ σ, ∀ i x y, (forms σ) i x y=(forms σ) i y x)
    (_hop : ∀ σ, ∀ i x y, |(forms σ) i x y| ≤ L*‖x‖*‖y‖)
    (_hactivity : ∀ i, (∑ j, coeff i j*U^(∑ a, consume i j a)) ≤ A)
    (_hbias : ∀ i, (∑ j, (coeff i j*(∑ a, consume i j a:ℕ)^2*(U+1)^(∑ a, consume i j a))*
      ‖fun a => (produce i j a:ℝ)-(consume i j a:ℝ)‖) ≤ D)
    (_hrow : ∀ i, (∑ j, w i j) ≤ κ)
    (_hquality : ∀ σ, ∀ s ∈ generalProductDomain N C (centers σ) (fun i y => (forms σ) i y y) outer, ∀ i,
      let v := (s.2:ℝ)/k
      let u := generalConcentration s i
      let y := u-(centers σ) i
      let ν := fun j a => (produce i j a:ℝ)-(consume i j a:ℝ)
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ rmax ∧ ‖y‖ ≤ r ∧ ‖u‖ ≤ U ∧
        (∀ a, (s.1 i a:ℝ)/v ≤ U) ∧
        (∀ j, |(forms σ) i y (ν j)| ≤ P*r) ∧ (∀ j, |(forms σ) i (ν j) (ν j)| ≤ R) ∧
        2*(forms σ) i y (∑ j, (coeff i j*(∏ a, ((s.1 i a:ℝ)/v)^(consume i j a))) • ν j) ≤ -lam*r^2 ∧
        (forms σ) i y y ≤ M*r^2)
    (_hz : ∀ σ, ∀ s ∈ generalProductDomain N C (centers σ) (fun i y => (forms σ) i y y) outer,
      ∀ j, 0 ≤ generalConcentration s j z ∧ generalConcentration s j z ≤ Z)
    (hcoerc : ∀ σ, ∀ i y, c*‖y‖^2 ≤ (forms σ) i y y)
    (_hzlo : ∀ σ, ∀ s ∈ generalProductDomain N C (centers σ) (fun i y => (forms σ) i y y) outer,
      ∀ j, lo ≤ generalConcentration s j z)
    (a : Fin k → Fin d) (threshold : Fin k → ℝ)
    (_hmargin : ∀ σ i, if σ i then threshold i+radius ≤ centers σ i (a i)
      else centers σ i (a i)+radius ≤ threshold i),
    (∃ initial : (Fin k → Bool) → Fin k → Fin d → ℕ,
      (∀ σ, initial σ ∈ generalBirthCounts N C (centers σ) (fun i y => forms σ i y y) birth) ∧
      (∀ σ, generalWordReadout N a threshold (initial σ)=σ) ∧ Function.Injective initial) ∧
    ∀ σ : Fin k → Bool,
    let center := centers σ
    let Q := forms σ
    let next := generalGlobalNext consume produce z
    let rate := generalGlobalRate consume coeff z γ w
    let hrate := general_global_rate_nonneg consume coeff z γ w hcoeff hγ.le hw
    let domain₀ := generalProductDomain N C center (fun i y => Q i y y) outer
    let domain₁ := generalProductDomain N C center (fun i y => Q i y y) parent
    ∃ (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
      (hclock₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₀).total s ≤ q₀)
      (hclock₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₁).total s ≤ q₁),
    let K := generalGenerationLaw hk next rate hrate N C hN Q center c radius birth outer parent recover
      hc hradius hbirth.le houter hgap (hcenter σ) (hcoerc σ) q₀ t₀ q₁ t₁ hq₀ hq₁ hclock₀ hclock₁
    let ε := (k:ℝ)*(7+2*(d:ℝ)+(lam*rho/2)*((t₀:ℝ)/(outer-birth)+(t₁:ℝ)/(parent-recover)))*Real.exp (-cgen*N)
    (∀ n, (K n).mass none ≤ ε) ∧
    ∀ (G : ℕ) n, 1-(G:ℝ)*ε ≤ wordLineageSuccess K G n := by
  classical
  obtain ⟨coupling,N0,γ₀,cgen,t₀,hcoupling,hγ₀,hγ₀c,hN0,hcgen,ht₀,hinterval⟩ :=
    general_uniform_architecture_interval d C hC c radius outer recover parent birth lam rho M A P R U Z L D rmax lo
      hc hradius houter hlam hrho hM hA hP hR hD hU hZ hL hrmax hcore hgap hparent hbirth hlo
  refine ⟨coupling,N0,γ₀,cgen,t₀,hcoupling,hγ₀,hγ₀c,hN0,hcgen,ht₀,?_⟩
  intro γ hγ hγmax
  obtain ⟨t₁,ht₁,harch⟩ := hinterval γ hγ hγmax
  refine ⟨t₁,ht₁,?_⟩
  intro k hk N hN hlarge ι inst consume produce coeff z w hcoeff hw hdiag hsym centers forms κ hκ hκmax
    hcenter0 hcenter hQ hop hactivity hbias hrow hquality hz hcoerc hzlo a threshold hmargin
  have hresult (σ : Fin k → Bool) := harch hk N hN hlarge consume produce coeff z w hcoeff hw
    hdiag hsym (centers σ) (forms σ) κ hκ hκmax (hcenter0 σ) (hcenter σ) (hQ σ) (hop σ)
    hactivity hbias hrow (hquality σ) (hz σ) (hcoerc σ) (hzlo σ)
  let chosen := fun σ => Classical.choice (hresult σ).1
  let initial := fun σ => (chosen σ).val
  have hmem : ∀ σ, initial σ ∈ generalBirthCounts N C (centers σ) (fun i y => forms σ i y y) birth :=
    fun σ => (chosen σ).property
  have hdecode : ∀ σ, generalWordReadout N a threshold (initial σ)=σ := by
    intro σ
    exact general_birth_readout N C (centers σ) (forms σ) c radius birth hc hradius
      (hbirth.le.trans houter) (hcoerc σ) σ a threshold (hmargin σ) (chosen σ)
  refine ⟨⟨initial,hmem,hdecode,general_word_initialization_injective N a threshold initial hdecode⟩,?_⟩
  intro σ
  exact (hresult σ).2

end CompositionalMemory
