import proofs.CompositionalMemory.GenericArchitectureLineage
import proofs.CompositionalMemory.GenericGenerationParameters
import proofs.CompositionalMemory.GenericBirthExistence

namespace CompositionalMemory
open FiniteCopy

/-- Uniform scalar constants for literal reaction generations and their lineages.
All architecture data, including module count and stored center, are quantified
AFTER the constants. No stochastic accuracy hypothesis is supplied. -/
theorem general_uniform_architecture (d C : ℕ) (hC : 0 < C)
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
    (center : Fin k → Fin d → ℝ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (κ : ℝ) (_hκ : 0 ≤ κ) (_hκmax : κ ≤ coupling)
    (_hcenter0 : ∀ i j, 0 ≤ center i j)
    (hcenter : ∀ i j, center i j ≤ (C:ℝ)-radius)
    (_hQ : ∀ i x y, Q i x y=Q i y x)
    (_hop : ∀ i x y, |Q i x y| ≤ L*‖x‖*‖y‖)
    (_hactivity : ∀ i, (∑ j, coeff i j*U^(∑ a, consume i j a)) ≤ A)
    (_hbias : ∀ i, (∑ j, (coeff i j*(∑ a, consume i j a:ℕ)^2*(U+1)^(∑ a, consume i j a))*
      ‖fun a => (produce i j a:ℝ)-(consume i j a:ℝ)‖) ≤ D)
    (_hrow : ∀ i, (∑ j, w i j) ≤ κ)
    (_hquality : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer, ∀ i,
      let v := (s.2:ℝ)/k
      let u := generalConcentration s i
      let y := u-center i
      let ν := fun j a => (produce i j a:ℝ)-(consume i j a:ℝ)
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ rmax ∧ ‖y‖ ≤ r ∧ ‖u‖ ≤ U ∧
        (∀ a, (s.1 i a:ℝ)/v ≤ U) ∧
        (∀ j, |Q i y (ν j)| ≤ P*r) ∧ (∀ j, |Q i (ν j) (ν j)| ≤ R) ∧
        2*Q i y (∑ j, (coeff i j*(∏ a, ((s.1 i a:ℝ)/v)^(consume i j a))) • ν j) ≤ -lam*r^2 ∧
        Q i y y ≤ M*r^2)
    (_hz : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer,
      ∀ j, 0 ≤ generalConcentration s j z ∧ generalConcentration s j z ≤ Z)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (_hzlo : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer,
      ∀ j, lo ≤ generalConcentration s j z),
    Nonempty (GeneralBirthCount N C center (fun i y => Q i y y) birth) ∧
    let next := generalGlobalNext consume produce z
    let rate := generalGlobalRate consume coeff z γ w
    let hrate := general_global_rate_nonneg consume coeff z γ w hcoeff hγ.le hw
    let domain₀ := generalProductDomain N C center (fun i y => Q i y y) outer
    let domain₁ := generalProductDomain N C center (fun i y => Q i y y) parent
    ∃ (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
      (hclock₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₀).total s ≤ q₀)
      (hclock₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₁).total s ≤ q₁),
    let K := generalGenerationLaw hk next rate hrate N C hN Q center c radius birth outer parent recover
      hc hradius hbirth.le houter hgap hcenter hcoerc q₀ t₀ q₁ t₁ hq₀ hq₁ hclock₀ hclock₁
    let ε := (k:ℝ)*(7+2*(d:ℝ)+(lam*rho/2)*((t₀:ℝ)/(outer-birth)+(t₁:ℝ)/(parent-recover)))*Real.exp (-cgen*N)
    (∀ n, (K n).mass none ≤ ε) ∧
    ∀ (G : ℕ) n, 1-(G:ℝ)*ε ≤ wordLineageSuccess K G n := by
  classical
  obtain ⟨α,coupling,N0,γ,t₀,t₁,rpart,δ,cgen,hα,hcoupling,_hc1,hN0,
    hγ,hγc,ht₀,ht₁,hrecover,hearly,hlate,hrpart,hsize,hδ,_hδ1,hmargin,
    hcgen,hc₀,hc₁,hcr,hce,hcl,hcp,hbudgets⟩ :=
    exists_uniform_generation_parameters lam rho M c A P R D U Z L rmax recover parent birth outer lo C
      hlam hrho hM hc hA hP hR hD hU hZ hL hrmax hcore hgap hparent hbirth hlo (by exact_mod_cast hC)
  have hbirth0 : 0 < birth := (mul_pos hM hrho).trans (hcore.trans (hgap.trans hparent))
  refine ⟨coupling,max N0 (1+L/birth),γ,cgen,⟨t₀,ht₀.le⟩,⟨t₁,ht₁.le⟩,hγ,hcoupling,hγc,hN0.trans (le_max_left _ _),hcgen,ht₀,ht₁,?_⟩
  intro k hk N hN hlarge ι inst consume produce coeff z w hcoeff hw hdiag hsym center Q κ hκ hκmax
    hcenter0 hcenter hQ hop hactivity hbias hrow hquality hz hcoerc hzlo
  have hsmall : N0 ≤ (N:ℝ) := (le_max_left _ _).trans hlarge
  have hfloor : L/(N:ℝ)^2 < birth := birth_floor_budget L birth N hL hbirth0 ((le_max_right _ _).trans hlarge)
  refine ⟨general_birth_nonempty N C (by omega) center Q L birth hL hcenter0
    (fun i a => (hcenter i a).trans (by linarith only [hradius])) hop hfloor,?_⟩
  have hb := hbudgets N 0 κ hsmall le_rfl hrmax hκ hκmax
  exact general_architecture_lineage hk N C hN hC consume produce coeff z γ w hcoeff hγ.le hw
    hdiag hsym center Q c radius outer α birth recover κ lam rho M A P R U Z L D rmax
    hc hradius houter hα hlam hM hrho hP hR hU hZ hL hA hκ hcenter hQ hop hactivity hbias hrow
    (fun r hr hrr => (hbudgets N r κ hsmall hr hrr hκ hκmax).1)
    (fun r hr hrr => (hbudgets N r κ hsmall hr hrr hκ hκmax).2.1)
    hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hquality hz parent lo rpart δ hbirth hgap hlo.le hrpart.le hδ
    hcoerc hsize hmargin hzlo hcore cgen hc₀ hc₁ hcr hce hcl hcp
    ⟨t₀,ht₀.le⟩ ⟨t₁,ht₁.le⟩ hrecover hearly hlate

/-- Uniform architecture theorem for every positive rate in one fixed growth interval. -/
theorem general_uniform_architecture_interval (d C : ℕ) (hC : 0 < C)
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
    (center : Fin k → Fin d → ℝ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (κ : ℝ) (_hκ : 0 ≤ κ) (_hκmax : κ ≤ coupling)
    (_hcenter0 : ∀ i j, 0 ≤ center i j)
    (hcenter : ∀ i j, center i j ≤ (C:ℝ)-radius)
    (_hQ : ∀ i x y, Q i x y=Q i y x)
    (_hop : ∀ i x y, |Q i x y| ≤ L*‖x‖*‖y‖)
    (_hactivity : ∀ i, (∑ j, coeff i j*U^(∑ a, consume i j a)) ≤ A)
    (_hbias : ∀ i, (∑ j, (coeff i j*(∑ a, consume i j a:ℕ)^2*(U+1)^(∑ a, consume i j a))*
      ‖fun a => (produce i j a:ℝ)-(consume i j a:ℝ)‖) ≤ D)
    (_hrow : ∀ i, (∑ j, w i j) ≤ κ)
    (_hquality : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer, ∀ i,
      let v := (s.2:ℝ)/k
      let u := generalConcentration s i
      let y := u-center i
      let ν := fun j a => (produce i j a:ℝ)-(consume i j a:ℝ)
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ rmax ∧ ‖y‖ ≤ r ∧ ‖u‖ ≤ U ∧
        (∀ a, (s.1 i a:ℝ)/v ≤ U) ∧
        (∀ j, |Q i y (ν j)| ≤ P*r) ∧ (∀ j, |Q i (ν j) (ν j)| ≤ R) ∧
        2*Q i y (∑ j, (coeff i j*(∏ a, ((s.1 i a:ℝ)/v)^(consume i j a))) • ν j) ≤ -lam*r^2 ∧
        Q i y y ≤ M*r^2)
    (_hz : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer,
      ∀ j, 0 ≤ generalConcentration s j z ∧ generalConcentration s j z ≤ Z)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (_hzlo : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer,
      ∀ j, lo ≤ generalConcentration s j z),
    Nonempty (GeneralBirthCount N C center (fun i y => Q i y y) birth) ∧
    let next := generalGlobalNext consume produce z
    let rate := generalGlobalRate consume coeff z γ w
    let hrate := general_global_rate_nonneg consume coeff z γ w hcoeff hγ.le hw
    let domain₀ := generalProductDomain N C center (fun i y => Q i y y) outer
    let domain₁ := generalProductDomain N C center (fun i y => Q i y y) parent
    ∃ (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
      (hclock₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₀).total s ≤ q₀)
      (hclock₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₁).total s ≤ q₁),
    let K := generalGenerationLaw hk next rate hrate N C hN Q center c radius birth outer parent recover
      hc hradius hbirth.le houter hgap hcenter hcoerc q₀ t₀ q₁ t₁ hq₀ hq₁ hclock₀ hclock₁
    let ε := (k:ℝ)*(7+2*(d:ℝ)+(lam*rho/2)*((t₀:ℝ)/(outer-birth)+(t₁:ℝ)/(parent-recover)))*Real.exp (-cgen*N)
    (∀ n, (K n).mass none ≤ ε) ∧
    ∀ (G : ℕ) n, 1-(G:ℝ)*ε ≤ wordLineageSuccess K G n := by
  classical
  obtain ⟨α,coupling,N0,γ₀,t₀,rpart,δ,cgen,hα,hcoupling,_hc1,hN0,
    hγ₀,hγ₀c,ht₀,hrpart,hsize,hδ,_hδ1,hmargin,
    hcgen,hc₀,hc₁,hcr,hce,hcl,hcp,hinterval⟩ :=
    exists_uniform_generation_interval lam rho M c A P R D U Z L rmax recover parent birth outer lo C
      hlam hrho hM hc hA hP hR hD hU hZ hL hrmax hcore hgap hparent hbirth hlo (by exact_mod_cast hC)
  have hbirth0 : 0 < birth := (mul_pos hM hrho).trans (hcore.trans (hgap.trans hparent))
  refine ⟨coupling,max N0 (1+L/birth),γ₀,cgen,⟨t₀,ht₀.le⟩,hcoupling,hγ₀,hγ₀c,
    hN0.trans (le_max_left _ _),hcgen,ht₀,?_⟩
  intro γ hγ hγmax
  obtain ⟨t₁,ht₁,hrecover,hearly,hlate,hbudgets⟩ := hinterval γ hγ hγmax
  refine ⟨⟨t₁,ht₁.le⟩,ht₁,?_⟩
  intro k hk N hN hlarge ι inst consume produce coeff z w hcoeff hw hdiag hsym center Q κ hκ hκmax
    hcenter0 hcenter hQ hop hactivity hbias hrow hquality hz hcoerc hzlo
  have hsmall : N0 ≤ (N:ℝ) := (le_max_left _ _).trans hlarge
  have hfloor : L/(N:ℝ)^2 < birth := birth_floor_budget L birth N hL hbirth0 ((le_max_right _ _).trans hlarge)
  refine ⟨general_birth_nonempty N C (by omega) center Q L birth hL hcenter0
    (fun i a => (hcenter i a).trans (by linarith only [hradius])) hop hfloor,?_⟩
  have hb := hbudgets N 0 κ hsmall le_rfl hrmax hκ hκmax
  exact general_architecture_lineage hk N C hN hC consume produce coeff z γ w hcoeff hγ.le hw
    hdiag hsym center Q c radius outer α birth recover κ lam rho M A P R U Z L D rmax
    hc hradius houter hα hlam hM hrho hP hR hU hZ hL hA hκ hcenter hQ hop hactivity hbias hrow
    (fun r hr hrr => (hbudgets N r κ hsmall hr hrr hκ hκmax).1)
    (fun r hr hrr => (hbudgets N r κ hsmall hr hrr hκ hκmax).2.1)
    hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hquality hz parent lo rpart δ hbirth hgap hlo.le hrpart.le hδ
    hcoerc hsize hmargin hzlo hcore cgen hc₀ hc₁ hcr hce hcl hcp
    ⟨t₀,ht₀.le⟩ ⟨t₁,ht₁.le⟩ hrecover hearly hlate

end CompositionalMemory
