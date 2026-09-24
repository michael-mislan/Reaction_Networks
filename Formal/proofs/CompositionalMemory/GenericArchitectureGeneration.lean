import proofs.CompositionalMemory.GenericArchitectureFirstPhase
import proofs.CompositionalMemory.GenericArchitectureSecondPhase
import proofs.CompositionalMemory.GenericGenerationBound

namespace CompositionalMemory
open FiniteCopy

theorem general_product_domain_mono {k d : ℕ} (N C : ℕ)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ)
    (b B : ℝ) (hb : b ≤ B) : generalProductDomain N C center E b ⊆ generalProductDomain N C center E B := by
  classical
  intro s hs
  unfold generalProductDomain at hs ⊢
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1,fun i => ((Finset.mem_filter.mp hs).2 i).trans_le hb⟩

/-- Failure of the constructed two-phase architecture generation law, derived
from primitive reaction/module bounds, without a phase-accuracy premise. -/
theorem general_architecture_generation_failure {k d : ℕ} {ι : Type*} [Fintype ι]
    (hk : 1 ≤ k) (N C : ℕ) (hN : 1 ≤ N) (hC : 0 < C)
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hcoeff : ∀ i j, 0 ≤ coeff i j) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (center : Fin k → Fin d → ℝ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (c radius outer α birth recover κ lam rho M A P R U Z L D rmax : ℝ)
    (hc : 0 < c) (hradius : 0 ≤ radius) (houter : outer ≤ c*radius^2)
    (hα : 0 < α) (hlam : 0 < lam) (hM : 0 < M) (hrho : 0 < rho)
    (hP : 0 ≤ P) (hR : 0 ≤ R) (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hA0 : 0 ≤ A) (hκ : 0 ≤ κ)
    (hcenter : ∀ i j, center i j ≤ (C:ℝ)-radius)
    (hQ : ∀ i x y, Q i x y=Q i y x)
    (hop : ∀ i x y, |Q i x y| ≤ L*‖x‖*‖y‖)
    (hactivity : ∀ i, (∑ j, coeff i j*U^(∑ a, consume i j a)) ≤ A)
    (hbias : ∀ i, (∑ j, (coeff i j*(∑ a, consume i j a:ℕ)^2*(U+1)^(∑ a, consume i j a))*
      ‖fun a => (produce i j a:ℝ)-(consume i j a:ℝ)‖) ≤ D)
    (hrow : ∀ i, (∑ j, w i j) ≤ κ)
    (hsres : ∀ r, 0 ≤ r → r ≤ rmax → α*(2*(P*r)+R/N) ≤ 1)
    (hscouple : ∀ r, 0 ≤ r → r ≤ rmax → α*(2*L*r*(U+1)+L*(U+1)^2/N) ≤ 1)
    (habsorb : α*(8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ) ≤ lam/4)
    (hforce : (2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2 ≤ lam^2*rho/8)
    (hcopy : (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
      α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N ≤ lam*N*rho/8)
    (hquality : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer, ∀ i,
      let v := (s.2:ℝ)/k
      let u := generalConcentration s i
      let y := u-center i
      let ν := fun j a => (produce i j a:ℝ)-(consume i j a:ℝ)
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ rmax ∧ ‖y‖ ≤ r ∧ ‖u‖ ≤ U ∧
        (∀ a, (s.1 i a:ℝ)/v ≤ U) ∧
        (∀ j, |Q i y (ν j)| ≤ P*r) ∧ (∀ j, |Q i (ν j) (ν j)| ≤ R) ∧
        2*Q i y (∑ j, (coeff i j*(∏ a, ((s.1 i a:ℝ)/v)^(consume i j a))) • ν j) ≤ -lam*r^2 ∧
        Q i y y ≤ M*r^2)
    (hz : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer,
      ∀ j, 0 ≤ generalConcentration s j z ∧ generalConcentration s j z ≤ Z)     (parent lo rpart δ : ℝ) (hbirth : birth ≤ outer) (hgap : recover < parent)
    (hlo : 0 ≤ lo) (hrpart : 0 ≤ rpart) (hδ : 0 < δ)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (hsize : parent ≤ c*rpart^2) (hmargin : parent+2*L*rpart*δ+L*δ^2 < birth)
    (hzlo : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer,
      ∀ j, lo ≤ generalConcentration s j z) :
    let next := generalGlobalNext consume produce z
    let rate := generalGlobalRate consume coeff z γ w
    let hrate := general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw
    let domain₀ := generalProductDomain N C center (fun i y => Q i y y) outer
    let domain₁ := generalProductDomain N C center (fun i y => Q i y y) parent
    let ceiling := α*((A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
      α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N+
      N*(2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2/lam)*Real.exp (α*N*(M*rho))
    ∀ (q₀ t₀ q₁ t₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
      (_ : α*lam*N*rho/4 ≤ q₀) (_ : 4*birth ≤ lam*rho*(t₀:ℝ)) (_ : γ*Z*(t₀:ℝ) ≤ 2/5)
      (_ : γ*lo*(t₁:ℝ)=11/10) (_ : 19*(γ*lo)*((k*N:ℕ):ℝ)/400 ≤ q₁)
      (hc₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₀).total s ≤ q₀)
      (hc₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₁).total s ≤ q₁)
      (n : GeneralBirthCount N C center (fun i y => Q i y y) birth),
    (generalGenerationLaw hk next rate hrate N C hN Q center c radius birth outer parent recover
      hc hradius hbirth houter hgap hcenter hcoerc q₀ t₀ q₁ t₁ hq₀ hq₁ hc₀ hc₁ n).mass none ≤
      ((k:ℝ)*(Real.exp (α*N*birth)+(t₀:ℝ)*ceiling)/Real.exp (α*N*outer)+
        (Real.exp (-((k*N:ℕ):ℝ)/125)+3*(k:ℝ)*Real.exp (-α*N*(recover-M*rho))))+
      ((k:ℝ)*(Real.exp (α*N*recover)+(t₁:ℝ)*ceiling)/Real.exp (α*N*parent)+
        Real.exp (-9*((k*N:ℕ):ℝ)/4000)+2*(k:ℝ)*(d:ℝ)*Real.exp (-2*(N:ℝ)*δ^2/(2*(C:ℝ)))) := by
  classical
  intro next rate hrate domain₀ domain₁ ceiling q₀ t₀ q₁ t₁ hq₀ hq₁ hd₀ ht₀ hearly ht₁ hd₁ hc₀ hc₁ n
  have hE := fun i => norm_coercive_coordinate (Q i) c hc.le (hcoerc i)
  have hparentbirth : parent < birth := by
    have hh : 0 ≤ 2*L*rpart*δ+L*δ^2 := by positivity
    linarith only [hmargin,hh]
  have hparentouter : parent ≤ outer := hparentbirth.le.trans hbirth
  have hsub : domain₁ ⊆ domain₀ := general_product_domain_mono N C center (fun i y => Q i y y) parent outer hparentouter
  let start : {s : GeneralCountState k d // s ∈ domain₀} :=
    ⟨(n.val,k*N),general_birth_in_growth_domain hk N C hN center (fun i y => Q i y y)
      c radius birth outer hc hradius hbirth houter hcenter hE n⟩
  have hstart (i) : Q i (generalConcentration start.val i-center i) (generalConcentration start.val i-center i) ≤ birth := by
    have he := (mem_generalBirthCounts N C (by omega) center (fun i y => Q i y y)
      c radius birth hc hradius (hbirth.trans houter) hcenter hE n.val).mp n.property i
    change Q i (generalConcentration (n.val,k*N) i-center i) (generalConcentration (n.val,k*N) i-center i) ≤ birth
    rw [general_lattice_concentration hk]
    exact he.le
  let ε₀ := (k:ℝ)*(Real.exp (α*N*birth)+(t₀:ℝ)*ceiling)/Real.exp (α*N*outer)+
    (Real.exp (-((k*N:ℕ):ℝ)/125)+3*(k:ℝ)*Real.exp (-α*N*(recover-M*rho)))
  let ε₁ := (k:ℝ)*(Real.exp (α*N*recover)+(t₁:ℝ)*ceiling)/Real.exp (α*N*parent)+
    Real.exp (-9*((k*N:ℕ):ℝ)/4000)+2*(k:ℝ)*(d:ℝ)*Real.exp (-2*(N:ℝ)*δ^2/(2*(C:ℝ)))
  have hε₁ : 0 ≤ ε₁ := by dsimp [ε₁,ceiling]; positivity
  have hfirst := general_architecture_first_phase hk N C hN consume produce coeff z γ w hcoeff hγ hw
    hdiag hsym center Q c radius outer α birth recover κ lam rho M A P R U Z L D rmax
    hc hradius houter hα hlam hM hrho hP hR hU hZ hL hA0 hκ hcenter hE hQ hop hactivity hbias hrow
    hsres hscouple habsorb hforce hcopy hquality hz q₀ t₀ hq₀ hd₀ ht₀ hearly hc₀ start rfl hstart
  have hsecond (s : {s : GeneralCountState k d // s ∈ domain₁}) (_ : s.val.2 < 2*(k*N))
      (hs : ∀ i, Q i (generalConcentration s.val i-center i) (generalConcentration s.val i-center i) ≤ recover) :
      (generalSecondPhaseLaw next rate hrate N C (by omega) Q center c radius birth parent
        hc hradius (hbirth.trans houter) hcenter hcoerc q₁ t₁ hq₁ hc₁ s).mass none ≤ ε₁ := by
    exact general_architecture_second_phase hk N C hN hC consume produce coeff z γ w hcoeff hγ hw
      hdiag hsym center Q c radius parent α recover κ lam rho M A P R U Z L D rmax
      hc hradius (hparentouter.trans houter) hα.le hlam hM hrho.le hP hR hU hZ hL hA0 hκ
      hcenter hE hQ hop hactivity hbias hrow hsres hscouple habsorb hforce hcopy
      (fun x hx => hquality x (hsub hx)) (fun x hx => hz x (hsub hx))
      birth lo rpart δ (hbirth.trans houter) hlo hrpart hδ hcoerc hsize hmargin
      (fun x hx => hzlo x (hsub hx)) q₁ t₁ hq₁ ht₁ hc₁ hd₁ s hs
  exact general_two_phase_failure next rate hrate N C (by omega) Q center c radius birth outer parent recover
    hc hradius (hbirth.trans houter) hgap hcenter hcoerc q₀ t₀ q₁ t₁ hq₀ hq₁ hc₀ hc₁ ε₀ ε₁ hε₁
    hsecond start hfirst

end CompositionalMemory
