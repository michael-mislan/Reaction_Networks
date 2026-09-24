import proofs.CompositionalMemory.GenericArchitectureExponential
import proofs.CompositionalMemory.WordLineage

namespace CompositionalMemory
open FiniteCopy

/-- Construct clocks for the actual generation law and derive designated-lineage accuracy. -/
theorem general_architecture_lineage {k d : ℕ} {ι : Type*} [Fintype ι]
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
      ∀ j, 0 ≤ generalConcentration s j z ∧ generalConcentration s j z ≤ Z)     (parent lo rpart δ : ℝ) (hbirth : birth < outer) (hgap : recover < parent)
    (hlo : 0 ≤ lo) (hrpart : 0 ≤ rpart) (hδ : 0 < δ)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (hsize : parent ≤ c*rpart^2) (hmargin : parent+2*L*rpart*δ+L*δ^2 < birth)
    (hzlo : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) outer,
      ∀ j, lo ≤ generalConcentration s j z)     (hcore : M*rho < recover) (cgen : ℝ)
    (hc₀ : cgen ≤ α*(outer-birth)/2) (hc₁ : cgen ≤ α*(parent-recover)/2)
    (hcr : cgen ≤ α*(recover-M*rho)) (hce : cgen ≤ 1/125) (hcl : cgen ≤ 9/4000)
    (hcp : cgen ≤ δ^2/(C:ℝ)) :
    let next := generalGlobalNext consume produce z
    let rate := generalGlobalRate consume coeff z γ w
    let hrate := general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw
    let domain₀ := generalProductDomain N C center (fun i y => Q i y y) outer
    let domain₁ := generalProductDomain N C center (fun i y => Q i y y) parent
    ∀ (t₀ t₁ : NNReal)
      (_ : 4*birth ≤ lam*rho*(t₀:ℝ)) (_ : γ*Z*(t₀:ℝ) ≤ 2/5)
      (_ : γ*lo*(t₁:ℝ)=11/10),
    ∃ (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
      (hclock₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₀).total s ≤ q₀)
      (hclock₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₁).total s ≤ q₁),
    let K := generalGenerationLaw hk next rate hrate N C hN Q center c radius birth outer parent recover
      hc hradius hbirth.le houter hgap hcenter hcoerc q₀ t₀ q₁ t₁ hq₀ hq₁ hclock₀ hclock₁
    let ε := (k:ℝ)*(7+2*(d:ℝ)+(lam*rho/2)*((t₀:ℝ)/(outer-birth)+(t₁:ℝ)/(parent-recover)))*Real.exp (-cgen*N)
    (∀ n, (K n).mass none ≤ ε) ∧
    ∀ (G : ℕ) n, 1-(G:ℝ)*ε ≤ wordLineageSuccess K G n := by
  classical
  intro next rate hrate domain₀ domain₁ t₀ t₁ ht₀ hearly ht₁
  let M₀ := retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₀
  let M₁ := retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₁
  obtain ⟨q₀,hq₀,hd₀,hclock₀⟩ := M₀.exists_clock (α*lam*N*rho/4)
  obtain ⟨q₁,hq₁,hd₁,hclock₁⟩ := M₁.exists_clock (19*(γ*lo)*((k*N:ℕ):ℝ)/400)
  refine ⟨q₀,q₁,hq₀,hq₁,hclock₀,hclock₁,?_⟩
  dsimp only
  have hbound := general_architecture_generation_exponential hk N C hN hC consume produce coeff z γ w
    hcoeff hγ hw hdiag hsym center Q c radius outer α birth recover κ lam rho M A P R U Z L D rmax
    hc hradius houter hα hlam hM hrho hP hR hU hZ hL hA0 hκ hcenter hQ hop hactivity hbias hrow
    hsres hscouple habsorb hforce hcopy hquality hz parent lo rpart δ hbirth hgap hlo hrpart hδ
    hcoerc hsize hmargin hzlo hcore cgen hc₀ hc₁ hcr hce hcl hcp
    q₀ t₀ q₁ t₁ hq₀ hq₁ hd₀ ht₀ hearly ht₁ hd₁ hclock₀ hclock₁
  refine ⟨hbound,?_⟩
  intro G n
  exact word_lineage_bound _ _ (by
    have hg₀ : 0 < outer-birth := sub_pos.mpr hbirth
    have hg₁ : 0 < parent-recover := sub_pos.mpr hgap
    positivity) hbound G n

end CompositionalMemory
