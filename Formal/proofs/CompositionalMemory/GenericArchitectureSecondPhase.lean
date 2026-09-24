import proofs.CompositionalMemory.GenericArchitectureExit
import proofs.CompositionalMemory.GenericSecondPhaseBound
import proofs.CompositionalMemory.GenericLateClock
import proofs.CompositionalMemory.GenericMembraneRates

namespace CompositionalMemory
open FiniteCopy

/-- Second-phase failure from literal safety, membrane timing and partition. -/
theorem general_architecture_second_phase {k d : ℕ} {ι : Type*} [Fintype ι]
    (hk : 1 ≤ k) (N C : ℕ) (hN : 1 ≤ N) (hC : 0 < C)
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hcoeff : ∀ i j, 0 ≤ coeff i j) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (center : Fin k → Fin d → ℝ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (c radius b α a κ lam rho M A P R U Z L D rmax : ℝ)
    (hc : 0 < c) (hradius : 0 ≤ radius) (hb : b ≤ c*radius^2)
    (hα : 0 ≤ α) (hlam : 0 < lam) (hM : 0 < M) (hrho : 0 ≤ rho)
    (hP : 0 ≤ P) (hR : 0 ≤ R) (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hA0 : 0 ≤ A) (hκ : 0 ≤ κ)
    (hcenter : ∀ i j, center i j ≤ (C:ℝ)-radius)
    (hE : ∀ i y j, c*(y j)^2 ≤ Q i y y)
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
    (hquality : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) b, ∀ i,
      let v := (s.2:ℝ)/k
      let u := generalConcentration s i
      let y := u-center i
      let ν := fun j a => (produce i j a:ℝ)-(consume i j a:ℝ)
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ rmax ∧ ‖y‖ ≤ r ∧ ‖u‖ ≤ U ∧
        (∀ a, (s.1 i a:ℝ)/v ≤ U) ∧
        (∀ j, |Q i y (ν j)| ≤ P*r) ∧ (∀ j, |Q i (ν j) (ν j)| ≤ R) ∧
        2*Q i y (∑ j, (coeff i j*(∏ a, ((s.1 i a:ℝ)/v)^(consume i j a))) • ν j) ≤ -lam*r^2 ∧
        Q i y y ≤ M*r^2)
    (hz : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) b,
      ∀ j, 0 ≤ generalConcentration s j z ∧ generalConcentration s j z ≤ Z)     (birth lo rpart δ : ℝ) (hbirth : birth ≤ c*radius^2)
    (hlo : 0 ≤ lo) (hrpart : 0 ≤ rpart) (hδ : 0 < δ)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (hsize : b ≤ c*rpart^2) (hmargin : b+2*L*rpart*δ+L*δ^2 < birth)
    (hzlo : ∀ s ∈ generalProductDomain N C center (fun i y => Q i y y) b,
      ∀ j, lo ≤ generalConcentration s j z) :
    let next := generalGlobalNext consume produce z
    let rate := generalGlobalRate consume coeff z γ w
    let hrate := general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw
    let domain := generalProductDomain N C center (fun i y => Q i y y) b
    let ceiling := α*((A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
      α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N+
      N*(2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2/lam)*Real.exp (α*N*(M*rho))
    ∀ (q t : NNReal) (hq : 0 < (q:ℝ)) (_ : γ*lo*(t:ℝ)=11/10)
      (hclock : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain).total s ≤ q)
      (_ : 19*(γ*lo)*((k*N:ℕ):ℝ)/400 ≤ q)
      (s : {s : GeneralCountState k d // s ∈ domain}),
    (∀ i, Q i (generalConcentration s.val i-center i) (generalConcentration s.val i-center i) ≤ a) →
    (generalSecondPhaseLaw next rate hrate N C (by omega) Q center c radius birth b hc hradius hbirth hcenter hcoerc
      q t hq hclock s).mass none ≤
      (k:ℝ)*(Real.exp (α*N*a)+(t:ℝ)*ceiling)/Real.exp (α*N*b)+
      Real.exp (-9*((k*N:ℕ):ℝ)/4000)+2*(k:ℝ)*(d:ℝ)*Real.exp (-2*(N:ℝ)*δ^2/(2*(C:ℝ))) := by
  classical
  intro next rate hrate domain ceiling q t hq htime hclock hdecay s hstart
  have hraw := general_second_phase_failure hk next rate hrate N C (by omega) hC Q hQ center
    c radius birth b L rpart δ hc hradius hbirth hL hrpart hδ hcenter hcoerc hop hsize hmargin
    q t hq hclock s
  have hout := general_architecture_product_exit hk N C hN consume produce coeff z γ w hcoeff hγ hw
    hdiag hsym center Q c radius b α a κ lam rho M A P R U Z L D rmax
    hc hradius hb hα hlam hM hrho hP hR hU hZ hL hA0 hκ hcenter hE hQ hop hactivity hbias hrow
    hsres hscouple habsorb hforce hcopy hquality hz q t hq hclock s hstart
  have hratebound (x) (hx : x ∈ domain) (_ : x.2 < 2*(k*N)) :
      (γ*lo)*((k*N:ℕ):ℝ) ≤ ∑ i, γ*(x.1 i z:ℝ) := by
    have hmrange := (mem_generalProductDomain hk N C hN center (fun i y => Q i y y)
      c radius b hc hradius hb hcenter hE x).mp hx
    exact (general_membrane_bounded_activity hk z x (k*N) (Nat.mul_pos (by omega) (by omega))
      ⟨hmrange.1,hmrange.2.1⟩ γ lo Z hγ hlo hZ (fun j => ⟨hzlo x hx j,(hz x hx j).2⟩)).1
  have hmrange := (mem_generalProductDomain hk N C hN center (fun i y => Q i y y)
    c radius b hc hradius hb hcenter hE s.val).mp s.property
  have hlate := general_late_division_tail consume produce coeff z hcoeff γ (γ*lo) w hγ hw
    N domain hratebound q t hq htime hclock hdecay s hmrange.1
  have hout' : ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain).uniformize
      q hq hclock).poissonized (q*t) (FiniteKernel.eventIndicator {none}) (some s) ≤
      (k:ℝ)*(Real.exp (α*N*a)+(t:ℝ)*ceiling)/Real.exp (α*N*b) := by
    apply (le_div_iff₀ (Real.exp_pos (α*N*b))).mpr
    nlinarith only [hout]
  exact hraw.trans (add_le_add (add_le_add hout' hlate) le_rfl)

end CompositionalMemory
