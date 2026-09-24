import proofs.CompositionalMemory.GenericCountRecoveryDrift
import proofs.CompositionalMemory.GenericRetainedRecovery
import proofs.CompositionalMemory.GenericRecoveryBudget
import proofs.CompositionalMemory.GenericCountExit

namespace CompositionalMemory
open FiniteCopy

/-- Timed recovery among active safe states under the actual architecture law.
Unsafe exits and frozen divisions carry zero recovery reward. -/
theorem general_architecture_product_recovery {k d : ℕ} {ι : Type*} [Fintype ι]
    (hk : 1 ≤ k) (N C : ℕ) (hN : 1 ≤ N)
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hcoeff : ∀ i j, 0 ≤ coeff i j) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (center : Fin k → Fin d → ℝ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (c radius b α a recover κ lam rho M A P R U Z L D rmax : ℝ)
    (hc : 0 < c) (hradius : 0 ≤ radius) (hb : b ≤ c*radius^2)
    (hα : 0 < α) (hlam : 0 < lam) (hM : 0 < M) (hrho : 0 < rho)
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
      ∀ j, 0 ≤ generalConcentration s j z ∧ generalConcentration s j z ≤ Z) :
    let next := generalGlobalNext consume produce z
    let rate := generalGlobalRate consume coeff z γ w
    let hrate := general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw
    let domain := generalProductDomain N C center (fun i y => Q i y y) b
    let decay := α*lam*N*rho/4
    ∀ (q t : NNReal) (hq : 0 < (q:ℝ)) (_ : decay ≤ q) (_ : 4*a ≤ lam*rho*(t:ℝ))
      (hclock : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain).total s ≤ q)
      (s : {s : GeneralCountState k d // s ∈ domain}),
    (∀ i, Q i (generalConcentration s.val i-center i) (generalConcentration s.val i-center i) ≤ a) →
    ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain).uniformize
      q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {x | ∃ i, Real.exp (α*(N:ℝ)*recover) ≤
        retainedActiveObservable (fun s => s.2 < 2*(k*N)) domain
          (fun s => Real.exp (α*(N:ℝ)*Q i (generalConcentration s i-center i)
            (generalConcentration s i-center i))) x}) (some s) ≤
      3*(k:ℝ)*Real.exp (-α*(N:ℝ)*(recover-M*rho)) := by
  classical
  intro next rate hrate domain decay q t hq hdecay htime hclock s hstart
  let ceiling := α*((A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
      α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N+
      N*(2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2/lam)*Real.exp (α*N*(M*rho))
  let plateau := (ceiling+decay*Real.exp (α*N*(M*rho)))/decay
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdp : 0 < decay := by dsimp [decay]; positivity
  have hceiling : 0 ≤ ceiling := by dsimp [ceiling]; positivity
  have hplateau : 0 ≤ plateau := by dsimp [plateau]; positivity
  let probability := ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain).uniformize
      q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {x | ∃ i, Real.exp (α*(N:ℝ)*recover) ≤
        retainedActiveObservable (fun s => s.2 < 2*(k*N)) domain
          (fun s => Real.exp (α*(N:ℝ)*Q i (generalConcentration s i-center i)
            (generalConcentration s i-center i))) x}) (some s)
  have hraw : Real.exp (α*(N:ℝ)*recover)*probability ≤
      (k:ℝ)*(Real.exp (-decay*(t:ℝ))*Real.exp (α*(N:ℝ)*a)+plateau) := by
    apply retained_product_recovery next rate hrate (fun s => s.2 < 2*(k*N)) domain
      (fun i s => Real.exp (α*(N:ℝ)*Q i (generalConcentration s i-center i)
        (generalConcentration s i-center i)))
      (Real.exp (α*(N:ℝ)*recover)) decay plateau (Real.exp (α*(N:ℝ)*a))
      (fun _ _ => (Real.exp_pos _).le) hdp.le hplateau (Real.exp_pos _).le _
      q t hq hdecay hclock s _
    · intro x hx _ i
      have hmrange := (mem_generalProductDomain hk N C hN center (fun i y => Q i y y)
        c radius b hc hradius hb hcenter hE x).mp hx
      have hm : 0 < x.2 := lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hmrange.1
      have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hNv : (N:ℝ) ≤ (x.2:ℝ)/k := (le_div_iff₀ hkpos).mpr (by
        have hh : (k:ℝ)*N ≤ x.2 := by exact_mod_cast hmrange.1
        nlinarith only [hh])
      obtain ⟨r,hr,hrr,hy,hu,hcoord,hcross,hquad,hd,henergy⟩ := hquality x hx i
      have hh := general_count_recovery_drift hk consume produce coeff z γ w hdiag hsym x hm i
        (center i) (Q i) α N κ lam r rho M A P R U Z L D (hQ i) hNp hNv hP hα.le hlam hγ hR
        hU hZ hL hr (hcoeff i) (hactivity i) (hbias i) hcoord hcross hquad hd (hw i) (hz x hx)
        (hrow i) (hop i) hy hu (hsres r hr hrr) (hscouple r hr hrr) habsorb
        hM hrho.le henergy hforce hcopy
      have heq : decay*plateau=ceiling+decay*Real.exp (α*N*(M*rho)) := by
        dsimp [plateau]
        field_simp
      rw [heq]
      convert hh using 1
      dsimp [ceiling,decay]
      ring
    · intro i
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hstart i) (by positivity))
  have hpbound : plateau ≤ 2*Real.exp (α*N*(M*rho)) := recovery_plateau_bound
    α N lam rho (2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)
    (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)
    (2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ) (M*rho)
    hα hNp hlam hrho hforce hcopy
  have hevent := hraw.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hpbound)
    (Nat.cast_nonneg k))
  exact recovery_probability_exponential probability k α N lam rho a recover (M*rho) t
    (Nat.cast_nonneg k) hα.le hNp.le (mul_nonneg hM.le hrho.le) htime hevent

end CompositionalMemory
