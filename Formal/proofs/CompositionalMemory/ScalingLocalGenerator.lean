import proofs.CompositionalMemory.IncidentGenerator
import proofs.CompositionalMemory.BirthResident

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set

/-- Local action of the coupled reaction generator in tau time. The row w
represents both directions of a symmetric exchange graph. z is computed from
all modules' literal integer counts in the shared volume. -/
noncomputable def coupledLocalGenerator {k : ℕ} (γ m : ℝ) (w : Fin k → ℝ)
    (i : Fin k) (n : Fin k → Counts) (W : Point → ℝ) : ℝ :=
  let x := effectiveConcentration (m/k) (n i)
  let z := fun j => effectiveConcentration (m/k) (n j) 2
  effectiveGenerator (1/100000) (m/k) W x +
    ∑ c, incidentRate γ m z w i c*(W (fun a => x a+localIncidentJump m i x c a)-W x)

theorem coupled_bound_from_resident {k : ℕ} (hk : 1 ≤ k)
    (E : EnergyData) (γ κ m N r : ℝ) (w : Fin k → ℝ) (i : Fin k)
    (n : Fin k → Counts) (s : Point)
    (hN : 1 ≤ N) (hm : (k : ℝ)*N ≤ m)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (hz : ∀ j, 0 ≤ effectiveConcentration (m/k) (n j) 2 ∧
      effectiveConcentration (m/k) (n j) 2 ≤ 4)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j ≤ κ)
    (hr : 0 ≤ r) (hrmax : r ≤ 1/400)
    (hy : normSq (fun a => effectiveConcentration (m/k) (n i) a-s a) = r^2)
    (hx : normSq (effectiveConcentration (m/k) (n i)) ≤ 4900)
    (hres : effectiveGenerator (1/100000) (m/k)
      (fun x => Real.exp ((1/1000000000000 : ℝ)*N*E.energy (fun a => x a-s a)))
      (effectiveConcentration (m/k) (n i)) ≤
      (1/1000000000000 : ℝ)*Real.exp ((1/1000000000000 : ℝ)*N*
        E.energy (fun a => effectiveConcentration (m/k) (n i) a-s a))*(-N*r^2/2+100000000)) :
    coupledLocalGenerator γ m w i n
      (fun x => Real.exp ((1/1000000000000 : ℝ)*N*E.energy (fun a => x a-s a))) ≤
      (1/1000000000000 : ℝ)*Real.exp ((1/1000000000000 : ℝ)*N*
        E.energy (fun a => effectiveConcentration (m/k) (n i) a-s a))*
        (-N*r^2/4+200000000+1200000000*N*(γ+κ)^2) := by
  let x := effectiveConcentration (m/k) (n i)
  let y : Point := fun a => x a-s a
  let z := fun j => effectiveConcentration (m/k) (n j) 2
  have hinc := literal_incident_observable hk E γ κ m N r z w i x y hN hm
    hγ hγmax hκ hκmax hz hw hs hr hrmax hy hx (by have h := (hz i).2; dsimp [x]; linarith only [h])
  have hfun (c : IncidentChannel k) :
      (fun a => x a+localIncidentJump m i x c a-s a) =
        (fun a => y a+localIncidentJump m i x c a) := by
    funext a
    dsimp [y]
    ring
  unfold coupledLocalGenerator
  dsimp only
  change effectiveGenerator (1/100000) (m/k) _ x +
    (∑ c, incidentRate γ m z w i c*(Real.exp ((1/1000000000000 : ℝ)*N*
      E.energy (fun a => x a+localIncidentJump m i x c a-s a))-
      Real.exp ((1/1000000000000 : ℝ)*N*E.energy y))) ≤ _
  simp_rw [hfun]
  exact combine_uniform_local_budget N r γ κ (Real.exp ((1/1000000000000 : ℝ)*N*E.energy y))
    _ _ (by linarith only [hN]) hγ hκ (Real.exp_pos _).le hres hinc

theorem coordinate_box_norm (x : Point) (hx : ∀ a, |x a| ≤ 35) : normSq x ≤ 4900 := by
  have hs (a) : (x a)^2 ≤ 1225 := by
    have h := mul_self_le_mul_self (abs_nonneg (x a)) (hx a)
    simpa only [← pow_two,sq_abs,show (35 : ℝ)^2=1225 by norm_num] using h
  unfold normSq
  linarith only [hs 0,hs 1,hs 2,hs 3]

end CompositionalMemory
