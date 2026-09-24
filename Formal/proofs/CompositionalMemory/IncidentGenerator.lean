import proofs.CompositionalMemory.SourceEnergy
import proofs.CompositionalMemory.IncidentRates
import proofs.CompositionalMemory.UniformLocalBudget

namespace CompositionalMemory
open FiniteCopy

noncomputable def localIncidentJump {k : ℕ} (m : ℝ) (i : Fin k) (x : Point) :
    IncidentChannel k → Point :=
  Sum.elim (fun j => localMembraneJump m i j x)
    (Sum.elim (fun _ a => (if a=2 then (-1 : ℝ) else 0)/(m/k))
      (fun _ a => (if a=2 then (1 : ℝ) else 0)/(m/k)))

theorem incident_jump_norm {k : ℕ} (m : ℝ) (i : Fin k) (x : Point)
    (hx : normSq x ≤ 4900) (hxz : x 2 ≤ 70) (c : IncidentChannel k) :
    normSq (localIncidentJump m i x c) ≤ (incidentSize m i c)^2 := by
  rcases c with j | j | j
  · exact local_membrane_jump_norm m i j x hx hxz
  all_goals norm_num [localIncidentJump,incidentSize,normSq,Fin.ext_iff]
  simp [div_div_eq_mul_div, neg_div]

/-- Literal incident reactions, with uniform constants and no stochastic premise. -/
theorem literal_incident_exponential {k : ℕ} (hk : 1 ≤ k)
    (E : EnergyData) (γ κ m N r : ℝ) (z w : Fin k → ℝ) (i : Fin k) (x y : Point)
    (hN : 1 ≤ N) (hm : (k : ℝ)*N ≤ m)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (hz : ∀ j, 0 ≤ z j ∧ z j ≤ 4) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j ≤ κ)
    (hr : 0 ≤ r) (hrmax : r ≤ 1/400) (hy : normSq y = r^2)
    (hx : normSq x ≤ 4900) (hxz : x 2 ≤ 70) :
    ∑ c, incidentRate γ m z w i c*
      (Real.exp ((1/1000000000000 : ℝ)*N*
        (E.energy (fun a => y a+localIncidentJump m i x c a)-E.energy y))-1) ≤
      (1/1000000000000 : ℝ)*(N*r^2/4+2*N*(84*(284*γ+8*κ))^2+1) := by
  have hNp : 0 < N := by linarith only [hN]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmpos : 0 < m := lt_of_lt_of_le (mul_pos hkpos hNp) hm
  have hd (c) := incident_size_bounds hk m N i hNp hm c
  apply perturbation_of_jump_sizes (incidentRate γ m z w i)
    (fun c => E.energy (fun a => y a+localIncidentJump m i x c a)-E.energy y)
    (incidentSize m i) N r (284*γ+8*κ) (20164*γ+8*κ)
    hN hr hrmax (by positivity) (incident_noise_budget γ κ hγmax hκmax)
    (incident_rate_nonnegative γ m z w i hγ hmpos.le (fun j => (hz j).1) hw)
    (fun c => (hd c).1) (fun c => (hd c).2)
  · intro c
    exact energy_increment_bound E y (localIncidentJump m i x c) r (incidentSize m i c)
      hr (hd c).1 hy (incident_jump_norm m i x hx hxz c)
  · exact incident_first_moment hk γ m κ z w i hγ hmpos (fun j => (hz j).2) hw hs
  · exact incident_second_moment hk γ m κ N z w i hγ hκ hNp hm (fun j => (hz j).2) hw hs

theorem literal_incident_observable {k : ℕ} (hk : 1 ≤ k)
    (E : EnergyData) (γ κ m N r : ℝ) (z w : Fin k → ℝ) (i : Fin k) (x y : Point)
    (hN : 1 ≤ N) (hm : (k : ℝ)*N ≤ m)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (hz : ∀ j, 0 ≤ z j ∧ z j ≤ 4) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j ≤ κ)
    (hr : 0 ≤ r) (hrmax : r ≤ 1/400) (hy : normSq y = r^2)
    (hx : normSq x ≤ 4900) (hxz : x 2 ≤ 70) :
    ∑ c, incidentRate γ m z w i c*
      (Real.exp ((1/1000000000000 : ℝ)*N*E.energy (fun a => y a+localIncidentJump m i x c a))-
        Real.exp ((1/1000000000000 : ℝ)*N*E.energy y)) ≤
      (1/1000000000000 : ℝ)*Real.exp ((1/1000000000000 : ℝ)*N*E.energy y)*
        (N*r^2/4+2*N*(84*(284*γ+8*κ))^2+1) := by
  let a : ℝ := 1/1000000000000
  have hid (c : IncidentChannel k) :
      Real.exp (a*N*E.energy (fun j => y j+localIncidentJump m i x c j))-Real.exp (a*N*E.energy y) =
      Real.exp (a*N*E.energy y)*
        (Real.exp (a*N*(E.energy (fun j => y j+localIncidentJump m i x c j)-E.energy y))-1) := by
    rw [mul_sub,mul_one,← Real.exp_add]
    congr 2
    ring
  have h := literal_incident_exponential hk E γ κ m N r z w i x y hN hm
    hγ hγmax hκ hκmax hz hw hs hr hrmax hy hx hxz
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (a*N*E.energy y)).le
  change ∑ c, incidentRate γ m z w i c*(Real.exp (a*N*E.energy
    (fun j => y j+localIncidentJump m i x c j))-Real.exp (a*N*E.energy y)) ≤ _
  simp_rw [hid]
  rw [Finset.mul_sum] at hh
  have hsum : (∑ c, incidentRate γ m z w i c*(Real.exp (a*N*E.energy y)*
      (Real.exp (a*N*(E.energy (fun j => y j+localIncidentJump m i x c j)-E.energy y))-1))) =
      ∑ c, Real.exp (a*N*E.energy y)*(incidentRate γ m z w i c*
        (Real.exp (a*N*(E.energy (fun j => y j+localIncidentJump m i x c j)-E.energy y))-1)) := by
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hsum]
  nlinarith only [hh]

end CompositionalMemory
