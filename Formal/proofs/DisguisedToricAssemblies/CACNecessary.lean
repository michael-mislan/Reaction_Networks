import proofs.DisguisedToricAssemblies.CACFluxConstruction
import proofs.DisguisedToricAssemblies.ConvexDual

namespace DisguisedToricAssemblies
open CoreCouplingCAC

def dualH : Fin 8 → Fin 4 → ℝ :=
  ![![1,1,1,1], ![1,1,0,1], ![-1,-1,0,1], ![1,1,0,1],
    ![1,1,0,1], ![1,1,-1,-1], ![-1,-1,1,1], ![-1,-1,1,1]]
def dualP : Fin 8 → ℝ := ![0,-1,-1,0,-1,0,-1,0]

def currentH : Fin 8 → Fin 4 → ℝ :=
  ![![0,0,1,0], ![0,1,0,0], ![0,1,0,0], ![0,1,0,0],
    ![0,1,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,1,0]]
def currentP : Fin 8 → ℝ := ![0,0,-1,0,0,0,0,0]

theorem dual_support (i j : Fin 8) :
    0 ≤ (∑ k, dualH i k*(complexes j k-complexes i k))+dualP j-dualP i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [dualH, dualP, complexes, Fin.sum_univ_succ]

theorem current_support (i j : Fin 8) :
    0 ≤ (∑ k, currentH i k*(complexes j k-complexes i k))+currentP j-currentP i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [currentH, currentP, complexes, Fin.sum_univ_succ]

theorem dual_row (p : Rates) (x : State) (i : Fin 8) :
    (∑ k, dualH i k*(activity x i*coefficient p i k)) =
      (![p.a+p.b,-x.A,0,p.u*x.z,-(2+p.d)*x.H,p.v*x.z^2,
        x.B-p.e*x.B,p.e*x.A^2] : Fin 8 → ℝ) i := by
  fin_cases i <;> norm_num [dualH, activity, coefficient, Fin.sum_univ_succ] <;> ring

theorem current_row (p : Rates) (x : State) (i : Fin 8) :
    (∑ k, currentH i k*(activity x i*coefficient p i k)) =
      (![0,x.A,-x.B*x.z,0,0,0,0,0] : Fin 8 → ℝ) i := by
  fin_cases i <;> norm_num [currentH, activity, coefficient, Fin.sum_univ_succ]

theorem dual_evaluation (p : Rates) (x : State) (hs : Stationary p x) :
    (∑ i, ∑ k, dualH i k*(activity x i*coefficient p i k)) =
      2*(x.B-p.e*(x.B-x.A^2)) := by
  simp_rw [dual_row]
  norm_num [Fin.sum_univ_succ]
  obtain ⟨ha,hb,_,hh⟩ := hs
  dsimp [fA] at ha
  dsimp [fB] at hb
  dsimp [fH] at hh
  linear_combination ha+hb+hh

theorem current_evaluation (p : Rates) (x : State) :
    (∑ i, ∑ k, currentH i k*(activity x i*coefficient p i k)) = x.A-x.B*x.z := by
  simp_rw [current_row]
  norm_num [Fin.sum_univ_succ]
  ring

theorem certificate_current_nonneg (p : Rates) (x : State) (q : Fin 8 → Fin 8 → ℝ)
    (hc : FluxCertificate p x q) : 0 ≤ x.A-x.B*x.z := by
  have hn := supporting_dual_nonneg q complexes currentH
    (fun i k => activity x i*coefficient p i k) currentP
    hc.1 hc.2.2.1 hc.2.2.2 current_support
  rwa [current_evaluation] at hn

theorem certificate_reservoir_bound (p : Rates) (x : State)
    (q : Fin 8 → Fin 8 → ℝ) (hc : FluxCertificate p x q)
    (hs : Stationary p x) : p.e*(x.B-x.A^2) ≤ x.B := by
  have hn := supporting_dual_nonneg q complexes dualH
    (fun i k => activity x i*coefficient p i k) dualP
    hc.1 hc.2.2.1 hc.2.2.2 dual_support
  rw [dual_evaluation p x hs] at hn
  linarith

end DisguisedToricAssemblies
