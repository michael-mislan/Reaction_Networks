import proofs.RAF1519.Refinement.PhaseAdjoint
import proofs.RAF1519.Refinement.CompensatedMaterial

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def phaseDot (b x : Fin 4 → ℝ) : ℝ := ∑ p, b p*x p

theorem phaseDot_sub (b x y : Fin 4 → ℝ) :
    phaseDot b (fun p => x p-y p) = phaseDot b x-phaseDot b y := by
  simp only [phaseDot,mul_sub,Finset.sum_sub_distrib]

theorem phaseDot_noise (b x y : Fin 4 → ℝ) (ε : ℝ)
    (hn : ∀ p, |x p-y p| ≤ ε) :
    |phaseDot b x-phaseDot b y| ≤ (∑ p, |b p|)*ε := by
  rw [← phaseDot_sub]
  calc
    _ ≤ ∑ p, |b p*(x p-y p)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, |b p| * ε := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hn p) (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

theorem phaseDot_diffusion {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (b : Fin 4 → ℝ) (x : ι → Fin 4 → ℝ) (i : ι) :
    phaseDot b (fun p => graphDiffusion k (fun j => x j p) i) =
      graphDiffusion k (fun j => phaseDot b (x j)) i := by
  unfold phaseDot graphDiffusion
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem phase_adjoint_pairing (b db x : Fin 4 → ℝ) :
    phaseDot db x+phaseDot b (fun p => ∑ q, phaseM p q*x q) =
      ∑ q, (db q+∑ p, b p*phaseM p q)*x q := by
  have he : phaseDot b (fun p => ∑ q, phaseM p q*x q) =
      ∑ q, (∑ p, b p*phaseM p q)*x q := by
    unfold phaseDot
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he]
  simp only [phaseDot,add_mul,Finset.sum_add_distrib]

/-- A scalar graph drift bound obtained by weighting the four physical phase
    inequalities. The error uses the same coordinate noise at every node. -/
theorem phase_weighted_drift {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (Δ ε : ℝ) (_hΔ : 0 ≤ Δ) (hε : 0 ≤ ε)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (b db : Fin 4 → ℝ) (hb : ∀ p, 0 ≤ b p) (hbsum : (∑ p, b p) ≤ 3/2)
    (hdb : (∑ p, |db p|) ≤ 132)
    (hres : ∀ q, 0 ≤ db q+∑ p, b p*phaseM p q)
    (X F v : ι → Fin 4 → ℝ) (hX : ∀ i p, 0 ≤ X i p)
    (hn : ∀ i p, |X i p-F i p| ≤ ε)
    (hv : ∀ i p, (∑ q, phaseM p q*X i q)+graphDiffusion k (fun j => X j p) i ≤ v i p)
    (i : ι) :
    graphDiffusion k (fun j => phaseDot b (F j)) i-(132+3*Δ)*ε ≤
      phaseDot db (F i)+phaseDot b (v i) := by
  have hweighted : phaseDot b (fun p => (∑ q, phaseM p q*X i q)+graphDiffusion k (fun j => X j p) i)
      ≤ phaseDot b (v i) :=
    Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hv i p) (hb p))
  have hsplit : phaseDot b (fun p => (∑ q, phaseM p q*X i q)+graphDiffusion k (fun j => X j p) i) =
      phaseDot b (fun p => ∑ q, phaseM p q*X i q)+graphDiffusion k (fun j => phaseDot b (X j)) i := by
    rw [show phaseDot b (fun p => (∑ q, phaseM p q*X i q)+graphDiffusion k (fun j => X j p) i) =
      phaseDot b (fun p => ∑ q, phaseM p q*X i q)+phaseDot b (fun p => graphDiffusion k (fun j => X j p) i) by
        simp only [phaseDot,mul_add,Finset.sum_add_distrib]]
    rw [phaseDot_diffusion]
  rw [hsplit] at hweighted
  have hpair : 0 ≤ phaseDot db (X i)+phaseDot b (fun p => ∑ q, phaseM p q*X i q) := by
    rw [phase_adjoint_pairing]
    exact Finset.sum_nonneg (fun q _ => mul_nonneg (hres q) (hX i q))
  have hdnoise := (phaseDot_noise db (X i) (F i) ε (hn i)).trans
    (mul_le_mul_of_nonneg_right hdb hε)
  have hbn : ∀ j, |phaseDot b (X j)-phaseDot b (F j)| ≤ (3/2)*ε := by
    intro j
    have hh := phaseDot_noise b (X j) (F j) ε (hn j)
    simp only [abs_of_nonneg (hb _)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hbsum hε)
  have hD := graphDiffusion_noise_bound k hk Δ ((3/2)*ε) (by positivity) hdegree
    (fun j => phaseDot b (X j)-phaseDot b (F j)) hbn i
  rw [graphDiffusion_sub] at hD
  have hdlo := (abs_le.mp hdnoise).2
  have hDlo := (abs_le.mp hD).1
  nlinarith

end
end RAF1519.Refinement
