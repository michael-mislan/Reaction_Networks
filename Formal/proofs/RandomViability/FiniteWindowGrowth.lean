import proofs.RandomViability.CompensatedPotentialInterval
import proofs.RandomViability.CompensatedOutput

namespace RandomViability
set_option maxHeartbeats 100000

def windowDuration (h : ℕ → ℝ) (A B : ℝ) (K : ℕ) : ℝ :=
  (∑ i : Fin K,h i)+B-A

def windowMassIntegral (M h : ℕ → ℝ) (A B : ℝ) (K : ℕ) : ℝ :=
  (∑ i : Fin K,M i*h i)+M K*B-M 0*A

/-- Telescope local gains, retaining both partial endpoint intervals. The
single-holding case K=0 is included and needs A<=B. -/
theorem finite_window_growth (P : ℕ → ℝ → ℝ) (M h : ℕ → ℝ)
    (A q c : ℝ) (K : ℕ) (B : ℝ)
    (hA : A ≤ h 0) (hh : ∀ i,0 ≤ h i)
    (hgain : ∀ i ≤ K,∀ a b,(if i=0 then A else 0) ≤ a → a ≤ b → b ≤ h i →
      (b-a)*(q-c*M i) ≤ P i b-P i a)
    (hlink : ∀ i < K,P i (h i) = P (i+1) 0)
    (hB0 : 0 ≤ B) (hBh : B ≤ h K) (hAB : K=0 → A ≤ B) :
    q*windowDuration h A B K-c*windowMassIntegral M h A B K ≤ P K B-P 0 A := by
  induction K generalizing B with
  | zero =>
    have hg := hgain 0 le_rfl A B (by simp) (hAB rfl) hBh
    simp only [windowDuration,windowMassIntegral,Fin.sum_univ_zero,zero_add]
    nlinarith only [hg]
  | succ K ih =>
    have hp := ih (h K)
      (fun i hi => hgain i (by omega))
      (fun i hi => hlink i (by omega)) (hh K) le_rfl
      (by intro hk; simpa only [hk] using hA)
    have hg := hgain (K+1) le_rfl 0 B (by simp) hB0 hBh
    rw [hlink K (by omega)] at hp
    simp only [windowDuration,windowMassIntegral,Fin.sum_univ_castSucc] at hp ⊢
    change q*((∑ i : Fin K,h i)+h K+B-A)-
      c*((∑ i : Fin K,M i*h i)+M K*h K+M (K+1)*B-M 0*A) ≤ _
    nlinarith only [hp,hg]

theorem finite_window_mass_bound (P : ℕ → ℝ → ℝ) (M h : ℕ → ℝ)
    (A B : ℝ) (K : ℕ)
    (hgain : ((19/10 : ℝ)-480*(1/500000000 : ℝ))*windowDuration h A B K-
      640*windowMassIntegral M h A B K ≤ P K B-P 0 A)
    (hwindow : windowDuration h A B K = 99) (hpenalty : P K B-P 0 A ≤ 54) :
    99*((19/10 : ℝ)-480*(1/500000000 : ℝ))-54 ≤
      640*windowMassIntegral M h A B K := by
  rw [hwindow] at hgain
  linarith only [hgain,hpenalty]

end RandomViability
