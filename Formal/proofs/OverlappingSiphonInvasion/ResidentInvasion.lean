import proofs.OverlappingSiphonInvasion.Source
import proofs.OverlappingSiphonInvasion.Membership

noncomputable section
namespace OverlappingSiphonInvasion

def face1 (s u : ℝ) : State := ![s,u,0,0]
def face2 (s u : ℝ) : State := ![s,0,u,0]
def missing1 : Fin 2 → Fin 4 := ![2,3]
def missing2 : Fin 2 → Fin 4 := ![1,3]

def residentBlock1 (p : Rates) (s u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.alpha2*s-p.gamma2*u-p.mu2, p.beta2*s;
     (p.gamma1+p.gamma2)*u, p.eta1*u+p.alpha3*s-p.mu3]

def residentBlock2 (p : Rates) (s u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.alpha1*s-p.gamma1*u-p.mu1, p.beta1*s;
     (p.gamma1+p.gamma2)*u, p.eta2*u+p.alpha3*s-p.mu3]

private theorem normalEntry_of_linear (p : Rates) (y : State) (i j : Fin 4) (q : ℝ)
    (h : ∀ t : ℝ, field p (fun l => y l+if l=j then t else 0) i = q*t) :
    normalEntry source (rateVector p) y i j = q := by
  unfold normalEntry
  simp_rw [source_field,h]
  simp

/-- The actual coordinate derivative at every point of the one-strain face,
for arbitrary rate vectors, before imposing the resident equilibrium equations. -/
theorem source_residentBlock1 (p : Rates) (s u : ℝ) :
    (fun i j : Fin 2 => normalEntry source (rateVector p) (face1 s u)
      (missing1 i) (missing1 j)) = residentBlock1 p s u := by
  funext i j
  fin_cases i <;> fin_cases j <;> apply normalEntry_of_linear <;> intro t <;>
    simp [field,face1,missing1,residentBlock1] <;> ring

theorem source_residentBlock2 (p : Rates) (s u : ℝ) :
    (fun i j : Fin 2 => normalEntry source (rateVector p) (face2 s u)
      (missing2 i) (missing2 j)) = residentBlock2 p s u := by
  funext i j
  fin_cases i <;> fin_cases j <;> apply normalEntry_of_linear <;> intro t <;>
    simp [field,face2,missing2,residentBlock2] <;> ring

/-- Constructive two-dimensional invasion criterion without a Perron theorem.
The covector is positive even when no chosen eigenvector is available. -/
theorem positive_covector_iff (A B C D : ℝ) (hB : 0 < B) (hC : 0 < C) :
    (∃ r : ℝ, 0 < r ∧ 0 < A+r*C ∧ 0 < B+r*D) ↔
      0 ≤ A ∨ 0 ≤ D ∨ A*D < B*C := by
  constructor
  · rintro ⟨r,_,h1,h2⟩
    by_cases hD : 0 ≤ D
    · exact Or.inr (Or.inl hD)
    · have hD' : D < 0 := lt_of_not_ge hD
      have hm1 := mul_pos h1 (neg_pos.mpr hD')
      have hm2 := mul_pos h2 hC
      exact Or.inr (Or.inr (by nlinarith only [hm1,hm2]))
  · intro hinv
    by_cases hD : 0 ≤ D
    · let r := max 0 (-A/C)+1
      have hr : 0 < r := by dsimp [r]; linarith [le_max_left (0:ℝ) (-A/C)]
      have hl : -A/C < r := by dsimp [r]; linarith [le_max_right (0:ℝ) (-A/C)]
      have hh := (div_lt_iff₀ hC).mp hl
      exact ⟨r,hr,by linarith,by nlinarith [mul_nonneg hr.le hD]⟩
    · have hD' : D < 0 := lt_of_not_ge hD
      have hnD : 0 < -D := neg_pos.mpr hD'
      have hdet : A*D < B*C := by
        rcases hinv with hA | hD0 | hd
        · have hm := mul_nonpos_of_nonneg_of_nonpos hA hD'.le
          nlinarith [mul_pos hB hC]
        · exact False.elim (hD hD0)
        · exact hd
      have hinterval : max 0 (-A/C) < B/(-D) := by
        apply max_lt
        · exact div_pos hB hnD
        · apply (div_lt_div_iff₀ hC hnD).mpr
          nlinarith only [hdet]
      obtain ⟨r,hrl,hru⟩ := exists_between hinterval
      have hr := lt_of_le_of_lt (le_max_left (0:ℝ) (-A/C)) hrl
      have hl := (div_lt_iff₀ hC).mp (lt_of_le_of_lt (le_max_right (0:ℝ) (-A/C)) hrl)
      have hu := (lt_div_iff₀ hnD).mp hru
      exact ⟨r,hr,by linarith,by nlinarith only [hu]⟩

theorem positive_covector_margin (A B C D : ℝ) (hB : 0 < B) (hC : 0 < C)
    (hinv : 0 ≤ A ∨ 0 ≤ D ∨ A*D < B*C) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ 2*δ ≤ A+r*C ∧ 2*δ*r ≤ B+r*D := by
  obtain ⟨r,hr,h1,h2⟩ := (positive_covector_iff A B C D hB hC).mpr hinv
  let δ := min (A+r*C) ((B+r*D)/r)/2
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (lt_min h1 (div_pos h2 hr)) (by norm_num)
  have hδ1 := min_le_left (A+r*C) ((B+r*D)/r)
  have hδ2 := min_le_right (A+r*C) ((B+r*D)/r)
  have hm := (le_div_iff₀ hr).mp hδ2
  exact ⟨r,δ,hr,hδ,by dsimp [δ]; linarith,by dsimp [δ]; nlinarith only [hm]⟩

end OverlappingSiphonInvasion
