import proofs.SandwichImmunoassay.Obstructions

noncomputable section

set_option maxHeartbeats 80000

namespace SandwichImmunoassay

/-- All calibrated parameters, occupancies, and both observed raw readings of a specimen. -/
structure Specimen where
  x : ℝ
  rho : ℝ
  C : ℝ
  D : ℝ
  K : ℝ
  J : ℝ
  d : ℝ
  g : ℝ
  r : ℝ
  p : ℝ
  q : ℝ
  pd : ℝ
  qd : ℝ
  e1 : ℝ
  ed : ℝ
  x_nonneg : 0 ≤ x
  rho_lo : 4/5 ≤ rho
  rho_hi : rho ≤ 1
  c_box : InBox C
  d_box : InBox D
  k_box : InBox K
  j_box : InBox J
  dilution_lo : 9 ≤ d
  dilution_hi : d ≤ 11
  gain_lo : 1 ≤ g
  drift_lo : 19/20 ≤ r
  drift_hi : r ≤ 21/20
  neat : Reaction (rho*x) C D K J p q
  diluted : Reaction (rho*x/d) C D K J pd qd
  error_neat : |e1| ≤ 1/10000
  error_diluted : |ed| ≤ 1/10000

def Specimen.y1 (s : Specimen) : ℝ := s.g * signal (s.rho*s.x) s.p s.q + s.e1
def Specimen.yd (s : Specimen) : ℝ := s.g*s.r * signal (s.rho*s.x/s.d) s.pd s.qd + s.ed
def Specimen.contrast (s : Specimen) : ℝ := s.yd-s.y1
def Design (x : ℝ) : Prop := x ≤ 1/10 ∨ (25 ≤ x ∧ x ≤ 100)

theorem specimen_exists (x rho : ℝ) (hx : 0 ≤ x) (hr0 : 4/5 ≤ rho)
    (hr1 : rho ≤ 1) : ∃ s : Specimen, s.x=x ∧ s.rho=rho := by
  have u0 : 0 ≤ rho*x := mul_nonneg (by linarith) hx
  obtain ⟨p,q,h⟩ := reaction_exists u0 (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
  obtain ⟨pd,qd,j⟩ := reaction_exists (div_nonneg u0 (by norm_num : (0:ℝ)≤10))
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
  refine ⟨⟨x,rho,1,1,1,1,10,1,1,p,q,pd,qd,0,0,hx,hr0,hr1,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,h,j,?_,?_⟩,rfl,rfl⟩ <;> norm_num [InBox]

theorem contrast_low (s : Specimen) (hx : s.x ≤ 1/10) : s.contrast ≤ 1/5000 := by
  have u := native_low s.x_nonneg hx (by linarith [s.rho_lo]) s.rho_hi
  have margin := low_source_margin s.neat s.diluted s.c_box s.d_box s.k_box s.j_box
    u.2 s.dilution_lo s.drift_hi
  have g0 : 0 ≤ s.g := by linarith [s.gain_lo]
  have gm := mul_nonpos_of_nonneg_of_nonpos g0 margin
  have e1 := abs_le.mp s.error_neat
  have ed := abs_le.mp s.error_diluted
  simp only [mul_sub, ← mul_assoc] at gm
  dsimp [Specimen.contrast, Specimen.yd, Specimen.y1]
  linarith only [gm, e1.1, ed.2]

theorem contrast_high (s : Specimen) (hx0 : 25 ≤ s.x) (hx1 : s.x ≤ 100) :
    1/1000 ≤ s.contrast := by
  have u := native_high hx0 hx1 s.rho_lo s.rho_hi
  have margin := high_source_margin s.neat s.diluted s.c_box s.d_box s.k_box s.j_box
    u.1 u.2 s.dilution_lo s.dilution_hi s.drift_lo
  have pos : 0 ≤ s.r*signal (s.rho*s.x/s.d) s.pd s.qd - signal (s.rho*s.x) s.p s.q := by linarith
  have gm := mul_le_mul_of_nonneg_right s.gain_lo pos
  have e1 := abs_le.mp s.error_neat
  have ed := abs_le.mp s.error_diluted
  simp only [one_mul, mul_sub, ← mul_assoc] at gm
  dsimp [Specimen.contrast, Specimen.yd, Specimen.y1]
  linarith only [gm, margin, e1.2, ed.1]

def compatible (a b : ℝ) : Set ℝ :=
  {x | ∃ s : Specimen, s.x=x ∧ s.y1=a ∧ s.yd=b}

theorem truth_contained (s : Specimen) : s.x ∈ compatible s.y1 s.yd := by
  exact ⟨s,rfl,rfl,rfl⟩

theorem certificate_sound (s : Specimen) :
    ((∀ x ∈ compatible s.y1 s.yd, x ≤ 1/10) → s.x ≤ 1/10) ∧
    ((∀ x ∈ compatible s.y1 s.yd, 25 ≤ x) → 25 ≤ s.x) := by
  exact ⟨fun h => h _ (truth_contained s), fun h => h _ (truth_contained s)⟩

theorem promised_decision (s : Specimen) (h : Design s.x) :
    (s.contrast ≤ 1/5000 ↔ s.x ≤ 1/10) ∧
    (1/5000 < s.contrast ↔ 25 ≤ s.x) := by
  have lo := contrast_low s
  have hi := contrast_high s
  rcases h with h | ⟨h0,h1⟩
  · constructor <;> constructor <;> intro hh
    · exact h
    · exact lo hh
    · have := lo h; linarith
    · linarith
  · constructor <;> constructor <;> intro hh
    · have := hi h0 h1; linarith
    · linarith
    · exact h0
    · have := hi h0 h1; linarith

theorem endpoint_no_classifier (rule : ℝ → Bool) :
    ¬ (rule (signal (200/2499) (49/100) (49/100)) = false ∧
       rule (signal (2499/50) (1/51) (1/51)) = true) := by
  rw [source_endpoint_collision.2.2.1]
  intro h
  rw [h.1] at h
  simp at h

/-- Main contract: truth containment, correct promised decisions using two raw readings,
and impossibility of replacing that protocol by the same neat endpoint alone. -/
theorem main :
    (∀ s : Specimen, s.x ∈ compatible s.y1 s.yd) ∧
    (∀ s : Specimen, Design s.x →
      (s.contrast ≤ 1/5000 ↔ s.x ≤ 1/10) ∧
      (1/5000 < s.contrast ↔ 25 ≤ s.x)) ∧
    (∀ rule : ℝ → Bool, ¬ (rule (signal (200/2499) (49/100) (49/100)) = false ∧
       rule (signal (2499/50) (1/51) (1/51)) = true)) ∧
    (∀ x rho : ℝ, 0 ≤ x → 4/5 ≤ rho → rho ≤ 1 →
      ∃ s : Specimen, s.x=x ∧ s.rho=rho) ∧
    (∀ (response : ℝ → ℝ) (rule : (ℝ → ℝ → ℝ) → Bool),
      ¬ (rule (fun d s => response (accessibleAction (1/10) 1 d s)) = false ∧
         rule (fun d s => response (accessibleAction 100 (1/1000) d s)) = true)) := by
  exact ⟨truth_contained,promised_decision,endpoint_no_classifier,specimen_exists,no_masking_classifier⟩

end SandwichImmunoassay
