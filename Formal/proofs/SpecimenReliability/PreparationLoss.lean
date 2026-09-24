import proofs.SpecimenReliability.TwoPreparations

namespace SpecimenReliability
noncomputable section

def oneBound (p s : ℝ) (n : ℕ) : ℝ := 1-p+p*(1-s)^n
def contrastA (s a : ℝ) (n : ℕ) : ℝ := 1+(1-s)^n-2*(1-a)^n
def contrastC (a : ℝ) (n : ℕ) : ℝ := 1-2*(1-a)^n+(1-2*a)^n

theorem switching_identity (p q s a : ℝ) (n : ℕ) :
    oneBound p s n - envelope p p q a a n =
      p*contrastA s a n-q*contrastC a n := by
  unfold oneBound envelope contrastA contrastC
  have he : 1-a-a = 1-2*a := by ring
  rw [he]; ring

theorem splitting_iff (p q s a : ℝ) (n : ℕ) :
    envelope p p q a a n < oneBound p s n ↔
      q*contrastC a n < p*contrastA s a n := by
  have h := switching_identity p q s a n
  constructor <;> intro hh <;> linarith

theorem one_target_no_diversification (p q a b : ℝ) :
    envelope p p q a b 1 = 1-p*(a+b) := by
  simp only [envelope, pow_one]; ring

theorem finite_switch_example :
    oneBound (4/5) (19/20) 2 = 101/500 ∧
    envelope (4/5) (4/5) (16/25) (9/20) (9/20) 2 = 179/1250 ∧
    envelope (4/5) (4/5) (79/100) (9/20) (9/20) 2 = 4079/20000 := by
  norm_num [oneBound, envelope]

theorem finite_switch_threshold (q : ℝ) :
    envelope (4/5) (4/5) q (9/20) (9/20) 2 < oneBound (4/5) (19/20) 2 ↔
      q < 106/135 := by
  unfold envelope oneBound
  norm_num
  constructor <;> intro h <;> linarith

end
end SpecimenReliability
