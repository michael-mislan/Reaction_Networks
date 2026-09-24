import proofs.CommonPhysicalRealization.ExporterSource

namespace FiniteReservoir
noncomputable section
open RandomViability.Binding

structure Bath where
  fuel : ℕ
  waste : ℕ
  deriving DecidableEq

def Bath.forward (b : Bath) : Bath := ⟨b.fuel-1,b.waste+1⟩
def Bath.reverse (b : Bath) : Bath := ⟨b.fuel+1,b.waste-1⟩
def Bath.total (b : Bath) : ℕ := b.fuel+b.waste

theorem forward_conserves (b : Bath) (h : 0 < b.fuel) :
    b.forward.total = b.total := by simp only [Bath.forward,Bath.total]; omega

theorem reverse_conserves (b : Bath) (h : 0 < b.waste) :
    b.reverse.total = b.total := by simp only [Bath.reverse,Bath.total]; omega

structure RateBox (alpha beta : ℝ) : Prop where
  alpha_nonneg : 0 ≤ alpha
  alpha_upper : alpha ≤ 1/25
  beta_nonneg : 0 ≤ beta
  beta_upper : beta ≤ 1/200000000000

def alpha (b : Bath) (d R : ℝ) : ℝ := d*((b.fuel:ℝ)/R)
def beta (b : Bath) (d R : ℝ) : ℝ := d*(1/8000000000)*((b.waste:ℝ)/R)

theorem rate_box (b : Bath) (d R : ℝ) (hR : 0 < R) (hd : 0 ≤ d)
    (hf : d*(b.fuel:ℝ) ≤ R/25) (hp : d*(b.waste:ℝ) ≤ R/25) :
    RateBox (alpha b d R) (beta b d R) := by
  constructor
  · unfold alpha; positivity
  · unfold alpha; rw [← mul_div_assoc, div_le_iff₀ hR]; linarith
  · unfold beta; positivity
  · unfold beta
    rw [← mul_div_assoc, div_le_iff₀ hR]
    nlinarith

theorem candidate_A (b : Bath) (R : ℕ) (hR : 0 < R) (ht : b.total=R)
    (d : ℝ) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    RateBox (alpha b d R) (beta b d R) := by
  have hf : (b.fuel:ℝ) ≤ R := by exact_mod_cast (show b.fuel ≤ R by unfold Bath.total at ht; omega)
  have hp : (b.waste:ℝ) ≤ R := by exact_mod_cast (show b.waste ≤ R by unfold Bath.total at ht; omega)
  apply rate_box b d R (by exact_mod_cast hR) hd
  · have := mul_le_mul hd' hf (Nat.cast_nonneg _) (by norm_num : (0:ℝ) ≤ 1/25)
    linarith
  · have := mul_le_mul hd' hp (Nat.cast_nonneg _) (by norm_num : (0:ℝ) ≤ 1/25)
    linarith

theorem candidate_B (b : Bath) (R : ℕ) (hR : 0 < R) (ht : b.total=2*R) :
    RateBox (alpha b (1/50) R) (beta b (1/50) R) := by
  have hf : (b.fuel:ℝ) ≤ 2*R := by exact_mod_cast (show b.fuel ≤ 2*R by unfold Bath.total at ht; omega)
  have hp : (b.waste:ℝ) ≤ 2*R := by exact_mod_cast (show b.waste ≤ 2*R by unfold Bath.total at ht; omega)
  apply rate_box b (1/50) R (by exact_mod_cast hR) (by norm_num) <;> linarith

abbrev State := Counts × Bath
def rate (s : State) (V r d R : ℝ) (j : CompetitionChannel) : ℝ :=
  CommonPhysicalRealization.physicalRate s.1 V r d (s.2.fuel/R) (s.2.waste/R) j

def next (s : State) (j : CompetitionChannel) : State :=
  (CommonPhysicalRealization.physicalNext s.1 j,
    match j with
    | .inl _ => s.2
    | .inr k => if k=0 then s.2.forward else s.2.reverse)

theorem forward_boundary (N : Counts) (p : ℕ) (V r d R : ℝ) :
    rate (N,⟨0,p⟩) V r d R (.inr 0)=0 := by
  simp [rate,CommonPhysicalRealization.physicalRate]

theorem reverse_boundary (N : Counts) (f : ℕ) (V r d R : ℝ) :
    rate (N,⟨f,0⟩) V r d R (.inr 1)=0 := by
  norm_num [rate,CommonPhysicalRealization.physicalRate]

theorem supported_conservation (s : State) (V r d R : ℝ) (j : CompetitionChannel)
    (h : rate s V r d R j ≠ 0) : (next s j).2.total=s.2.total := by
  cases j with
  | inl j => rfl
  | inr j =>
    fin_cases j
    · have hf : 0 < s.2.fuel := by
        by_contra hn
        have hz : s.2.fuel=0 := by omega
        apply h
        simp [rate,CommonPhysicalRealization.physicalRate,hz]
      exact forward_conserves s.2 hf
    · have hp : 0 < s.2.waste := by
        by_contra hn
        have hz : s.2.waste=0 := by omega
        apply h
        norm_num [rate,CommonPhysicalRealization.physicalRate,hz]
      exact reverse_conserves s.2 hp

end
end FiniteReservoir
