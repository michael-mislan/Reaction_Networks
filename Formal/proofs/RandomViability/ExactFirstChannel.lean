import proofs.RandomViability.JumpFirstRace

namespace RandomViability
open Classical FiniteCopy
noncomputable section
set_option maxHeartbeats 30000
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Every genuine channel is marked, including genuine population self-loops. -/
theorem first_channel_mass (M : FiniteJumpModel α β) (q : ℝ) (hq : 0 < q)
    (hb : ∀ x, M.total x ≤ q) (x : α) (hx : 0 < M.total x) (b : β) (k : ℕ) :
    (labeledUniformize M q hq hb).pathEventMass k x
      (FiniteLabeledKernel.firstRace (markedLabel (fun _ => True))
        (markedLabel (fun c => c = b)) k) =
      M.rate x b / M.total x * (1 - (1 - M.total x / q)^k) := by
  induction k with
  | zero => simp [FiniteLabeledKernel.pathEventMass, FiniteLabeledKernel.firstRace]
  | succ k ih =>
    rw [FiniteLabeledKernel.firstRace_mass_succ, Fintype.sum_option]
    simp only [markedLabel, if_false, labeledUniformize, if_true, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [labeledUniformize] at ih
    rw [ih, pow_succ]
    field_simp [ne_of_gt hx, ne_of_gt hq]
    ring

/-- The Poissonized finite-path first-channel event has the physical holding-time CDF. -/
theorem first_channel_poisson (M : FiniteJumpModel α β) (q t : NNReal)
    (hq : 0 < (q : ℝ)) (hb : ∀ x, M.total x ≤ q)
    (x : α) (hx : 0 < M.total x) (b : β) :
    (labeledUniformize M q hq hb).poissonEventMass (q*t) x
      (FiniteLabeledKernel.firstRace (markedLabel (fun _ => True))
        (markedLabel (fun c => c = b))) =
      M.rate x b / M.total x * (1 - Real.exp (-M.total x * t)) := by
  have hs := ((poissonWeight_sum (q*t)).sub
    (poissonWeight_geometric (q*t) (1-M.total x/(q : ℝ)))).mul_left
      (M.rate x b / M.total x)
  have he : ((q*t : NNReal) : ℝ) * ((1-M.total x/(q : ℝ))-1) =
      -M.total x*t := by
    rw [NNReal.coe_mul]
    field_simp
    ring
  rw [he] at hs
  unfold FiniteLabeledKernel.poissonEventMass
  simp_rw [first_channel_mass M q hq hb x hx b]
  convert hs.tsum_eq using 1
  congr 1
  funext k
  ring

end
end RandomViability
