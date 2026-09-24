import proofs.TypeIIStability.Source
import proofs.TypeIIStability.PhysicalJacobian

namespace TypeIIStability.Witness
noncomputable section
open TypeIIL TypeII3
open TypeIIStability.Source
open MixedDegradation.TypeII
open scoped Matrix BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 1600000

@[simp] theorem fin_two {n : ℕ} (h : 2 < n+3) : (⟨2,h⟩ : Fin (n+3)) = 2 := rfl
@[simp] theorem fin_three {n : ℕ} (h : 3 < n+4) : (⟨3,h⟩ : Fin (n+4)) = 3 := rfl
@[simp] theorem fin_four {n : ℕ} (h : 4 < n+5) : (⟨4,h⟩ : Fin (n+5)) = 4 := rfl
@[simp] theorem fin_five {n : ℕ} (h : 5 < n+6) : (⟨5,h⟩ : Fin (n+6)) = 5 := rfl
@[simp] theorem fin_six {n : ℕ} (h : 6 < n+7) : (⟨6,h⟩ : Fin (n+7)) = 6 := rfl

@[simp] theorem vec_two {α : Type*} {n : ℕ} (a : α) (b : Fin (n+2) → α) :
    Matrix.vecCons a b (2 : Fin (n+3)) = b 1 := rfl
@[simp] theorem vec_three {α : Type*} {n : ℕ} (a : α) (b : Fin (n+3) → α) :
    Matrix.vecCons a b (3 : Fin (n+4)) = b 2 := rfl
@[simp] theorem vec_four {α : Type*} {n : ℕ} (a : α) (b : Fin (n+4) → α) :
    Matrix.vecCons a b (4 : Fin (n+5)) = b 3 := rfl
@[simp] theorem vec_five {α : Type*} {n : ℕ} (a : α) (b : Fin (n+5) → α) :
    Matrix.vecCons a b (5 : Fin (n+6)) = b 4 := rfl
@[simp] theorem vec_six {α : Type*} {n : ℕ} (a : α) (b : Fin (n+6) → α) :
    Matrix.vecCons a b (6 : Fin (n+7)) = b 5 := rfl

def returnChain : Fin 3 → MixedDegradation.UnitChain :=
  ![.direct (forwardRate 5) (reverseRate 5) (rates_positive.1 5) (rates_positive.2.1 5),
    .extend (.direct (forwardRate 1) (reverseRate 1) (rates_positive.1 1) (rates_positive.2.1 1))
      (forwardRate 6) (reverseRate 6) (degradation 6)
      (rates_positive.1 6) (rates_positive.2.1 6) (rates_positive.2.2 6).le,
    .direct (forwardRate 3) (reverseRate 3) (rates_positive.1 3) (rates_positive.2.1 3)]

def sourceRates : Rates skeleton (fun _ => 1) where
  tailDepth := ![1, 2, 1]
  tailDepth_pos := by intro j; fin_cases j <;> norm_num
  tailCycleWeight := fun _ _ => 1
  tailCycleWeight_pos := by intro j k; omega
  terminal_cycle_weight := by intro j; rfl
  chain := returnChain
  plus := ![forwardRate 0, (returnChain 1).summary.c, forwardRate 2,
    (returnChain 2).summary.c, forwardRate 4, (returnChain 0).summary.c]
  minus := ![reverseRate 0, (returnChain 1).summary.beta, reverseRate 2,
    (returnChain 2).summary.beta, reverseRate 4, (returnChain 0).summary.beta]
  degrade := fun i => degradation i.castSucc
  plus_pos := by
    intro i; fin_cases i
    · exact rates_positive.1 0
    · exact (returnChain 1).summary.c_pos
    · exact rates_positive.1 2
    · exact (returnChain 2).summary.c_pos
    · exact rates_positive.1 4
    · exact (returnChain 0).summary.c_pos
  minus_pos := by
    intro i; fin_cases i
    · exact rates_positive.2.1 0
    · exact (returnChain 1).summary.beta_pos
    · exact rates_positive.2.1 2
    · exact (returnChain 2).summary.beta_pos
    · exact rates_positive.2.1 4
    · exact (returnChain 0).summary.beta_pos
  degrade_nonneg := fun i => (rates_positive.2.2 i.castSucc).le
  terminal_plus := by intro j; fin_cases j <;> rfl
  terminal_minus := by intro j; fin_cases j <;> rfl

def unusedCoincident : MixedDegradation.Coincident.AllZeroParams where
  plus0 := 1
  plus1 := 1
  plus2 := 1
  minus0 := 1
  minus1 := 1
  minus2 := 1
  d0 := 1
  d1 := 1
  d2 := 1
  m0 := 1
  m1 := 1
  m2 := 1
  plus0_pos := by norm_num
  plus1_pos := by norm_num
  plus2_pos := by norm_num
  minus0_pos := by norm_num
  minus1_pos := by norm_num
  minus2_pos := by norm_num
  d0_nonneg := by norm_num
  d1_nonneg := by norm_num
  d2_nonneg := by norm_num
  m0_pos := by norm_num
  m1_pos := by norm_num
  m2_pos := by norm_num

def paperNetwork : PaperRaw.OpenNetwork 3 where
  weakGap := weakGap
  separated :=
    { n := 6
      next := next6
      back := back6
      source := skeleton
      weight := fun _ => 1
      weight_pos := by intro i; omega
      rates := sourceRates }
  coincident := unusedCoincident

theorem unit_tail_minimal {n : ℕ} [NeZero n] (start : Fin n) :
    PaperTailPassesMinimality (paperTailRotatedWeight (fun _ : Fin n => 1) start) := by
  rintro ⟨w, _, hw⟩
  have hs : 0 < ∑ i, ∑ j, paperTailCycleRestriction
      (paperTailRotatedWeight (fun _ : Fin n => 1) start) i j*w j :=
    Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  simp_rw [paperTailCycleRestriction_mulVec] at hs
  have hp : (∑ i, w ((finRotate n).symm i)) = ∑ i, w i := Equiv.sum_comp _ _
  simp only [paperTailRotatedWeight, Nat.cast_one, one_mul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, hp] at hs
  linarith

theorem paper_core : PaperRaw.IsPaperTypeIILCore paperNetwork := by
  refine ⟨weak_top, ?_⟩
  rintro ⟨h⟩
  cases h with
  | stem R => exact weak_minimal ⟨R⟩
  | tail hsep j start hauto =>
    fin_cases j <;> exact unit_tail_minimal start hauto

def sourceState : State skeleton (fun _ => 1) sourceRates where
  core := fun i => x i.castSucc
  tail := Fin.cases PUnit.unit
    (Fin.cases (PUnit.unit, x 6) (Fin.cases PUnit.unit (fun i => Fin.elim0 i)))

theorem source_positive : Positive sourceState := by
  constructor
  · intro i; exact parameters_positive.2.2.2 i.castSucc
  · intro j; fin_cases j
    · trivial
    · exact ⟨trivial, parameters_positive.2.2.2 6⟩
    · trivial

theorem planted_current (i : Fin 7) :
    forwardRate i*x i - reverseRate i*products x i = p i-q i := by
  have hx := ne_of_gt (parameters_positive.2.2.2 i)
  have hm := ne_of_gt (products_pos x parameters_positive.2.2.2 i)
  simp [forwardRate, reverseRate, hx, hm]

theorem planted_loss (i : Fin 7) : degradation i*x i = e i := by
  exact div_mul_cancel₀ _ (ne_of_gt (parameters_positive.2.2.2 i))

def leftCurrent : Fin 3 → ℝ := ![p 5-q 5, p 1-q 1, p 3-q 3]
def rightCurrent : Fin 3 → ℝ := ![p 5-q 5, p 6-q 6, p 3-q 3]

theorem literal_chain_balances (j : Fin 3) :
    MixedDegradation.ChainFlux (sourceRates.chain j) (sourceState.tail j)
      (sourceState.core (skeleton.paperTailTerminal j))
      (sourceState.core (skeleton.fork j)) (leftCurrent j) (rightCurrent j) := by
  fin_cases j
  · change (p 5-q 5 = forwardRate 5*x 5-reverseRate 5*x 0) ∧
      (p 5-q 5 = forwardRate 5*x 5-reverseRate 5*x 0)
    exact ⟨(planted_current 5).symm, (planted_current 5).symm⟩
  · change ∃ jMid,
      ((p 1-q 1 = forwardRate 1*x 1-reverseRate 1*x 6) ∧
      jMid = forwardRate 1*x 1-reverseRate 1*x 6) ∧
      jMid-forwardRate 6*x 6+reverseRate 6*x 2-degradation 6*x 6 = 0 ∧
      p 6-q 6 = forwardRate 6*x 6-reverseRate 6*x 2
    refine ⟨p 1-q 1, ⟨(planted_current 1).symm, (planted_current 1).symm⟩, ?_, (planted_current 6).symm⟩
    have hb := congrFun stationary_balance 6
    have hc := planted_current 6
    have hd := planted_loss 6
    norm_num [N, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ] at hb
    change forwardRate 6*x 6-reverseRate 6*x 2 = p 6-q 6 at hc
    linarith
  · change (p 3-q 3 = forwardRate 3*x 3-reverseRate 3*x 4) ∧
      (p 3-q 3 = forwardRate 3*x 3-reverseRate 3*x 4)
    exact ⟨(planted_current 3).symm, (planted_current 3).symm⟩

def sourceP : Matrix (Fin 6) (Fin 6) ℕ :=
  ![![0,0,0,0,0,1], ![1,0,1,0,0,0], ![0,1,0,0,0,0],
    ![0,0,1,0,1,0], ![0,0,0,1,0,0], ![1,0,0,0,1,0]]

theorem source_product_matrix : sourceProductExponent next6 (fun _ => 1) back6 = sourceP := by
  funext i r
  exact (show ∀ i r, sourceProductExponent next6 (fun _ => 1) back6 i r = sourceP i r from by decide) i r

def sourceN : Matrix (Fin 6) (Fin 6) ℝ :=
  ![![-1,0,0,0,0,1], ![1,-1,1,0,0,0], ![0,1,-1,0,0,0],
    ![0,0,1,-1,1,0], ![0,0,0,1,-1,0], ![1,0,0,0,1,-1]]

theorem source_stoich_matrix : sourceStoich next6 (fun _ => 1) back6 = sourceN := by
  funext i r
  unfold sourceStoich
  rw [source_product_matrix]
  fin_cases i <;> fin_cases r <;> norm_num [sourceP, sourceN, Fin.ext_iff]

theorem active_product (z : Fin 7 → ℝ) (j : Fin 3) :
    paperSourceProductMonomial (sourceProductExponent next6 (fun _ => 1) back6)
      (fork6 j) (fun i => z i.castSucc) = products z (fork6 j).castSucc := by
  have hc : (fun i : Fin 6 => z i.castSucc) = ![z 0,z 1,z 2,z 3,z 4,z 5] := by
    ext i; fin_cases i <;> rfl
  rw [source_product_matrix, hc]
  fin_cases j
  · change paperSourceProductMonomial sourceP 0 _ = z 1*z 5
    simp [paperSourceProductMonomial, sourceP, Fin.prod_univ_succ]
  · change paperSourceProductMonomial sourceP 2 _ = z 3*z 1
    simp [paperSourceProductMonomial, sourceP, Fin.prod_univ_succ, mul_comm]
  · change paperSourceProductMonomial sourceP 4 _ = z 5*z 3
    simp [paperSourceProductMonomial, sourceP, Fin.prod_univ_succ, mul_comm]

theorem active_current (j : Fin 3) :
    current sourceRates sourceState.core (fork6 j) = p (fork6 j).castSucc-q (fork6 j).castSucc := by
  have hplus : sourceRates.plus (fork6 j) = forwardRate (fork6 j).castSucc := by fin_cases j <;> rfl
  have hminus : sourceRates.minus (fork6 j) = reverseRate (fork6 j).castSucc := by fin_cases j <;> rfl
  change sourceRates.plus (fork6 j)*x (fork6 j).castSucc - sourceRates.minus (fork6 j)*
    paperSourceProductMonomial (sourceProductExponent next6 (fun _ => 1) back6)
      (fork6 j) (fun i => x i.castSucc) = _
  rw [hplus, hminus, active_product]
  exact planted_current _

theorem source_tail_terminal (j : Fin 3) : skeleton.paperTailTerminal j = backStem6 j := by
  fin_cases j <;> rfl

theorem retained_balance_formula (c : Fin 6 → ℝ) (jl jr : Fin 3 → ℝ) (i : Fin 6) :
    (∑ r, sourceStoich next6 (fun _ => 1) back6 i r*c r) -
      (∑ j, sourceStoich next6 (fun _ => 1) back6 i (skeleton.paperTailTerminal j)*c (skeleton.paperTailTerminal j)) +
      (∑ j, skeleton.paperTailBoundaryContribution i j (jl j) (jr j)) =
      ![-c 0+jr 0, c 0+c 2-jl 1, -c 2+jr 1,
        c 2+c 4-jl 2, -c 4+jr 2, c 0+c 4-jl 0] i := by
  simp only [source_stoich_matrix]
  have hf : skeleton.fork = fork6 := rfl
  fin_cases i <;>
    norm_num [sourceN, fork6, backStem6, source_tail_terminal, hf,
      SourceCyclicNonemptyGapSystem.paperTailBoundaryContribution,
      Fin.sum_univ_succ] <;>
    norm_num [Fin.ext_iff, Fin.succ] <;> ring

theorem source_stationary : Stationary sourceRates sourceState := by
  refine ⟨leftCurrent, rightCurrent, literal_chain_balances, ?_⟩
  intro i
  rw [retained_balance_formula]
  have h0 := active_current 0
  have h1 := active_current 1
  have h2 := active_current 2
  change current sourceRates sourceState.core 0 = p 0-q 0 at h0
  change current sourceRates sourceState.core 2 = p 2-q 2 at h1
  change current sourceRates sourceState.core 4 = p 4-q 4 at h2
  have hb := congrFun stationary_balance i.castSucc
  change _ = degradation i.castSucc*x i.castSucc
  rw [planted_loss]
  simp only [h0, h1, h2]
  have hcast : ∀ k : Fin 6, k.castSucc = (![0,1,2,3,4,5] : Fin 6 → Fin 7) k := by
    intro k; fin_cases k <;> rfl
  rw [hcast] at hb ⊢
  fin_cases i
  all_goals
    norm_num [leftCurrent, rightCurrent]
    norm_num [N, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ] at hb
    convert hb using 1 <;> ring

theorem paper_separated : PaperWeakStemSpecies.AllSeparated paperNetwork.weakGap := by
  intro j; rfl

def paperState : paperNetwork.State :=
  (paperNetwork.separatedStateEquiv paper_separated).symm sourceState

theorem paper_positive : paperNetwork.PositiveState paperState := by
  simpa [PaperRaw.OpenNetwork.PositiveState, paper_separated, paperState] using source_positive

theorem paper_stationary : paperNetwork.Stationary paperState := by
  simpa [PaperRaw.OpenNetwork.Stationary, paper_separated, paperState] using source_stationary

end
end TypeIIStability.Witness
