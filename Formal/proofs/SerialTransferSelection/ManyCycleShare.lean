import proofs.SerialTransferSelection.ShareCycleProbability
import proofs.SerialTransferSelection.ManyCycleMeasured

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

noncomputable def shareCycleError (N M JB JR : ℕ) (qb qr t q ε : ℝ) : ℝ :=
  (phaseChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+t*qb/JB)+
    (16/(ε^2*(M : ℝ)*q)+(M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*qr/JR))

def shareHistoryStep (N M : ℕ) (zL zH : ℝ) (q : ℕ → ℝ) (ε : ℝ) (j : ℕ)
    (x y : Option (ReadyPopulation N M zL zH)) : Prop :=
  match x, y with
  | some s, some t => shareCycleReadyRelation N M zL zH s.val (q j) ε t
  | _, _ => False

def shareHistoryEligible (N M : ℕ) (zL zH : ℝ) (q : ℕ → ℝ) (j : ℕ)
    (x : Option (ReadyPopulation N M zL zH)) : Prop :=
  match x with
  | some s => ∀ b, q j ≤ ancestralShare b s.val
  | none => False

variable (N M JB JR : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (zL zH : ℝ)
  (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
  (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
  (qr : NNReal) (hqr : 0 < (qr : ℝ))
  (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)
  (γ : ℝ) (hγ : 0 ≤ γ) (qb t : NNReal) (hqb : 0 < (qb : ℝ))
  (hclockb : ∀ (s : ReadyPopulation N M zL zH) x,
    (cycleBatchModel N M zL zH γ hγ s).total x ≤ qb)

theorem sourceManyCycleLaw_share_probability
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (h1000 : 1000 ≤ N)
    (hJB : 0 < JB) (hJR : 0 < JR) (hγpos : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (hkr : (N : ℝ)*localAlpha*innerEnergy/672 ≤ qr)
    (hkb : (9/40000)*(N : ℝ)*γ ≤ qb) (htime : (t : ℝ)=8/γ)
    (q : ℕ → ℝ) (ε : ℝ) (hq : ∀ j, 0 < q j) (hε : 0 < ε) (hε1 : ε < 1)
    (hnext : ∀ j, q (j+1) ≤ (1-ε)/(4*(1+ε))*q j)
    (K : ℕ) (s : ReadyPopulation N M zL zH)
    (hfloor : ∀ b, q 0 ≤ ancestralShare b s.val) :
    1-historyBudget (fun j => shareCycleError N M JB JR qb qr t (q j) ε) K 0 ≤
      (sourceManyCycleLaw N M JB JR hN hM zL zH hzL hzH qr hqr hclockr
        γ hγ qb t hqb hclockb K s).expect
        (FiniteKernel.eventIndicator {h | historyGood (shareHistoryStep N M zL zH q ε) K 0 (some s) h}) := by
  apply finiteHistoryLaw_probability _ _ (shareHistoryEligible N M zL zH q)
  · intro j
    have hqj := hq j
    unfold shareCycleError phaseChemicalRawError recoveryError partitionError localAlpha innerEnergy outerEnergy
    positivity
  · intro j x hx
    cases x with
    | none => exact False.elim hx
    | some y =>
      have he : {v | shareHistoryStep N M zL zH q ε j (some y) v} =
          successfulOutput (shareCycleReadyRelation N M zL zH y.val (q j) ε) := by
        ext v
        cases v <;> rfl
      rw [he]
      exact sourceCycleLaw_share_probability N M JB JR hN hM zL zH hzL hzH y qr hqr hclockr
        hsL hsH hlarge hJR hkr (q j) ε (hq j) hε hε1 hx h1000 hJB
        γ hγpos hγmax qb t hqb (hclockb y) hkb htime
  · intro j x y _ hxy
    cases x with
    | none => exact False.elim hxy
    | some x =>
      cases y with
      | none => exact False.elim hxy
      | some y => exact fun b => (hnext j).trans (hxy.1 b)
  · exact hfloor

theorem historyGood_mono {α : Type*} (R S : ℕ → α → α → Prop)
    (hRS : ∀ j x y, R j x y → S j x y) (k j : ℕ) (x : α) (h : Fin k → α)
    (hh : historyGood R k j x h) : historyGood S k j x h := by
  induction k generalizing j x with
  | zero => trivial
  | succ k ih => exact ⟨hRS j x (h 0) hh.1,ih (j+1) (h 0) (Fin.tail h) hh.2⟩

theorem shareHistory_measured (N M : ℕ) (hN : 0 < N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (q : ℕ → ℝ) (ε : ℝ) (K : ℕ) (s : ReadyPopulation N M zL zH)
    (hnew : ∀ c ∈ s.val.live, c.compartment.2=N)
    (hpos : ∀ b, 0 < ancestralCount b s.val.live)
    (h : Fin K → Option (ReadyPopulation N M zL zH))
    (hh : historyGood (shareHistoryStep N M zL zH q ε) K 0 (some s) h) :
    manyMeasuredEvent N M zL zH ε K s.val h := by
  apply manyCycle_good_measured N M hN zL zH hzL hzH (fun j => q j/2) ε K s hnew hpos h
  apply historyGood_mono _ _ _ K 0 (some s) h hh
  intro j x y hxy
  cases x with
  | none => exact False.elim hxy
  | some x =>
    cases y with
    | none => exact False.elim hxy
    | some y => exact hxy.2

noncomputable def shareFloor (j : ℕ) : ℝ := (1/2)*(49/204)^j

theorem shareFloor_pos (j : ℕ) : 0 < shareFloor j := by unfold shareFloor; positivity

theorem shareFloor_next (j : ℕ) : shareFloor (j+1) =
    (1-(1/50 : ℝ))/(4*(1+1/50))*shareFloor j := by
  unfold shareFloor
  rw [pow_succ]
  ring

end SerialTransferSelection
