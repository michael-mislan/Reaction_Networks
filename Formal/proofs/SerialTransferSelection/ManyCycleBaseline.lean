import proofs.SerialTransferSelection.ManyCycleLaw

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

def manyCycleStep (N M : ℕ) (zL zH : ℝ) (p : ℕ → ℝ) (ε : ℝ) (j : ℕ)
    (x y : Option (ReadyPopulation N M zL zH)) : Prop :=
  match x, y with
  | some s, some t => cycleReadyRelation N M zL zH s.val (p j) ε t
  | _, _ => False

def manyCycleEligible (N M : ℕ) (zL zH : ℝ) (p : ℕ → ℝ) (j : ℕ)
    (x : Option (ReadyPopulation N M zL zH)) : Prop :=
  match x with
  | some s => ∀ b, p j*(M : ℝ) ≤ ancestralCount b s.val.live
  | none => False

variable (N M JB JR : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (zL zH : ℝ)
  (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
  (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
  (qr : NNReal) (hqr : 0 < (qr : ℝ))
  (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)
  (γ : ℝ) (hγ : 0 ≤ γ) (qb t : NNReal) (hqb : 0 < (qb : ℝ))
  (hclockb : ∀ (s : ReadyPopulation N M zL zH) x,
    (cycleBatchModel N M zL zH γ hγ s).total x ≤ qb)

/-- Every original failed branch remains in this history distribution. -/
noncomputable def sourceManyCycleLaw (K : ℕ) (s : ReadyPopulation N M zL zH) :=
  finiteHistoryLaw (fun _ => sourceCycleOptionKernel N M JB JR hN hM zL zH hzL hzH
    qr hqr hclockr γ hγ qb t hqb hclockb) K 0 (some s)

theorem sourceManyCycleLaw_probability
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (h1000 : 1000 ≤ N)
    (hJB : 0 < JB) (hJR : 0 < JR) (hγpos : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (hkr : (N : ℝ)*localAlpha*innerEnergy/672 ≤ qr)
    (hkb : (9/40000)*(N : ℝ)*γ ≤ qb) (htime : (t : ℝ)=8/γ)
    (p : ℕ → ℝ) (ε : ℝ) (hp : ∀ j, 0 < p j) (hε : 0 < ε) (hε1 : ε < 1)
    (hnext : ∀ j, p (j+1) ≤ (1-ε)*p j/16)
    (K : ℕ) (s : ReadyPopulation N M zL zH)
    (hfloor : ∀ b, p 0*(M : ℝ) ≤ ancestralCount b s.val.live) :
    1-historyBudget (fun j => sourceCycleError N M JB JR qb qr t (p j) ε) K 0 ≤
      (sourceManyCycleLaw N M JB JR hN hM zL zH hzL hzH qr hqr hclockr
        γ hγ qb t hqb hclockb K s).expect
        (FiniteKernel.eventIndicator {h | historyGood (manyCycleStep N M zL zH p ε) K 0 (some s) h}) := by
  apply finiteHistoryLaw_probability _ _ (manyCycleEligible N M zL zH p)
  · intro j
    have hpj := hp j
    unfold sourceCycleError phaseChemicalRawError recoveryError partitionError localAlpha innerEnergy outerEnergy
    positivity
  · intro j x hx
    cases x with
    | none => exact False.elim hx
    | some y =>
      have he : {v | manyCycleStep N M zL zH p ε j (some y) v} =
          successfulOutput (cycleReadyRelation N M zL zH y.val (p j) ε) := by
        ext v
        cases v <;> rfl
      rw [he]
      exact sourceCycleLaw_probability N M JB JR hN hM zL zH hzL hzH y qr hqr hclockr
        hsL hsH hlarge hJR hkr (p j) ε (hp j) hε hε1 hx h1000 hJB
        γ hγpos hγmax qb t hqb (hclockb y) hkb htime
  · intro j x y _ hxy
    cases x with
    | none => exact False.elim hxy
    | some x =>
      cases y with
      | none => exact False.elim hxy
      | some y =>
        intro b
        exact (le_div_iff₀ (by positivity : (0 : ℝ) < M)).mp
          ((hnext j).trans (hxy.1 b).2)
  · exact hfloor

noncomputable def baselineFloor (j : ℕ) : ℝ := (1/2)*(49/800)^j

theorem baselineFloor_pos (j : ℕ) : 0 < baselineFloor j := by
  unfold baselineFloor
  positivity

theorem baselineFloor_next (j : ℕ) : baselineFloor (j+1) =
    (1-(1/50 : ℝ))*baselineFloor j/16 := by
  unfold baselineFloor
  rw [pow_succ]
  ring

/-- Every positive prefix has a real returned population and telescoping size gain. -/
theorem manyCycle_good_prefix (p : ℕ → ℝ) (ε : ℝ) (k j : ℕ)
    (s : ReadyPopulation N M zL zH)
    (h : Fin k → Option (ReadyPopulation N M zL zH))
    (hh : historyGood (manyCycleStep N M zL zH p ε) k j (some s) h)
    (i : Fin k) :
    ∃ y : ReadyPopulation N M zL zH, h i = some y ∧
      (∀ b, 0 < ancestralCount b y.val.live) ∧
      ((i.val+1 : ℕ) : ℝ)*cycleSizeGain ε < sizeLogOdds y.val-sizeLogOdds s.val := by
  induction k generalizing j s with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    obtain ⟨hfirst,htail⟩ := hh
    cases he : h 0 with
    | none => simp [he, manyCycleStep] at hfirst
    | some y =>
      have hy : cycleReadyRelation N M zL zH s.val (p j) ε y := by
        simpa [he, manyCycleStep] using hfirst
      have htail' : historyGood (manyCycleStep N M zL zH p ε) k (j+1)
          (some y) (Fin.tail h) := by simpa [he] using htail
      refine Fin.cases ?_ (fun r => ?_) i
      · refine ⟨y,he,fun b => (hy.1 b).1,?_⟩
        simpa using hy.2
      · obtain ⟨z,hz,hpos,hgain⟩ := ih (j+1) y (Fin.tail h) htail' r
        refine ⟨z,hz,hpos,?_⟩
        have hcast : (((r.succ.val+1 : ℕ) : ℝ)) = ((r.val+1 : ℕ) : ℝ)+1 := by
          simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        rw [hcast]
        nlinarith only [hgain,hy.2]

end SerialTransferSelection
