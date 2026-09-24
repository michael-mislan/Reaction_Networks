import proofs.RAF1519.Refinement.MarkMeasurable
import proofs.RAF1519.Refinement.CountReadyReturn

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators

/-- One literal operating period, before adding the pulse's food dose. -/
def operatingSuccess {n : ℕ} (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) : Prop :=
  ∀ i, Ready (1/100) (fun s => countPath V z 4 (i,s)) ∧
    39/1000 ≤ markedWindow V i .inventory z 3 4 ∧
    6/1000 ≤ markedWindow V i .freeX z 3 4 ∧
    markedWindow V i .foodU z 0 4 ≤ 4001/1000 ∧
    markedWindow V i .foodW z 0 4 ≤ 4001/1000 ∧
    markedWindow V i .service z 0 4 ≤ 181/1000

theorem operatingSuccess_measurable {n : ℕ} (V : ℝ) :
    MeasurableSet {z : ℕ → JumpState (MolecularState n) (CountChannel n) | operatingSuccess V z} := by
  have hr : ∀ i : Fin n, MeasurableSet {z : ℕ → JumpState (MolecularState n) (CountChannel n) |
      Ready (1/100) (fun s => countPath V z 4 (i,s))} := by
    intro i
    exact (Set.to_countable {N : MolecularState n |
      Ready (1/100) (concentration V (fun s => N (i,s)))}).measurableSet.preimage
        (molecularStateAt_measurable 4)
  unfold operatingSuccess
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (hr i).inter ((measurableSet_le measurable_const (markedWindow_measurable V i .inventory 3 4)).inter
    ((measurableSet_le measurable_const (markedWindow_measurable V i .freeX 3 4)).inter
    ((measurableSet_le (markedWindow_measurable V i .foodU 0 4) measurable_const).inter
    ((measurableSet_le (markedWindow_measurable V i .foodW 0 4) measurable_const).inter
      (measurableSet_le (markedWindow_measurable V i .service 0 4) measurable_const)))))

theorem operatingSuccess_of_noise {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (hmarks : ∀ i m, z ∉ markIntervalFailure r d k V i m (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (hD : ∀ i, ((z 0).1 (i,6):ℝ)/V ≤ 1101/100000)
    (hY : ∀ i, 12/1000 ≤ stock (concentration V (fun s => (z 0).1 (i,s))))
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z)) : operatingSuccess V z := by
  have hsafe := material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0
  intro i
  have hcomp := count_operating_compensators r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc
    hnoise h0 hD hY K hK i
  exact ⟨count_ready_return r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc hnoise h0 hD hY K hK i,
    marked_operating_outputs r d k V hV.ne' i z hh (hmarks i) hsafe K hK hcomp.1 hcomp.2.1 hcomp.2.2⟩

end
end RAF1519.Refinement
