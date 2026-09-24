import proofs.PowerLawSmallRAF.FiniteLigationExposure

namespace PowerLawSmallRAF

set_option maxHeartbeats 100000

open scoped BigOperators

/-- Full finite outcome-history weight for the word-generation kernel. -/
noncomputable def ligationHistoryWeight (p : ℝ) :
    (words : List LigationWord) → (Fin words.length → Bool) → Finset LigationWord → ℝ
  | [], _, _ => 1
  | w :: rest, bits, known =>
      if bits 0 then
        (1 - ligationFailureChance p known w) *
          ligationHistoryWeight p rest (Fin.tail bits) (insert w known)
      else
        ligationFailureChance p known w *
          ligationHistoryWeight p rest (Fin.tail bits) known

def stoppedLigationHistory (selected : Finset LigationWord) :
    (words : List LigationWord) → (Fin words.length → Bool) → Finset LigationWord → Prop
  | [], _, _ => True
  | w :: rest, bits, known =>
      if w ∈ selected then
        LigationCutDensity known w ∧ bits 0 = false ∧
          stoppedLigationHistory selected rest (Fin.tail bits) known
      else
        stoppedLigationHistory selected rest (Fin.tail bits)
          (if bits 0 then insert w known else known)

noncomputable instance (selected : Finset LigationWord) (words : List LigationWord)
    (bits : Fin words.length → Bool) (known : Finset LigationWord) :
    Decidable (stoppedLigationHistory selected words bits known) := Classical.propDecidable _

noncomputable def stoppedLigationHistoryWeight (p : ℝ) (selected : Finset LigationWord)
    (words : List LigationWord) (bits : Fin words.length → Bool)
    (known : Finset LigationWord) : ℝ :=
  if stoppedLigationHistory selected words bits known then
    ligationHistoryWeight p words bits known else 0

theorem sum_bool_history_cons (n : Nat) (f : (Fin (n+1) → Bool) → ℝ) :
    (∑ bits, f bits) = ∑ b : Bool, ∑ tail : Fin n → Bool, f (Fin.cons b tail) := by
  calc
    (∑ bits, f bits) = ∑ z : Bool × (Fin n → Bool), f (Fin.cons z.1 z.2) := by
      exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool))
        (fun z => f (Fin.cons z.1 z.2)) f (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

theorem ligationHistoryWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (bits : Fin words.length → Bool)
    (known : Finset LigationWord) : 0 ≤ ligationHistoryWeight p words bits known := by
  induction words generalizing known with
  | nil => simp [ligationHistoryWeight]
  | cons w rest ih =>
      have hm := ligationFailureChance_nonneg_le_one hp hp1 known w
      simp only [ligationHistoryWeight]
      split
      · exact mul_nonneg (sub_nonneg.mpr hm.2) (ih _ _)
      · exact mul_nonneg hm.1 (ih _ _)

/-- Normalization is proved for the history law, not assumed as a kernel
interface. No probabilistic independence of generated words is asserted. -/
theorem sum_ligationHistoryWeight (p : ℝ) (words : List LigationWord)
    (known : Finset LigationWord) :
    (∑ bits : Fin words.length → Bool, ligationHistoryWeight p words bits known) = 1 := by
  induction words generalizing known with
  | nil => simp [ligationHistoryWeight]
  | cons w rest ih =>
      trans ∑ b : Bool, ∑ tail : Fin rest.length → Bool,
        ligationHistoryWeight p (w :: rest) (Fin.cons b tail) known
      · exact sum_bool_history_cons rest.length _
      rw [Fintype.sum_bool]
      change (∑ tail : Fin rest.length → Bool,
          (1 - ligationFailureChance p known w) *
            ligationHistoryWeight p rest tail (insert w known)) +
        (∑ tail : Fin rest.length → Bool,
          ligationFailureChance p known w * ligationHistoryWeight p rest tail known) = 1
      rw [← Finset.mul_sum, ← Finset.mul_sum, ih, ih]
      ring

theorem sum_ite_const_mul {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P]
    (a : ℝ) (f : I → ℝ) :
    (∑ i, if P i then a * f i else 0) = a * ∑ i, if P i then f i else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Exact path-event interpretation of the recursively integrated stopped
mass. The selected failures are events on the whole history. -/
theorem stoppedLigationMass_eq_history_event (p : ℝ) (selected : Finset LigationWord)
    (words : List LigationWord) (known : Finset LigationWord) :
    stoppedLigationMass p selected words known =
      ∑ bits : Fin words.length → Bool,
        stoppedLigationHistoryWeight p selected words bits known := by
  induction words generalizing known with
  | nil => simp [stoppedLigationMass, stoppedLigationHistoryWeight,
      stoppedLigationHistory, ligationHistoryWeight]
  | cons w rest ih =>
      suffices h : stoppedLigationMass p selected (w :: rest) known =
          ∑ b : Bool, ∑ tail : Fin rest.length → Bool,
            stoppedLigationHistoryWeight p selected (w :: rest) (Fin.cons b tail) known by
        exact h.trans (sum_bool_history_cons rest.length (fun bits =>
          stoppedLigationHistoryWeight p selected (w :: rest) bits known)).symm
      rw [Fintype.sum_bool]
      by_cases hs : w ∈ selected
      · by_cases hd : LigationCutDensity known w
        · simp only [stoppedLigationMass, stoppedLigationHistoryWeight,
            stoppedLigationHistory, ligationHistoryWeight,
            hs, hd, Fin.cons_zero, Fin.tail_cons, ↓reduceIte, Bool.true_eq_false,
            Bool.false_eq_true, and_false, false_and, true_and, Finset.sum_const_zero, zero_add]
          rw [sum_ite_const_mul]
          change _ = _ * ∑ tail, stoppedLigationHistoryWeight p selected rest tail known
          rw [← ih]
        · simp [stoppedLigationMass, stoppedLigationHistoryWeight,
            stoppedLigationHistory, hs, hd]
      · simp only [stoppedLigationMass, stoppedLigationHistoryWeight,
          stoppedLigationHistory, ligationHistoryWeight,
          hs, Fin.cons_zero, Fin.tail_cons, Bool.false_eq_true, ↓reduceIte]
        rw [sum_ite_const_mul, sum_ite_const_mul]
        change _ = (1 - ligationFailureChance p known w) *
          (∑ tail, stoppedLigationHistoryWeight p selected rest tail (insert w known)) +
          ligationFailureChance p known w *
          (∑ tail, stoppedLigationHistoryWeight p selected rest tail known)
        rw [← ih, ← ih]
        ring

/-- The stopped-chain estimate as an inequality for an explicit normalized
finite probability law, with all selected lengths retained. -/
theorem stoppedLigationHistory_mass_le_exp {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (selected : Finset LigationWord) (words : List LigationWord)
    (hlen : ∀ w ∈ words, w ∈ selected → 4 ≤ w.length)
    (known : Finset LigationWord) :
    (∑ bits : Fin words.length → Bool,
      stoppedLigationHistoryWeight p selected words bits known) ≤
      Real.exp (-p * (selectedWordLengthSum selected words : ℝ) / 2) := by
  rw [← stoppedLigationMass_eq_history_event]
  exact stoppedLigationMass_le_exp hp hp1 selected words hlen known

end PowerLawSmallRAF
