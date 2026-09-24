import proofs.PowerLawSmallRAF.LigationRawRowLaw
import proofs.PowerLawSmallRAF.OrderedLigationHistory

namespace PowerLawSmallRAF

open scoped BigOperators

set_option maxHeartbeats 100000

/-- A full split-position row for each scheduled word, sampled statically.
On a duplicate-free schedule each physical word has exactly one row. -/
def LigationRawConfiguration : List LigationWord → Type
  | [] => Unit
  | w :: rest => ((ligationCuts w) → Bool) × LigationRawConfiguration rest

noncomputable instance ligationRawConfigurationFintype :
    (words : List LigationWord) → Fintype (LigationRawConfiguration words)
  | [] => inferInstanceAs (Fintype Unit)
  | w :: rest =>
      letI := ligationRawConfigurationFintype rest
      inferInstanceAs (Fintype (((ligationCuts w) → Bool) × LigationRawConfiguration rest))

noncomputable def ligationRawWeight (p : ℝ) :
    (words : List LigationWord) → LigationRawConfiguration words → ℝ
  | [], _ => 1
  | _w :: rest, cfg => bernoulliFullRowWeight p cfg.1 * ligationRawWeight p rest cfg.2

noncomputable def ligationRawKnown : (words : List LigationWord) →
    LigationRawConfiguration words → Finset LigationWord → Finset LigationWord
  | [], _, known => known
  | w :: rest, cfg, known => ligationRawKnown rest cfg.2
      (if fullLigationRowFails known w cfg.1 then known else insert w known)

/-- Exact equality of expectations under the static product of full rows and
the normalized outcome-history law. No generated-word independence is assumed. -/
theorem ligationRaw_history_expectation (p : ℝ) (words : List LigationWord)
    (known : Finset LigationWord) (payoff : Finset LigationWord → ℝ) :
    (∑ cfg : LigationRawConfiguration words,
      ligationRawWeight p words cfg * payoff (ligationRawKnown words cfg known)) =
      ∑ bits : Fin words.length → Bool,
        ligationHistoryWeight p words bits known *
          payoff (ligationHistoryKnown words bits known) := by
  induction words generalizing known with
  | nil => simp [LigationRawConfiguration, ligationRawWeight, ligationRawKnown,
      ligationHistoryWeight, ligationHistoryKnown]
  | cons w rest ih =>
      let continuation := fun state : Finset LigationWord =>
        ∑ bits : Fin rest.length → Bool, ligationHistoryWeight p rest bits state *
          payoff (ligationHistoryKnown rest bits state)
      have hraw : (∑ cfg : LigationRawConfiguration (w :: rest),
          ligationRawWeight p (w :: rest) cfg * payoff (ligationRawKnown (w :: rest) cfg known)) =
          ligationFailureChance p known w * continuation known +
            (1-ligationFailureChance p known w) * continuation (insert w known) := by
        change (∑ cfg : ((ligationCuts w) → Bool) × LigationRawConfiguration rest,
          (bernoulliFullRowWeight p cfg.1 * ligationRawWeight p rest cfg.2) *
            payoff (ligationRawKnown rest cfg.2
              (if fullLigationRowFails known w cfg.1 then known else insert w known))) = _
        rw [Fintype.sum_prod_type]
        trans ∑ cfg : (ligationCuts w) → Bool, bernoulliFullRowWeight p cfg *
          (if fullLigationRowFails known w cfg then continuation known else continuation (insert w known))
        · apply Finset.sum_congr rfl
          intro cfg _
          simp only [mul_assoc, ← Finset.mul_sum]
          by_cases hf : fullLigationRowFails known w cfg
          · simp only [hf, ↓reduceIte]
            exact congrArg (fun z => bernoulliFullRowWeight p cfg * z) (ih known)
          · simp only [hf, ↓reduceIte]
            exact congrArg (fun z => bernoulliFullRowWeight p cfg * z) (ih (insert w known))
        · exact fullLigationRow_choice p known w (continuation known) (continuation (insert w known))
      have hhistory : (∑ bits : Fin (w :: rest).length → Bool,
          ligationHistoryWeight p (w :: rest) bits known *
            payoff (ligationHistoryKnown (w :: rest) bits known)) =
          (1-ligationFailureChance p known w) * continuation (insert w known) +
            ligationFailureChance p known w * continuation known := by
        trans ∑ b : Bool, ∑ tail : Fin rest.length → Bool,
          ligationHistoryWeight p (w :: rest) (Fin.cons b tail) known *
            payoff (ligationHistoryKnown (w :: rest) (Fin.cons b tail) known)
        · exact sum_bool_history_cons rest.length _
        rw [Fintype.sum_bool]
        change (∑ tail : Fin rest.length → Bool,
            ((1-ligationFailureChance p known w) * ligationHistoryWeight p rest tail (insert w known)) *
              payoff (ligationHistoryKnown rest tail (insert w known))) +
          (∑ tail : Fin rest.length → Bool,
            (ligationFailureChance p known w * ligationHistoryWeight p rest tail known) *
              payoff (ligationHistoryKnown rest tail known)) = _
        simp only [mul_assoc, ← Finset.mul_sum]
        rfl
      rw [hraw, hhistory]
      ring

theorem ligationRawWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (cfg : LigationRawConfiguration words) :
    0 ≤ ligationRawWeight p words cfg := by
  induction words with
  | nil => simp [ligationRawWeight]
  | cons w rest ih =>
      apply mul_nonneg _ (ih cfg.2)
      apply Finset.prod_nonneg
      intro i _
      unfold bernoulliBitWeight
      split_ifs
      · exact hp
      · exact sub_nonneg.mpr hp1

theorem sum_ligationRawWeight (p : ℝ) (words : List LigationWord) :
    (∑ cfg : LigationRawConfiguration words, ligationRawWeight p words cfg) = 1 := by
  have h := ligationRaw_history_expectation p words ∅ (fun _ => 1)
  simpa only [mul_one, sum_ligationHistoryWeight] using h

end PowerLawSmallRAF
