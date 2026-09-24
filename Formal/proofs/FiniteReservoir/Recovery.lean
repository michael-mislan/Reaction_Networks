import proofs.FiniteReservoir.FiniteModel
import proofs.FiniteCopyReactor.EntryProbability

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy

def entryModel (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (H : ℝ) :=
  model V M p hV (fun N => resourceGood N V ∧ weightedCount N < H)

def entryTest (V M : ℕ) (H s : ℝ) (X : BoxState V M) : ℝ :=
  RandomViability.Binding.entryTest V H s X.1

theorem entry_total (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (H : ℝ) (X : BoxState V M) : (entryModel V M p hV H).total X ≤ 3000*(V:ℝ) :=
  model_total V M p hV _ (fun _ h => h.1) X

theorem entry_inside (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (H s : ℝ) (X : BoxState V M) (h : entryActive V H X.1) :
    (entryModel V M p hV H).generator (entryTest V M H s) X ≤
      generator (boxCounts X.1) V p.release
        (alpha (bathOf X.2) p.cleavage p.capacity) (beta (bathOf X.2) p.cleavage p.capacity)
        (fun N => Real.exp (-s*weightedCount N)) := by
  rw [← model_inside V M p hV (fun N => resourceGood N V ∧ weightedCount N < H) X h h.1]
  apply FiniteJumpModel.generator_mono_at
  · simp [entryTest,RandomViability.Binding.entryTest,h]
  · intro j
    unfold entryTest RandomViability.Binding.entryTest
    split_ifs
    · exact le_rfl
    · positivity

theorem entry_step_transfer (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (H s t : ℝ) (hH : H ≤ (3/50)*(V:ℝ)) (hs : 0 ≤ s) (hs' : s ≤ 1/100)
    (ht : t ≤ (1+(5/8)/(3000*(V:ℝ)))*s) (X : BoxState V M) :
    ((entryModel V M p hV H).uniformize (3000*(V:ℝ)) (by positivity)
      (entry_total V M p hV H)).step (entryTest V M H s) X ≤ entryTest V M H t X := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases h : entryActive V H X.1
  · have hg := (entry_inside V M p hV H s X h).trans
      (corridor_stock_exponential _ V p.release _ _ s hV p.release_lower p.release_upper
        (parameters_box p X.2) h.1 (h.2.le.trans hH) hs hs')
    have hdiv := div_le_div_of_nonneg_right hg (show 0 ≤ 3000*(V:ℝ) by positivity)
    simp only [entryTest,RandomViability.Binding.entryTest,if_pos h]
    calc
      _ ≤ Real.exp (-s*weightedCount (boxCounts X.1)) *
          (1+(-(5/8)*s*weightedCount (boxCounts X.1))/(3000*(V:ℝ))) := by
        calc
          _ ≤ Real.exp (-s*weightedCount (boxCounts X.1)) +
              Real.exp (-s*weightedCount (boxCounts X.1)) *
                (-(5/8)*s*weightedCount (boxCounts X.1))/(3000*(V:ℝ)) :=
            add_le_add le_rfl hdiv
          _ = _ := by ring
      _ ≤ Real.exp (-s*weightedCount (boxCounts X.1)) *
          Real.exp ((-(5/8)*s*weightedCount (boxCounts X.1))/(3000*(V:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp ((-(5/8)*s*weightedCount (boxCounts X.1))/(3000*(V:ℝ)))]
      _ = Real.exp (-((1+(5/8)/(3000*(V:ℝ)))*s)*weightedCount (boxCounts X.1)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_right ht (weightedCount_nonneg (boxCounts X.1))
        linarith
  · have hh : ¬(resourceGood (boxCounts X.1) V ∧ weightedCount (boxCounts X.1)<H) := h
    rw [show (entryModel V M p hV H).generator (entryTest V M H s) X=0 from
      model_outside V M p hV _ X hh _]
    simp [entryTest,RandomViability.Binding.entryTest,h]

def entryKernel (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) : FiniteKernel (BoxState V M) :=
  (entryModel V M p hV ((3/50)*(V:ℝ))).uniformize (3000*(V:ℝ)) (by positivity)
    (entry_total V M p hV ((3/50)*(V:ℝ)))

theorem seeded_discrete_transfer (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (X : BoxState V M) :
    (entryKernel V M p hV).steps (8100*V) (entryTest V M ((3/50)*(V:ℝ)) (1/1000)) X ≤
      entryTest V M ((3/50)*(V:ℝ)) (101/20000) X := by
  apply steps_capped_target (entryKernel V M p hV)
    (entryTest V M ((3/50)*(V:ℝ))) (101/20000) (1+(5/8)/(3000*(V:ℝ)))
    (1/1000) (101/20000) (by norm_num) (le_add_of_nonneg_right (by positivity))
    (by norm_num) (by norm_num)
    (fun s t hst Y => RandomViability.Binding.entryTest_antitone V _ s t hst Y.1)
  · intro s hs hsc Y
    apply entry_step_transfer V M p hV _ s _ le_rfl hs (by linarith) (min_le_right _ _) Y
  · norm_num
  · have := FiniteCopyReactor.seeded_clock_growth V hV
    linarith

end
end FiniteReservoir
