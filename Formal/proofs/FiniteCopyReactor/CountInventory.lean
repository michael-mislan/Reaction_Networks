import proofs.FiniteCopyReactor.Template
import proofs.FiniteCopyReactor.PulseInventory

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

def templateStock (N : Counts) : ℝ := (N 2:ℝ)+N 3+N 4+2*N 5

/-- Net internal template production, including the driven destruction/creation pair. -/
def synthesisMark : CompetitionChannel → ℝ
  | .inl j => (basalMark j+catalyticMark j)/4
  | .inr j => if j=0 then -1 else 1

theorem product_count_template (N : Counts) :
    (∑ i,productSpecies i*(N i:ℝ))=4*templateStock N := by
  norm_num [productSpecies,Fin.sum_univ_succ,templateStock]
  change 4*(N 2:ℝ)+(4*(N 3:ℝ)+(4*(N 4:ℝ)+8*(N 5:ℝ))) = _
  ring

theorem source_template_inventory (N : Counts) (j : CompetitionChannel)
    (h : ∀ i,reactants (competitionBase j) i ≤ N i) :
    templateStock (competitionNext N j)-templateStock N=synthesisMark j-templateMark j := by
  have hd := next_linear_difference N (competitionBase j) productSpecies h
  rw [product_stoich,product_count_template,product_count_template] at hd
  have he : basalMark (competitionBase j)+catalyticMark (competitionBase j)-exportMark (competitionBase j)=
      4*(synthesisMark j-templateMark j) := by
    cases j with
    | inl j => fin_cases j <;> norm_num [competitionBase,basalMark,catalyticMark,exportMark,synthesisMark,templateMark]
    | inr j => fin_cases j <;> norm_num [competitionBase,drivenBase,basalMark,catalyticMark,exportMark,synthesisMark,templateMark]
  rw [he] at hd
  change 4*templateStock (competitionNext N j)-4*templateStock N=4*(synthesisMark j-templateMark j) at hd
  linarith

theorem pulse_template_inventory (N : Counts) (V : ℕ) (p : Intervention) (o : PulseOutcome N) :
    templateStock (postPulseCounts N V p o)+templateStock (categoryCounts N o 1)+
      templateStock (categoryCounts N o 2)=templateStock N := by
  have h2 := category_inventory N o 2
  have h3 := category_inventory N o 3
  have h4 := category_inventory N o 4
  have h5 := category_inventory N o 5
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h2 h3 h4 h5
  change categoryCounts N o 0 2+(categoryCounts N o 1 2+categoryCounts N o 2 2)=N 2 at h2
  change categoryCounts N o 0 3+(categoryCounts N o 1 3+categoryCounts N o 2 3)=N 3 at h3
  change categoryCounts N o 0 4+(categoryCounts N o 1 4+categoryCounts N o 2 4)=N 4 at h4
  change categoryCounts N o 0 5+(categoryCounts N o 1 5+categoryCounts N o 2 5)=N 5 at h5
  rw [← add_assoc] at h2 h3 h4 h5
  have h2' : (categoryCounts N o 0 2:ℝ)+categoryCounts N o 1 2+categoryCounts N o 2 2=N 2 := by exact_mod_cast h2
  have h3' : (categoryCounts N o 0 3:ℝ)+categoryCounts N o 1 3+categoryCounts N o 2 3=N 3 := by exact_mod_cast h3
  have h4' : (categoryCounts N o 0 4:ℝ)+categoryCounts N o 1 4+categoryCounts N o 2 4=N 4 := by exact_mod_cast h4
  have h5' : (categoryCounts N o 0 5:ℝ)+categoryCounts N o 1 5+categoryCounts N o 2 5=N 5 := by exact_mod_cast h5
  norm_num [templateStock,postPulseCounts]
  linarith

/-- Every finite supported reaction path satisfies the literal template inventory. -/
theorem finite_path_inventory (n : ℕ) (N : ℕ → Counts) (j : ℕ → CompetitionChannel)
    (hs : ∀ k < n, ∀ i,reactants (competitionBase (j k)) i ≤ N k i)
    (hn : ∀ k < n,N (k+1)=competitionNext (N k) (j k)) :
    templateStock (N n)-templateStock (N 0)=
      (∑ k ∈ Finset.range n,synthesisMark (j k))-(∑ k ∈ Finset.range n,templateMark (j k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun k hk => hs k (by omega)) (fun k hk => hn k (by omega))
    have hstep := source_template_inventory (N n) (j n) (hs n (by omega))
    rw [← hn n (by omega)] at hstep
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    linarith

theorem templateStock_nonneg (N : Counts) : 0 ≤ templateStock N := by unfold templateStock; positivity

end
end FiniteCopyReactor
