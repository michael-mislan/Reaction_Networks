import proofs.SmallResidentCompositionCopying.AmplificationGeometry

namespace SmallResidentCompositionCopying.Amplification
open Classical
noncomputable section

theorem sharp_separated_words (word word' : Word) (z z' : Counts)
    (hz : newborn z) (hz' : newborn z') (hne : word≠word') :
    (1:ℝ)/10 ≤ distance word word' z z' := by
  obtain ⟨i,hi⟩ : ∃ i,word i≠word' i := by
    by_contra h; push Not at h; exact hne (funext h)
  have h1 := occupied_mass word z hz i
  have h2 := occupied_mass word' z' hz' i
  have he1 : composition word' z' (i,word i)=0 := by simp [composition,resident,Ne.symm hi]
  have he2 : composition word z (i,word' i)=0 := by simp [composition,resident,hi]
  have hn : (i,word i) ≠ (i,word' i) := by simp [hi]
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({(i,word i),(i,word' i)} : Finset Species))
    (fun s _ _ => abs_nonneg (composition word z s-composition word' z' s))
  simp only [Finset.sum_pair hn,he1,he2,sub_zero,zero_sub,abs_neg,
    abs_of_nonneg (by linarith : 0≤composition word z (i,word i)),
    abs_of_nonneg (by linarith : 0≤composition word' z' (i,word' i))] at hs
  dsimp [distance]
  linarith

end
end SmallResidentCompositionCopying.Amplification
