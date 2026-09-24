import proofs.CoreCouplingCAC.Source

namespace CoreCouplingCAC

/-! Exact comparison certificates. ODE and box applicability are separate obligations. -/
noncomputable def lowComparison : Fin 4 → Fin 4 → ℝ :=
  ![![(-50012970413/50000000000 : ℝ), (13470471/50000000000 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(50012970471/50000000000 : ℝ), (-149802670413/50000000000 : ℝ), (2002809/100000 : ℝ), (0 : ℝ)],
    ![(1 : ℝ), (399161/200000 : ℝ), (-21997167/500000 : ℝ), (3 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (999161/50000 : ℝ), (-20001/10000 : ℝ)]]
noncomputable def lowRight : Fin 4 → ℝ := ![(633/625 : ℝ), (48429/1000 : ℝ), (71441/10000 : ℝ), (89847/1250 : ℝ)]
noncomputable def lowLeft : Fin 4 → ℝ := ![(112193/2500 : ℝ), (88741/5000 : ℝ), (3267/125 : ℝ), (397021/10000 : ℝ)]
theorem low_comparison_certificate :
    (∀ i, 0 < lowRight i) ∧ (∀ i, 0 < lowLeft i) ∧
    (∀ i, (∑ j : Fin 4, lowComparison i j * lowRight j) < 0) ∧
    (∀ i, (∑ j : Fin 4, lowComparison j i * lowLeft j) < 0) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro i; fin_cases i <;> norm_num [lowRight,lowLeft,lowComparison,Fin.sum_univ_succ]

noncomputable def highComparison : Fin 4 → Fin 4 → ℝ :=
  ![![(-25010469361/25000000000 : ℝ), (2679847/6250000000 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(6252617347/6250000000 : ℝ), (-124419644361/25000000000 : ℝ), (12056999/1000000 : ℝ), (0 : ℝ)],
    ![(1 : ℝ), (1988189/500000 : ℝ), (-6483479/125000 : ℝ), (3 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (3488189/125000 : ℝ), (-20001/10000 : ℝ)]]
noncomputable def highRight : Fin 4 → ℝ := ![(5069/5000 : ℝ), (166069/5000 : ℝ), (67713/5000 : ℝ), (473619/2500 : ℝ)]
noncomputable def highLeft : Fin 4 → ℝ := ![(52644/625 : ℝ), (370897/10000 : ℝ), (92321/2000 : ℝ), (174343/2500 : ℝ)]
theorem high_comparison_certificate :
    (∀ i, 0 < highRight i) ∧ (∀ i, 0 < highLeft i) ∧
    (∀ i, (∑ j : Fin 4, highComparison i j * highRight j) < 0) ∧
    (∀ i, (∑ j : Fin 4, highComparison j i * highLeft j) < 0) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro i; fin_cases i <;> norm_num [highRight,highLeft,highComparison,Fin.sum_univ_succ]

end CoreCouplingCAC
