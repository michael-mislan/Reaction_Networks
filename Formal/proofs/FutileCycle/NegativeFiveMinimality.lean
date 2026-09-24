import proofs.FutileCycle.NegativeFive

namespace FutileCycle
noncomputable section
open Matrix DUnstableCores

theorem negativeFive_padded_no_rhp (p : Fin 5 → Prop) [DecidablePred p]
    (hp : ∃ i, ¬p i) (d : Fin 5 → ℝ) (hd : ∀ i, 0 < d i)
    (z : ℂ) (hz : 0 < z.re) (w : Fin 5 → ℂ)
    (he : padded (complexify (rightScale negativeFive d)) p *ᵥ w=z • w) : w=0 := by
  classical
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hwzero (i) (hi : ¬p i) : w i=0 := by
    have hh := congrFun he i
    simp [padded, Matrix.mulVec, dotProduct, hi] at hh
    exact hh.resolve_left hz0
  let u : Fin 5 → ℂ := fun i => (d i:ℂ)*w i
  let a : Fin 5 → ℂ := fun i => 1+z/(d i:ℂ)
  have hu0 (i) (hi : ¬p i) : u i=0 := by simp [u,hwzero i hi]
  have ha (i) : 1 < (a i).re := resolvent_re z _ hz (hd i)
  have rows (i) (hi : p i) : (complexify negativeFive *ᵥ u) i=z*w i := by
    have hh := congrFun he i
    have heq : (padded (complexify (rightScale negativeFive d)) p *ᵥ w) i =
        (complexify negativeFive *ᵥ u) i := by
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : p j
      · simp [padded, hi,hj,complexify,rightScale,u,mul_assoc]
      · simp [padded,hi,hj,u,hwzero j hj]
    rw [heq] at hh
    exact hh
  have equations (i) (hi : p i) : a i*u i = (complexify negativeFive *ᵥ u) i+u i := by
    rw [rows i hi]
    dsimp [a,u]
    rw [resolvent_mul z _ _ (hd i), add_comm]
  have e0 (h : p 0) : a 0*u 0 = -u 3 := by
    have hh := equations 0 h
    simpa [negativeFive,complexify,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
  have e1 (h : p 1) : a 1*u 1 = u 4 := by
    have hh := equations 1 h
    simpa [negativeFive,complexify,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
  have e2 (h : p 2) : a 2*u 2 = -u 0+u 4 := by
    have hh := equations 2 h
    simp [negativeFive,complexify,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hh
    linear_combination hh
  have e3 (h : p 3) : a 3*u 3 = -u 1 := by
    have hh := equations 3 h
    simpa [negativeFive,complexify,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
  have e4 (h : p 4) : a 4*u 4 = u 2 := by
    have hh := equations 4 h
    simpa [negativeFive,complexify,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
  have bound (i : Fin 5) (v : ℂ) (hr : p i → a i*u i=v) : ‖u i‖ ≤ ‖v‖ := by
    by_cases hi : p i
    · by_cases hui : u i=0
      · simp [hui]
      · exact (norm_lt_of_amplifier _ _ _ (ha i) hui (hr hi)).le
    · simp [hu0 i hi]
  have h03 : ‖u 0‖ ≤ ‖u 3‖ := by simpa using bound 0 _ e0
  have h31 : ‖u 3‖ ≤ ‖u 1‖ := by simpa using bound 3 _ e3
  have h14 := bound 1 _ e1
  have h42 := bound 4 _ e4
  have hzero : u 0=0 := by
    obtain ⟨i,hi⟩ := hp
    have hzi := hu0 i hi
    fin_cases i <;> simp only [Fin.reduceFinMk] at hzi ⊢
    · exact hzi
    all_goals
      have hnorm := congrArg norm hzi
      simp only [norm_zero] at hnorm
      apply norm_le_zero_iff.mp
      linarith
  have htwo : u 2=0 := by
    by_contra hh
    have hp2 : p 2 := by by_contra h; exact hh (hu0 2 h)
    have he2 := e2 hp2
    rw [hzero,neg_zero,zero_add] at he2
    have hs := norm_lt_of_amplifier _ _ _ (ha 2) hh he2
    linarith
  have hall (i : Fin 5) : u i=0 := by
    fin_cases i <;> change u _ = 0
    · exact hzero
    · change u 1 = 0
      apply norm_le_zero_iff.mp; rw [htwo,norm_zero] at h42; linarith
    · exact htwo
    · change u 3 = 0
      apply norm_le_zero_iff.mp; rw [htwo,norm_zero] at h42; linarith
    · exact norm_eq_zero.mp (by rw [htwo,norm_zero] at h42; exact le_antisymm h42 (norm_nonneg _))
  funext i
  have hdi : (d i:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hd i)
  exact (mul_eq_zero.mp (hall i)).resolve_left hdi

theorem negativeFive_proper_dNon (s : Finset (Fin 5)) (hs : s ≠ Finset.univ) :
    DNonUnstable (negativeFive.submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
  classical
  intro d hd
  let df : Fin 5 → ℝ := fun i => if h : i ∈ s then d ⟨i,h⟩ else 1
  have hdf i : 0 < df i := by dsimp [df]; split_ifs with h; exact hd ⟨i,h⟩; norm_num
  have hp : ∃ i : Fin 5, i ∉ s := by
    by_contra h; push Not at h; exact hs (Finset.eq_univ_of_forall h)
  rintro ⟨z,v,hz,hv,he⟩
  obtain ⟨w,hw,hew⟩ := principal_eigenpair_extends (complexify (rightScale negativeFive df))
    (fun i => i ∈ s) z v hv (by
      funext i
      calc
        _ = (complexify (rightScale (negativeFive.submatrix
            (fun i : s => i.val) (fun i : s => i.val)) d) *ᵥ v) i := by
          unfold Matrix.mulVec dotProduct
          apply Finset.sum_congr
          · ext j; simp
          · intro j _; simp [complexify,rightScale,df,j.property]
        _ = _ := he i)
  exact hw (negativeFive_padded_no_rhp (fun i => i ∈ s) hp df hdf z hz w hew)

def negativeFiveChildAt (n : ℕ) (hn : 3 ≤ n) : Child (futile n) (Fin 5) where
  species i := (negativeChildAt n hn).species i.castSucc
  species_injective := (negativeChildAt n hn).species_injective.comp (Fin.castSucc_injective _)
  reaction i := (negativeChildAt n hn).reaction i.castSucc
  reaction_injective := (negativeChildAt n hn).reaction_injective.comp (Fin.castSucc_injective _)
  supported i := (negativeChildAt n hn).supported i.castSucc

theorem negativeFiveChildAt_matrix (n : ℕ) (hn : 3 ≤ n) :
    (negativeFiveChildAt n hn).matrix.map (fun x : ℤ => (x:ℝ))=negativeFive := by
  have hh := negativeChildAt_matrix n hn
  ext i j
  change ((negativeChildAt n hn).matrix i.castSucc j.castSucc : ℝ)=_
  rw [hh]
  fin_cases i <;> fin_cases j <;> norm_num [negativeMatrix,negativeFive]

theorem negativeFive_core_all_n (n : ℕ) (hn : 3 ≤ n) :
    ∃ J : Child (futile n) (Fin 5),
      DUnstable (J.matrix.map (fun x : ℤ => (x:ℝ))) ∧
      ∀ s : Finset (Fin 5), s ≠ Finset.univ →
        DNonUnstable ((J.matrix.map (fun x : ℤ => (x:ℝ))).submatrix
          (fun i : s => i.val) (fun i : s => i.val)) := by
  refine ⟨negativeFiveChildAt n hn,?_,?_⟩
  · rw [negativeFiveChildAt_matrix]; exact negativeFive_dUnstable
  · rw [negativeFiveChildAt_matrix]; exact negativeFive_proper_dNon

end
end FutileCycle
