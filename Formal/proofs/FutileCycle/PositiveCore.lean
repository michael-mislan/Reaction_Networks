import proofs.FutileCycle.PositiveStructure
import proofs.FutileCycle.FlowerScaledMinimality
import proofs.FutileCycle.SignConjugacy
import proofs.FutileCycle.NegativeCore

namespace FutileCycle
noncomputable section
open Matrix DUnstableCores

def positiveRealMatrix (n : ℕ) (hn : 2 ≤ n) :
    Matrix (PositiveIndex n) (PositiveIndex n) ℝ :=
  (positiveChild n hn).matrix.map (fun x : ℤ => (x:ℝ))

theorem positive_det (n : ℕ) (hn : 2 ≤ n) : (positiveChild n hn).matrix.det=1 := by
  rw [sign_conjugate_det (positiveSign n) (positiveSign_sq n)
    (flowerMatrix (2*n-1)) _ (positive_source_flower n hn), flowerMatrix_det]
  have he : 2*n-1+1=2*n := by omega
  rw [he, pow_mul]
  norm_num

theorem positive_complex_entry (n : ℕ) (hn : 2 ≤ n) (i j : PositiveIndex n) :
    complexify (positiveRealMatrix n hn) i j =
      (positiveSign n i:ℂ) * flowerComplex (2*n-1) i j * (positiveSign n j:ℂ) := by
  simp only [complexify, positiveRealMatrix, Matrix.map_apply]
  rw [positive_source_flower]
  simp [flowerComplex]

theorem positive_unstable (n : ℕ) (hn : 2 ≤ n) :
    HurwitzUnstable (positiveRealMatrix n hn) := by
  obtain ⟨z,w,hz,hw,he⟩ := flower_eigenpair (2*n-1) (by omega)
  have hs (i : PositiveIndex n) : (positiveSign n i:ℂ)*(positiveSign n i:ℂ)=1 := by
    exact_mod_cast positiveSign_sq n i
  have hrev (i j : PositiveIndex n) : flowerComplex (2*n-1) i j =
      (positiveSign n i:ℂ) * complexify (positiveRealMatrix n hn) i j * (positiveSign n j:ℂ) := by
    rw [positive_complex_entry]
    symm
    calc
      _ = ((positiveSign n i:ℂ)*(positiveSign n i:ℂ)) *
          flowerComplex (2*n-1) i j *
          ((positiveSign n j:ℂ)*(positiveSign n j:ℂ)) := by ring
      _ = _ := by rw [hs, hs, one_mul, mul_one]
  obtain ⟨hv,hev⟩ := sign_conjugate_eigenpair (fun i => (positiveSign n i:ℂ)) hs
    (complexify (positiveRealMatrix n hn)) (flowerComplex (2*n-1)) hrev z w hw he
  exact ⟨z,_,hz,hv,fun i => congrFun hev i⟩

theorem positive_padded_scaled_no_rhp (n : ℕ) (hn : 2 ≤ n)
    (p : PositiveIndex n → Prop) [DecidablePred p] (hp : ∃ i, ¬p i)
    (d : PositiveIndex n → ℝ) (hd : ∀ i, 0 < d i)
    (z : ℂ) (hz : 0 < z.re) (w : PositiveIndex n → ℂ) (hw : w ≠ 0)
    (he : padded (complexify (rightScale (positiveRealMatrix n hn) d)) p *ᵥ w=z • w) :
    False := by
  have hs (i : PositiveIndex n) : (positiveSign n i:ℂ)*(positiveSign n i:ℂ)=1 := by
    exact_mod_cast positiveSign_sq n i
  have hb (i j : PositiveIndex n) :
      padded (complexify (rightScale (positiveRealMatrix n hn) d)) p i j =
      (positiveSign n i:ℂ) *
        padded (fun i j => flowerComplex (2*n-1) i j * (d j:ℂ)) p i j *
        (positiveSign n j:ℂ) := by
    by_cases hij : p i ∧ p j
    · simp only [padded, if_pos hij, complexify, rightScale, Complex.ofReal_mul]
      change complexify (positiveRealMatrix n hn) i j * (d j:ℂ) = _
      rw [positive_complex_entry]
      ring
    · simp [padded, hij]
  obtain ⟨hv,hev⟩ := sign_conjugate_eigenpair _ hs _ _ hb z w hw he
  exact hv (flower_scaled_no_rhp (2*n-1) p hp d hd z hz _ hev)

theorem positive_proper_scaling (n : ℕ) (hn : 2 ≤ n)
    (s : Finset (PositiveIndex n)) (hs : s ≠ Finset.univ)
    (d : s → ℝ) (hd : ∀ i, 0 < d i) :
    HurwitzNonpositive (rightScale ((positiveRealMatrix n hn).submatrix
      (fun i : s => i.val) (fun i : s => i.val)) d) := by
  classical
  let dfull : PositiveIndex n → ℝ := fun i => if h : i ∈ s then d ⟨i,h⟩ else 1
  have hdfull i : 0 < dfull i := by
    dsimp [dfull]
    split_ifs with h
    · exact hd ⟨i,h⟩
    · norm_num
  have hp : ∃ i : PositiveIndex n, i ∉ s := by
    by_contra hh
    push Not at hh
    exact hs (Finset.eq_univ_of_forall hh)
  rintro ⟨z,v,hz,hv,he⟩
  obtain ⟨w,hw,hew⟩ := principal_eigenpair_extends
    (complexify (rightScale (positiveRealMatrix n hn) dfull)) (fun i => i ∈ s) z v hv (by
      funext i
      calc
        _ = (complexify (rightScale ((positiveRealMatrix n hn).submatrix
            (fun i : s => i.val) (fun i : s => i.val)) d) *ᵥ v) i := by
          unfold Matrix.mulVec dotProduct
          apply Finset.sum_congr
          · ext j; simp
          · intro j _
            simp [complexify, rightScale, dfull, j.property]
        _ = _ := he i)
  exact positive_padded_scaled_no_rhp n hn (fun i => i ∈ s) hp dfull hdfull z hz w hw hew

theorem positive_minimal (n : ℕ) (hn : 2 ≤ n) :
    MinimalUnstable (positiveRealMatrix n hn) := by
  refine ⟨positive_unstable n hn,?_⟩
  intro s hs
  simpa only [rightScale_one] using positive_proper_scaling n hn s hs (fun _ => 1)
    (fun _ => by norm_num)

end
end FutileCycle
