import proofs.ThermoCoreCompatibility.Hypergraph.TripleMargin

namespace ThermoCoreCompatibility.Hypergraph.MonomialTriple

theorem current_perturbation {b c x y ρ : ℝ} (hr : 0 ≤ ρ)
    (hb : |c-b| ≤ ρ) (hx : 0 ≤ x) (hxu : x ≤ 1) (hy : 0 ≤ y) (hyu : y ≤ 1) :
    |c*(x-y)-b*(x-y)| ≤ ρ := by
  have hd : |x-y| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ = |c-b| * |x-y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ ρ*1 := mul_le_mul hb hd (abs_nonneg _) hr
    _ = ρ := mul_one _

theorem production_perturbation {m p q p' q' ρ : ℝ}
    (hm : 0 ≤ m) (hmu : m ≤ 4) (hr : 0 ≤ ρ)
    (hp : |p'-p| ≤ ρ) (hq : |q'-q| ≤ ρ) :
    |(m*q'-p')-(m*q-p)| ≤ 5*ρ := by
  have h := abs_add_le (m*(q'-q)) (-(p'-p))
  have hmabs : |m| = m := abs_of_nonneg hm
  rw [abs_mul,hmabs,abs_neg] at h
  have hq' := mul_le_mul_of_nonneg_left hq hm
  have hm' := mul_le_mul_of_nonneg_right hmu hr
  have he : (m*q'-p')-(m*q-p) = m*(q'-q)+(-(p'-p)) := by ring
  rw [he]
  linarith

/-- Source-coordinate margin, valid without assuming productivity. -/
theorem source_coordinate_margin {A B C₀ C₁ C₂ τ : ℝ}
    (ha : 0 ≤ A) (hu : C₀ ≤ 89/125) (hl : 81/125 ≤ C₁)
    (h₀ : τ ≤ A-5*B+4*C₀)
    (h₁ : τ ≤ B/2-3*C₁/2+A^4)
    (h₂ : τ ≤ 3*(C₂-A^3)-(A-B))
    (h₃ : τ ≤ (B-C₂)-(C₂-A^3)) : τ ≤ -3/500 := by
  apply negative_margin (B := B) ha hu hl <;> linarith

noncomputable def residual (D : FanData (Fin 3)) (A B : ℝ) (C : Fin 3 → ℝ)
    (i k : Fin 3) : ℝ :=
  let j := D.sharedFactor*(A-B)
  let p := D.firstFactor i*(B-C i)
  let q := D.secondFactor i*(C i-A^(D.gain i))
  ![(D.gain i:ℝ)*q-j,j-p,p-q] k

def Near (D : FanData (Fin 3)) (la ua lb ub : ℝ) : Prop :=
  (∀ i, D.gain i=data.gain i) ∧
  |D.sharedFactor-1| ≤ 1/1000000 ∧
  (∀ i, |D.firstFactor i-data.firstFactor i| ≤ 1/1000000) ∧
  (∀ i, |D.secondFactor i-data.secondFactor i| ≤ 1/1000000) ∧
  (∀ i, |D.lower i-data.lower i| ≤ 1/1000000) ∧
  (∀ i, |D.upper i-data.upper i| ≤ 1/1000000) ∧
  |la-1/10| ≤ 1/1000000 ∧ |ua-9/10| ≤ 1/1000000 ∧
  |lb-1/10| ≤ 1/1000000 ∧ |ub-9/10| ≤ 1/1000000

theorem residual_error (D : FanData (Fin 3)) (la ua lb ub A B : ℝ) (C : Fin 3 → ℝ)
    (hn : Near D la ua lb ub) (ha : 0 ≤ A) (hau : A ≤ 1)
    (hb : 0 ≤ B) (hbu : B ≤ 1) (hc : ∀ i, 0 ≤ C i ∧ C i ≤ 1) (i k : Fin 3) :
    |residual D A B C i k-residual data A B C i k| ≤ 5*(1/1000000) := by
  obtain ⟨hg,h₀,h₁,h₂,_⟩ := hn
  have ht := pow_le_one₀ ha hau (n := data.gain i)
  have ht₀ := pow_nonneg ha (data.gain i)
  have hj := current_perturbation (by norm_num : (0:ℝ) ≤ 1/1000000) h₀ ha hau hb hbu
  have hp := current_perturbation (by norm_num : (0:ℝ) ≤ 1/1000000) (h₁ i) hb hbu (hc i).1 (hc i).2
  have hq := current_perturbation (by norm_num : (0:ℝ) ≤ 1/1000000) (h₂ i) (hc i).1 (hc i).2 ht₀ ht
  have hm : (data.gain i:ℝ) ≤ 4 := by fin_cases i <;> norm_num [data]
  fin_cases k
  · simpa only [residual,hg i,data,Matrix.cons_val_zero,one_mul] using
      production_perturbation (Nat.cast_nonneg (data.gain i)) hm (by norm_num) hj hq
  · simpa only [residual,hg i,data,Matrix.cons_val_one,one_mul] using
      production_perturbation (m:=1) (by norm_num) (by norm_num) (by norm_num) hp hj
  · simpa only [residual,hg i,data,Matrix.cons_val_two,one_mul] using
      production_perturbation (m:=1) (by norm_num) (by norm_num) (by norm_num) hq hp

theorem residual_positive_iff (D : FanData (Fin 3)) (A B : ℝ) (C : Fin 3 → ℝ) (i : Fin 3) :
    (∀ k, 0 < residual D A B C i k) ↔
      TriangleProduction (D.gain i) (D.firstFactor i) (D.secondFactor i)
        (A^(D.gain i)) B (C i) (D.sharedFactor*(A-B)) := by
  simp [Fin.forall_fin_succ,residual,TriangleProduction,sub_pos]

end ThermoCoreCompatibility.Hypergraph.MonomialTriple
