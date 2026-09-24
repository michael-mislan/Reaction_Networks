import proofs.SmallResidentCompositionCopying.FiniteFoodSource

namespace SmallResidentCompositionCopying.FiniteFood
open Classical
noncomputable section

abbrev Species := Fin 2 × Bool
def newborn {K : ℕ} (z : Counts K) : Prop := z.1.val+1<K ∧ z.2.val+1<K
def total {K : ℕ} (z : Counts K) : ℕ := z.1.val+z.2.val+2
def composition {K : ℕ} (w : Word) (z : Counts K) (s : Species) : ℝ :=
  (resident w z s.1 s.2:ℝ)/(total z:ℝ)
def distance {K : ℕ} (w v : Word) (z t : Counts K) : ℝ :=
  ∑ s : Species, |composition w z s-composition v t s|

theorem budgets {K : ℕ} (z : Counts K) : total z≤2*K ∧ (newborn z → total z≤2*(K-1)) := by
  have := z.1.isLt; have := z.2.isLt
  dsimp [total,newborn]; omega

theorem occupied {K : ℕ} (w : Word) (z : Counts K) (hz : newborn z) (i : Fin 2) :
    1/(K:ℝ)≤composition w z (i,w i) := by
  have hK : 0<K := by have := z.1.isLt; omega
  have hK' : (0:ℝ)<K := by exact_mod_cast hK
  have ht : (0:ℝ)<total z := by dsimp [total]; positivity
  have ha : (z.1.val:ℝ)+2≤K := by exact_mod_cast (show z.1.val+2≤K from hz.1)
  have hb : (z.2.val:ℝ)+2≤K := by exact_mod_cast (show z.2.val+2≤K from hz.2)
  have ha0 : (0:ℝ)≤z.1.val := Nat.cast_nonneg _
  have hb0 : (0:ℝ)≤z.2.val := Nat.cast_nonneg _
  have hKm : (0:ℝ)≤K-1 := by linarith
  simp only [composition,resident,ite_true]
  apply (div_le_div_iff₀ hK' ht).2
  fin_cases i <;> norm_num [count,total] <;>
    nlinarith [mul_nonneg hKm ha0,mul_nonneg hKm hb0]

theorem separated {K : ℕ} (w v : Word) (z t : Counts K)
    (hz : newborn z) (ht : newborn t) (hne : w≠v) : (2:ℝ)/K≤distance w v z t := by
  obtain ⟨i,hi⟩ : ∃ i,w i≠v i := by
    by_contra h; push Not at h; exact hne (funext h)
  have h1 := occupied w z hz i
  have h2 := occupied v t ht i
  have hp1 : 0≤composition w z (i,w i) := by dsimp [composition]; positivity
  have hp2 : 0≤composition v t (i,v i) := by dsimp [composition]; positivity
  have he1 : composition v t (i,w i)=0 := by simp [composition,resident,Ne.symm hi]
  have he2 : composition w z (i,v i)=0 := by simp [composition,resident,hi]
  have hn : (i,w i)≠(i,v i) := by simp [hi]
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({(i,w i),(i,v i)} : Finset Species))
    (fun s _ _ => abs_nonneg (composition w z s-composition v t s))
  simp only [Finset.sum_pair hn,he1,he2,sub_zero,zero_sub,abs_neg,
    abs_of_nonneg hp1,abs_of_nonneg hp2] at hs
  rw [show (2:ℝ)/K=1/K+1/K by ring]
  exact le_trans (add_le_add h1 h2) hs

def decoder (p : Species → ℝ) (i : Fin 2) : Bool := decide (0<p (i,true))
theorem decode {K : ℕ} (w : Word) (z : Counts K) : decoder (composition w z)=w := by
  funext i
  have ht : (0:ℝ)<total z := by dsimp [total]; positivity
  cases h : w i
  · simp [decoder,composition,resident,h]
  · have hp : 0<composition w z (i,true) := by
      simp only [composition,resident,h,ite_true]
      apply div_pos _ ht
      positivity
    simp [decoder,hp]

end
end SmallResidentCompositionCopying.FiniteFood
