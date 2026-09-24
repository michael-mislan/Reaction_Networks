import proofs.SmallResidentCompositionCopying.FiniteFoodRobustness
import proofs.HeritableCompositions.BinomialMoment

namespace SmallResidentCompositionCopying.FiniteFood
open FiniteCopy CompositionalMemory HeritableCompositions
noncomputable section

def singleReturn (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (n+2), if a=0 ∨ a=n+1 then 0 else fairBinomialWeight (n+1) a

theorem single_return (n : ℕ) : singleReturn n=1-(1/2:ℝ)^n := by
  have h := fair_binomial_sum (n+1)
  have he : fairBinomialWeight (n+1) 0 + fairBinomialWeight (n+1) (n+1)=(1/2:ℝ)^n := by
    simp only [fairBinomialWeight,Nat.choose_zero_right,Nat.choose_self,Nat.cast_one,
      pow_succ,div_pow,one_pow]
    ring
  have hs : singleReturn n + (fairBinomialWeight (n+1) 0 + fairBinomialWeight (n+1) (n+1)) =
      ∑ a ∈ Finset.range (n+2), fairBinomialWeight (n+1) a := by
    unfold singleReturn
    have hh : (∑ a ∈ Finset.range (n+2), if a=0 ∨ a=n+1 then fairBinomialWeight (n+1) a else 0) =
        fairBinomialWeight (n+1) 0 + fairBinomialWeight (n+1) (n+1) := by
      have ht (a : ℕ) : (if a=0 ∨ a=n+1 then fairBinomialWeight (n+1) a else 0)=
          (if a=0 then fairBinomialWeight (n+1) a else 0)+
          (if a=n+1 then fairBinomialWeight (n+1) a else 0) := by
        by_cases h0 : a=0 <;> by_cases h1 : a=n+1 <;> simp_all
      simp_rw [ht]
      simp [Finset.sum_add_distrib]
    rw [← hh,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [he] at hs
  change (∑ a ∈ Finset.range (n+2), fairBinomialWeight (n+1) a)=1 at h
  linarith

def actualPayoff {K : ℕ} (z : Counts K) : ℝ := singleReturn z.1.val*singleReturn z.2.val
theorem actual_payoff {K : ℕ} : (actualPayoff : Counts K → ℝ)=reward := by
  funext z
  simp [actualPayoff,single_return,reward,g]

def actualReturn (p : Rates) (K : ℕ) (word : Word) (z : Counts K) : ℝ :=
  finiteTimeExpectation (chemistry p K word) 20 actualPayoff z
theorem actual_return {K : ℕ} (p : Rates) (word : Word) (z : Counts K) :
    actualReturn p K word z=finiteTimeExpectation (model p K) 20 reward z := by
  rw [actualReturn,word_law,actual_payoff]

/-- All molecules, including food, are split. Refill reads module total only. -/
theorem refill (K A B : ℕ) (h : A+B=K) : (K-A)+(K-B)=K := by omega

theorem admitted_daughters (K n a : ℕ) (hn : n≤K) (ha : 0<a) (hb : a<n) :
    1≤a ∧ a≤K-1 ∧ 1≤n-a ∧ n-a≤K-1 := by omega

theorem food_refill (K n a f : ℕ) (hn : n≤K) (ha : a≤n) (hf : f≤K-n) :
    a+f+(K-(a+f))=K ∧ f+(K-(a+f))=K-a := by omega

theorem return9 (word : Word) (z : Counts 9) :
    (8046297159:ℝ)/8112104000 ≤ actualReturn nominal 9 word z := by
  rw [actual_return]; exact nominal9 z

theorem return20 (word : Word) (z : Counts 20) :
    (7077818258231:ℝ)/7077927321600 ≤ actualReturn nominal 20 word z := by
  rw [actual_return]; exact nominal20 z

theorem return_box (p : Rates) (hp : OperatingBox p) (word : Word) (z : Counts 9) :
    (114080769:ℝ)/115203200 ≤ actualReturn p 9 word z := by
  rw [actual_return]; exact robust9 p hp z

end
end SmallResidentCompositionCopying.FiniteFood
