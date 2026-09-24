import proofs.CompositionalMemory.SourceLocalGenerator
import proofs.CompositionalMemory.GlobalGeneratorBinding

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set

theorem low_count_generator_bound {k : ℕ} (hk : 1 ≤ k)
    (zc γ κ N : ℝ) (m : ℕ) (hmpos : 0 < m) (w : Fin k → Fin k → ℝ)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j) (i : Fin k) (n : Fin k → Counts)
    (hzc : zc ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates zc))
    (hN : 1 ≤ N) (hm : (k : ℝ)*N ≤ (m : ℝ))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (hz : ∀ j, 0 ≤ effectiveConcentration ((m : ℝ)/k) (n j) 2 ∧
      effectiveConcentration ((m : ℝ)/k) (n j) 2 ≤ 4)
    (hw : ∀ j, 0 ≤ w i j) (hs : ∑ j, w i j ≤ κ)
    (hy : ∀ a, |effectiveConcentration ((m : ℝ)/k) (n i) a-pointOfState (lift sourceRates zc) a| ≤ 1/400)
    (hnorm : normSq (fun a => effectiveConcentration ((m : ℝ)/k) (n i) a-
      pointOfState (lift sourceRates zc) a) ≤ 1/160000)
    (hx : ∀ a, |effectiveConcentration ((m : ℝ)/k) (n i) a| ≤ 35) :
    modularGenerator γ w
      (fun t => Real.exp ((1/1000000000000 : ℝ)*N*
        lowEnergy (fun a => modularConcentration t i a-pointOfState (lift sourceRates zc) a))) (n,m) ≤
      (1/1000000000000 : ℝ)*Real.exp ((1/1000000000000 : ℝ)*N*
        lowEnergy (fun a => effectiveConcentration ((m : ℝ)/k) (n i) a-pointOfState (lift sourceRates zc) a))*
        (-N*normSq (fun a => effectiveConcentration ((m : ℝ)/k) (n i) a-
          pointOfState (lift sourceRates zc) a)/4+200000000+1200000000*N*(γ+κ)^2) := by
  rw [global_local_generator hk γ w hdiag hsym (n,m) hmpos i
    (fun x => Real.exp ((1/1000000000000 : ℝ)*N*
      lowEnergy (fun a => x a-pointOfState (lift sourceRates zc) a)))]
  exact low_coupled_generator_bound hk zc γ κ (m : ℝ) N (w i) i n
    hzc hstationary hN hm hγ hγmax hκ hκmax hz hw hs hy hnorm hx

theorem high_count_generator_bound {k : ℕ} (hk : 1 ≤ k)
    (zc γ κ N : ℝ) (m : ℕ) (hmpos : 0 < m) (w : Fin k → Fin k → ℝ)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j) (i : Fin k) (n : Fin k → Counts)
    (hzc : zc ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates zc))
    (hN : 1 ≤ N) (hm : (k : ℝ)*N ≤ (m : ℝ))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (hz : ∀ j, 0 ≤ effectiveConcentration ((m : ℝ)/k) (n j) 2 ∧
      effectiveConcentration ((m : ℝ)/k) (n j) 2 ≤ 4)
    (hw : ∀ j, 0 ≤ w i j) (hs : ∑ j, w i j ≤ κ)
    (hy : ∀ a, |effectiveConcentration ((m : ℝ)/k) (n i) a-pointOfState (lift sourceRates zc) a| ≤ 1/400)
    (hnorm : normSq (fun a => effectiveConcentration ((m : ℝ)/k) (n i) a-
      pointOfState (lift sourceRates zc) a) ≤ 1/160000)
    (hx : ∀ a, |effectiveConcentration ((m : ℝ)/k) (n i) a| ≤ 35) :
    modularGenerator γ w
      (fun t => Real.exp ((1/1000000000000 : ℝ)*N*
        highEnergy (fun a => modularConcentration t i a-pointOfState (lift sourceRates zc) a))) (n,m) ≤
      (1/1000000000000 : ℝ)*Real.exp ((1/1000000000000 : ℝ)*N*
        highEnergy (fun a => effectiveConcentration ((m : ℝ)/k) (n i) a-pointOfState (lift sourceRates zc) a))*
        (-N*normSq (fun a => effectiveConcentration ((m : ℝ)/k) (n i) a-
          pointOfState (lift sourceRates zc) a)/4+200000000+1200000000*N*(γ+κ)^2) := by
  rw [global_local_generator hk γ w hdiag hsym (n,m) hmpos i
    (fun x => Real.exp ((1/1000000000000 : ℝ)*N*
      highEnergy (fun a => x a-pointOfState (lift sourceRates zc) a)))]
  exact high_coupled_generator_bound hk zc γ κ (m : ℝ) N (w i) i n
    hzc hstationary hN hm hγ hγmax hκ hκmax hz hw hs hy hnorm hx

end CompositionalMemory
