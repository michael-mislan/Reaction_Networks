import proofs.HeritableCompositions.StructuralTransfer
import proofs.HeritableCompositions.ReproductionComparison

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

/-- Complete quantitative source endpoint. All stochastic estimates are derived;
the two source centers and nonempty, distinguishable birth sets are supplied. -/
structure SourceConclusion (γ : ℝ) (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) where
  zL : ℝ
  zH : ℝ
  hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000)
  hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)
  hsL : Stationary sourceRates (lift sourceRates zL)
  hsH : Stationary sourceRates (lift sourceRates zH)
  low_heredity : HeredityConclusion (lowCertificate zL γ hzL hsL hγ.le hmax) hγ hmax
  high_heredity : HeredityConclusion (highCertificate zH γ hzH hsH hγ.le hmax) hγ hmax
  low_nonempty : ∀ N, copyThreshold γ ≤ N → Nonempty (BirthCount (lowCertificate zL γ hzL hsL hγ.le hmax) N)
  high_nonempty : ∀ N, copyThreshold γ ≤ N → Nonempty (BirthCount (highCertificate zH γ hzH hsH hγ.le hmax) N)
  low_readout : ∀ N, 1 ≤ N → ∀ n : BirthCount (lowCertificate zL γ hzL hsL hγ.le hmax) N,
    compositionalReadout n.val < 0
  high_readout : ∀ N, 1 ≤ N → ∀ n : BirthCount (highCertificate zH γ hzH hsH hγ.le hmax) N,
    0 < compositionalReadout n.val
  reproduction : ∀ (N : ℕ) (hN : copyThreshold γ ≤ N)
    (nL : BirthCount (lowCertificate zL γ hzL hsL hγ.le hmax) N)
    (nH : BirthCount (highCertificate zH γ hzH hsH hγ.le hmax) N),
    highTime γ < lowTime γ ∧
    1-(generationPrefactor γ+2+lowTime γ)*Real.exp (-(N : ℝ)*heredityExponent) ≤
      reproductionSuccess zL zH γ hzL hzH hsL hsH hγ hmax N (copyThreshold_positive γ N hN) nL nH

theorem heritable_compositional_states (γ : ℝ) (hγ : 0 < γ)
    (hmax : γ ≤ 1/100000000000) : Nonempty (SourceConclusion γ hγ hmax) := by
  obtain ⟨zL,hzL,hsL⟩ := low_source_root
  obtain ⟨zH,hzH,hsH⟩ := high_source_root
  have hsize (N : ℕ) (hN : copyThreshold γ ≤ N) : 1000000000000 ≤ N := by
    have h := copyThreshold_large γ N hN
    have h' : (1000000000000 : ℝ) ≤ N := by linarith only [h]
    exact_mod_cast h'
  exact ⟨{
    zL := zL
    zH := zH
    hzL := hzL
    hzH := hzH
    hsL := hsL
    hsH := hsH
    low_heredity := structural_transfer _ hγ hmax
    high_heredity := structural_transfer _ hγ hmax
    low_nonempty := fun N hN => low_birth_nonempty zL γ hzL hsL hγ.le hmax N (hsize N hN)
    high_nonempty := fun N hN => high_birth_nonempty zH γ hzH hsH hγ.le hmax N (hsize N hN)
    low_readout := low_birth_readout zL γ hzL hsL hγ.le hmax
    high_readout := high_birth_readout zH γ hzH hsH hγ.le hmax
    reproduction := fun N hN nL nH => finite_time_differential_reproduction zL zH γ hzL hzH hsL hsH
      hγ hmax N (copyThreshold_positive γ N hN) (copyThreshold_large γ N hN) nL nH }⟩

end HeritableCompositions
