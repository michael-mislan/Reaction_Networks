import proofs.HeritableCompositions.Selection

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem expect_add {α : Type*} [Fintype α] (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x+g x) = μ.expect f+μ.expect g := by
  simp only [FiniteLaw.expect,mul_add,Finset.sum_add_distrib]

noncomputable def pairLaw {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) : FiniteLaw (α × β) :=
  μ.bind (fun x => ν.bind (fun y => FiniteLaw.pure (x,y)))

theorem pair_failure_union {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw (Option α)) (ν : FiniteLaw β) (A : Set β) :
    (pairLaw μ ν).expect (FiniteKernel.eventIndicator {p | p.1=none ∨ p.2 ∈ A}) ≤
      μ.mass none+ν.expect (FiniteKernel.eventIndicator A) := by
  classical
  unfold pairLaw
  rw [FiniteLaw.expect_bind]
  simp_rw [FiniteLaw.expect_bind,FiniteLaw.expect_pure]
  have h (x : Option α) :
      ν.expect (fun y => FiniteKernel.eventIndicator {p : Option α × β | p.1=none ∨ p.2 ∈ A} (x,y)) ≤
      FiniteKernel.eventIndicator {none} x+ν.expect (FiniteKernel.eventIndicator A) := by
    calc
      _ ≤ ν.expect (fun y => FiniteKernel.eventIndicator {none} x+FiniteKernel.eventIndicator A y) := by
        apply ν.expect_mono
        intro y
        by_cases hx : x=none <;> by_cases hy : y ∈ A <;>
          simp [FiniteKernel.eventIndicator,hx,hy]
      _ = _ := by rw [expect_add,FiniteLaw.expect_const]
  have hh := μ.expect_mono _ _ h
  rw [expect_add,FiniteLaw.expect_const,expect_failure] at hh
  exact hh

noncomputable def lowBad (N : ℕ) (D : Finset Compartment) : Set (StoppedCompartment D) :=
  {x | x=none ∨ x ∈ divisionRecorded N D}

theorem low_bad_indicator (N : ℕ) (D : Finset Compartment) (x : StoppedCompartment D) :
    FiniteKernel.eventIndicator (lowBad N D) x =
      FiniteKernel.eventIndicator {none} x+FiniteKernel.eventIndicator (divisionRecorded N D) x := by
  classical
  cases x with
  | none => simp [lowBad,divisionRecorded,FiniteKernel.eventIndicator]
  | some c => simp [lowBad,FiniteKernel.eventIndicator]

noncomputable def reproductionSuccess (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (nL : BirthCount (lowCertificate zL γ hzL hsL hγ.le hmax) N)
    (nH : BirthCount (highCertificate zH γ hzH hsH hγ.le hmax) N) : ℝ :=
  1-(pairLaw (highGeneration zH γ hzH hsH hγ hmax N hN nH)
    (lowObservation zL γ hzL hsL hγ hmax N hN nL)).expect
    (FiniteKernel.eventIndicator {p | p.1=none ∨ p.2 ∈ lowBad N _})

theorem finite_time_differential_reproduction (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (nL : BirthCount (lowCertificate zL γ hzL hsL hγ.le hmax) N)
    (nH : BirthCount (highCertificate zH γ hzH hsH hγ.le hmax) N) :
    highTime γ < lowTime γ ∧
    1-(generationPrefactor γ+2+lowTime γ)*Real.exp (-(N : ℝ)*heredityExponent) ≤
      reproductionSuccess zL zH γ hzL hzH hsL hsH hγ hmax N hN nL nH := by
  refine ⟨selection_time_gap γ hγ,?_⟩
  have hH := high_faithful_reproduction zH γ hzH hsH hγ hmax N hN hlarge nH
  have hL := low_undivided_bound zL γ hzL hsL hγ hmax N hN nL
  have hu := pair_failure_union (highGeneration zH γ hzH hsH hγ hmax N hN nH)
    (lowObservation zL γ hzL hsL hγ hmax N hN nL) (lowBad N _)
  have he := funext (low_bad_indicator N
    (growthDomain N (lowCertificate zL γ hzL hsL hγ.le hmax).center
      (lowCertificate zL γ hzL hsL hγ.le hmax).energy outerEnergy))
  rw [he] at hu
  unfold reproductionSuccess
  linarith only [hH,hL,hu]

end HeritableCompositions
