import proofs.CompositionalMemory.GenericCountDomain
import proofs.CompositionalMemory.GenericProductExit

namespace CompositionalMemory
open FiniteCopy

theorem general_count_departure_energy {k d : ℕ} (hk : 1 ≤ k) (N C : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ)
    (c radius b : ℝ) (hc : 0 < c) (hradius : 0 ≤ radius) (hb : b ≤ c*radius^2)
    (hcenter : ∀ i j, center i j ≤ (C:ℝ)-radius) (hE : ∀ i y j, c*(y j)^2 ≤ E i y)
    (s t : GeneralCountState k d) (hs : s ∈ generalProductDomain N C center E b)
    (hactive : s.2 < 2*(k*N)) (hstep : s.2 ≤ t.2 ∧ t.2 ≤ s.2+1)
    (hout : t ∉ generalProductDomain N C center E b) :
    ∃ i, b ≤ E i (fun j => generalConcentration t i j-center i j) := by
  classical
  have hmem := (mem_generalProductDomain hk N C hN center E c radius b hc hradius hb hcenter hE s).mp hs
  have hrange : k*N ≤ t.2 ∧ t.2 ≤ 2*(k*N) := by constructor <;> omega
  by_contra h
  push Not at h
  exact hout ((mem_generalProductDomain hk N C hN center E c radius b hc hradius hb hcenter hE t).mpr
    ⟨hrange.1,hrange.2,h⟩)

theorem general_count_product_exit {k d : ℕ} {R : Type*} [Fintype R]
    (hk : 1 ≤ k) (N C : ℕ) (hN : 1 ≤ N)
    (next : GeneralCountState k d → R → GeneralCountState k d)
    (rate : GeneralCountState k d → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (hstep : ∀ s r, s.2 ≤ (next s r).2 ∧ (next s r).2 ≤ s.2+1)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ)
    (c radius b α a ceiling : ℝ) (hc : 0 < c) (hradius : 0 ≤ radius)
    (hb : b ≤ c*radius^2) (hα : 0 ≤ α) (hceiling : 0 ≤ ceiling)
    (hcenter : ∀ i j, center i j ≤ (C:ℝ)-radius) (hE : ∀ i y j, c*(y j)^2 ≤ E i y)
    (hgen : ∀ s ∈ generalProductDomain N C center E b, s.2 < 2*(k*N) → ∀ i,
      reactionGenerator next rate (fun t => Real.exp (α*(N:ℝ)*
        E i (fun j => generalConcentration t i j-center i j))) s ≤ ceiling)
    (q t : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center E b)).total s ≤ q)
    (s : {s : GeneralCountState k d // s ∈ generalProductDomain N C center E b})
    (hstart : ∀ i, E i (fun j => generalConcentration s.val i j-center i j) ≤ a) :
    Real.exp (α*(N:ℝ)*b)*((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center E b)).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some s) ≤ (k:ℝ)*(Real.exp (α*(N:ℝ)*a)+(t:ℝ)*ceiling) := by
  apply retained_product_exit_bound next rate hrate (fun s => s.2 < 2*(k*N))
    (generalProductDomain N C center E b)
    (fun i s => E i (fun j => generalConcentration s i j-center i j))
    α N a b ceiling hα (Nat.cast_nonneg N) hceiling _ hgen q t hq hclock s hstart
  intro x hx ha r hout
  exact general_count_departure_energy hk N C hN center E c radius b hc hradius hb hcenter hE
    x (next x r) hx ha (hstep x r) hout

end CompositionalMemory
