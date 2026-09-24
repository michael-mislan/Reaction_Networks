import proofs.RAFSupportSelection.PortfolioBoundary
import proofs.RAFSupportSelection.PortfolioCoverage

namespace RAFSupportSelection
open RAF RAFQueryCompilation
variable {M R I T : Type*} [DecidableEq M] [Fintype M] [DecidableEq R] [Fintype R]
  [LinearOrder I] [DecidableEq T] [Fintype T]

/-- A uniform finite training workload: each event is a query and a retained reaction.
This objective concerns rescued mass; it is not a multiplicative residual-cost bound. -/
def rescueEvents (S : Finset R) (queries : T → Finset R) (p : I → R → Finset R)
    (i : I) : Finset (T × R) :=
  Finset.univ.filter (fun qr => qr.2 ∈ S \ selectedCone S (p i) (queries qr.1))

def trainedPortfolio (S : Finset R) (queries : T → Finset R) (p : I → R → Finset R)
    (H : Finset I) (hH : H.Nonempty) (b : ℕ) : Finset I :=
  greedyPortfolio (rescueEvents S queries p) H hH b

/-- A computable finite-pool portfolio is source-correct for every deletion, including
unseen queries, and has the finite greedy coverage guarantee on the training workload. -/
theorem source_portfolio_selection (Q : CRS M R) (cats : R → Finset M)
    (S : Finset R) (queries : T → Finset R) (p : I → R → Finset R)
    (ranks : I → R → ℕ) (H : Finset I) (hH : H.Nonempty)
    (hw : ∀ i ∈ H, RankedSupport Q cats S (p i) (ranks i))
    (b : ℕ) (hb : 1 ≤ b) :
    (trainedPortfolio S queries p H hH b).card ≤ b ∧
    (∀ K, portfolioQuery Q cats S K (trainedPortfolio S queries p H hH b) p =
      evaluate Q (fun x r => x ∈ cats r) (S \ K)) ∧
    (∀ B ⊆ H, B.card ≤ b →
      ((coverage (rescueEvents S queries p) B).card : ℝ) * (1 - (1 - 1/(b:ℝ))^b) ≤
        (coverage (rescueEvents S queries p) (trainedPortfolio S queries p H hH b)).card) := by
  refine ⟨greedyPortfolio_card _ H hH b, ?_, ?_⟩
  · intro K
    exact portfolioQuery_correct Q cats S K _ p ranks
      (fun i hi => hw i (greedyPortfolio_subset _ H hH b hi))
  · intro B hBH hB
    exact greedyPortfolio_guarantee _ H hH B hBH b hb hB b

end RAFSupportSelection
