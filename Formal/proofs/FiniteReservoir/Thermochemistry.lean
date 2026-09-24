import proofs.FiniteReservoir.Reservoir
import proofs.CommonPhysicalRealization.ExporterThermochemistry
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace FiniteReservoir
noncomputable section
open RandomViability.Binding CommonPhysicalRealization

def countPotential (g C : ℝ) (n : ℕ) : ℝ :=
  n*g+Real.log (Nat.factorial n)-n*Real.log C

theorem count_potential_succ (g C : ℝ) (n : ℕ) :
    countPotential g C (n+1)-countPotential g C n=g+Real.log ((n:ℝ)+1)-Real.log C := by
  have hn : ((Nat.factorial n:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  simp only [countPotential,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [Real.log_mul hn1 hn]
  ring

def internalPotential (N : Counts) (V : ℝ) : ℝ :=
  countPotential 0 V (N 0)+countPotential 0 V (N 1)+
  countPotential (-Real.log 10) V (N 2)+countPotential (-Real.log 10) V (N 3)+
  countPotential (-Real.log 10) V (N 4)+countPotential (-2*Real.log 10) V (N 5)

def bathPotential (b : Bath) (RF RP : ℝ) : ℝ :=
  countPotential (Real.log 10+Real.log 8000000000) RF b.fuel+countPotential 0 RP b.waste

def totalPotential (s : State) (V RF RP : ℝ) : ℝ :=
  internalPotential s.1 V+bathPotential s.2 RF RP

def drivenBefore (u w x c1 c2 z f p : ℕ) : State := (![u,w,x+1,c1,c2,z],⟨f+1,p⟩)
def drivenAfter (u w x c1 c2 z f p : ℕ) : State := (![u+1,w+1,x,c1,c2,z],⟨f,p+1⟩)

theorem driven_neighbor_update (u w x c1 c2 z f p : ℕ) :
    next (drivenBefore u w x c1 c2 z f p) (.inr 0)=drivenAfter u w x c1 c2 z f p := by
  apply Prod.ext
  · funext i
    fin_cases i <;> norm_num [next,drivenBefore,drivenAfter,physicalNext,competitionBase,drivenBase,reactants,products]
  · simp [next,drivenBefore,drivenAfter,Bath.forward]

theorem driven_potential_increment (u w x c1 c2 z f p : ℕ) (V RF RP : ℝ) :
    totalPotential (drivenAfter u w x c1 c2 z f p) V RF RP-
      totalPotential (drivenBefore u w x c1 c2 z f p) V RF RP=
    -Real.log 8000000000+Real.log ((u:ℝ)+1)+Real.log ((w:ℝ)+1)-Real.log ((x:ℝ)+1)-Real.log V+
      Real.log ((p:ℝ)+1)-Real.log ((f:ℝ)+1)+Real.log RF-Real.log RP := by
  have hu := count_potential_succ 0 V u
  have hw := count_potential_succ 0 V w
  have hx := count_potential_succ (-Real.log 10) V x
  have hf := count_potential_succ (Real.log 10+Real.log 8000000000) RF f
  have hp := count_potential_succ 0 RP p
  change (countPotential 0 V (u+1)+countPotential 0 V (w+1)+
    countPotential (-Real.log 10) V x+countPotential (-Real.log 10) V c1+
    countPotential (-Real.log 10) V c2+countPotential (-2*Real.log 10) V z+
    (countPotential (Real.log 10+Real.log 8000000000) RF f+countPotential 0 RP (p+1)))-
    (countPotential 0 V u+countPotential 0 V w+
    countPotential (-Real.log 10) V (x+1)+countPotential (-Real.log 10) V c1+
    countPotential (-Real.log 10) V c2+countPotential (-2*Real.log 10) V z+
    (countPotential (Real.log 10+Real.log 8000000000) RF (f+1)+countPotential 0 RP p))=_
  linarith

/-- Neighboring propensities use post-jump waste p+1, including the initially empty-waste boundary. -/
theorem driven_neighbor_ratio (u w x c1 c2 z f p : ℕ) (V r d RF RP : ℝ)
    (hV : 0 < V) (hd : 0 < d) (hRF : 0 < RF) (hRP : 0 < RP) :
    physicalRate (drivenBefore u w x c1 c2 z f p).1 V r d ((f+1:ℕ)/RF) ((p:ℝ)/RP) (.inr 0) /
      physicalRate (drivenAfter u w x c1 c2 z f p).1 V r d ((f:ℝ)/RF) ((p+1:ℕ)/RP) (.inr 1)=
    8000000000*((f:ℝ)+1)/((p:ℝ)+1)*(RP/RF)*(V*((x:ℝ)+1)/(((u:ℝ)+1)*((w:ℝ)+1))) := by
  have h1 (n : ℕ) : (n:ℝ)+1 ≠ 0 := by positivity
  dsimp [physicalRate,drivenBefore,drivenAfter]
  push_cast
  field_simp [ne_of_gt hV,ne_of_gt hd,ne_of_gt hRF,ne_of_gt hRP,h1]

theorem driven_detailed_balance (u w x c1 c2 z f p : ℕ) (V r d RF RP : ℝ)
    (hV : 0 < V) (hd : 0 < d) (hRF : 0 < RF) (hRP : 0 < RP) :
    physicalRate (drivenBefore u w x c1 c2 z f p).1 V r d ((f+1:ℕ)/RF) ((p:ℝ)/RP) (.inr 0) /
      physicalRate (drivenAfter u w x c1 c2 z f p).1 V r d ((f:ℝ)/RF) ((p+1:ℕ)/RP) (.inr 1)=
    Real.exp (-(totalPotential (drivenAfter u w x c1 c2 z f p) V RF RP-
      totalPotential (drivenBefore u w x c1 c2 z f p) V RF RP)) := by
  rw [driven_neighbor_ratio u w x c1 c2 z f p V r d RF RP hV hd hRF hRP,driven_potential_increment]
  have h1 (n : ℕ) : (n:ℝ)+1 ≠ 0 := by positivity
  have hpos : 0 < 8000000000*((f:ℝ)+1)/((p:ℝ)+1)*(RP/RF)*(V*((x:ℝ)+1)/(((u:ℝ)+1)*((w:ℝ)+1))) := by positivity
  rw [← Real.exp_log hpos]
  congr 1
  simp [Real.log_mul,Real.log_div,ne_of_gt hV,ne_of_gt hRF,ne_of_gt hRP,h1]
  ring

/-- Chemical exchange potential telescopes exactly; it need not be a constant affinity times net service. -/
theorem bath_potential_telescope (b : ℕ → Bath) (RF RP : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,(bathPotential (b (k+1)) RF RP-bathPotential (b k) RF RP))=
      bathPotential (b n) RF RP-bathPotential (b 0) RF RP := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

end
end FiniteReservoir
