import proofs.RobustPermanence.ConsumerFlow

namespace RobustPermanence
open CoreCouplingGlobal CoreCouplingCAC

/-- One independent rate per directed literal reaction. -/
structure AssemblyRates where
  a : ℝ
  b : ℝ
  p : ℝ
  q : ℝ
  alpha : ℝ
  beta : ℝ
  ef : ℝ
  er : ℝ
  u : ℝ
  v : ℝ
  h1 : ℝ
  h2 : ℝ
  d : ℝ
  k : ℝ
  mu : ℝ
  rho : ℝ

noncomputable def rateRadius : ℝ := 1/1000000000000000000

structure RateNeighborhood (e : ℝ) (r : AssemblyRates) : Prop where
  a : |r.a-6| ≤ rateRadius
  b : |r.b-27| ≤ rateRadius
  p : |r.p-1| ≤ rateRadius
  q : |r.q-1| ≤ rateRadius
  alpha : |r.alpha-1| ≤ rateRadius
  beta : |r.beta-1| ≤ rateRadius
  ef : |r.ef-e| ≤ rateRadius
  er : |r.er-e| ≤ rateRadius
  u : |r.u-16| ≤ rateRadius
  v : |r.v-2| ≤ rateRadius
  h1 : |r.h1-1| ≤ rateRadius
  h2 : |r.h2-1| ≤ rateRadius
  d : |r.d-1/10000| ≤ rateRadius
  k : |r.k-1| ≤ rateRadius
  mu : |r.mu-1/2| ≤ rateRadius
  rho : |r.rho-1| ≤ rateRadius

noncomputable def rateA (r : AssemblyRates) (A B z : ℝ) : ℝ :=
  r.a-(r.p+r.alpha)*A+r.q*B*z+2*r.ef*B-2*r.er*A^2
noncomputable def rateB (r : AssemblyRates) (A B z : ℝ) : ℝ :=
  r.b+r.p*A-(r.q*z+r.beta+r.ef)*B+r.er*A^2
noncomputable def rateZ (r : AssemblyRates) (A B z H X : ℝ) : ℝ :=
  r.p*A-r.q*B*z-r.u*z+(r.h1+2*r.h2)*H-2*r.v*z^2-r.k*z*X
noncomputable def rateH (r : AssemblyRates) (z H : ℝ) : ℝ :=
  r.u*z+r.v*z^2-(r.h1+r.h2+r.d)*H
noncomputable def rateX (r : AssemblyRates) (z X : ℝ) : ℝ :=
  X*(r.k*z-r.mu-r.rho*X)

/-- The equations retain each monomial from the 16 literal channels:
0→A, 0→B, A→B+z, B+z→A, A→0, B→0, B→2A, 2A→B,
z→H, 2z→H, H→z, H→2z, H→0, X+z→2X, X→0, 2X→X. -/
noncomputable def rateField (r : AssemblyRates) (y : ConsumerVector) : ConsumerVector :=
  ![rateA r (y 0) (y 1) (y 2),rateB r (y 0) (y 1) (y 2),
    rateZ r (y 0) (y 1) (y 2) (y 3) (y 4),rateH r (y 2) (y 3),rateX r (y 2) (y 4)]

noncomputable def referenceRates (e : ℝ) : AssemblyRates :=
  ⟨6,27,1,1,1,1,e,e,16,2,1,1,1/10000,1,1/2,1⟩

theorem reference_field_eq (e : ℝ) : rateField (referenceRates e) = consumerField e := by
  funext y i
  fin_cases i <;> dsimp [rateField,referenceRates,consumerField,rateA,rateB,rateZ,rateH,rateX,
    fA,fB,fZ,fH,flagshipRates] <;> ring

theorem rate_total_identity (r : AssemblyRates) (A B z : ℝ) :
    rateA r A B z+rateB r A B z = r.a+r.b-r.alpha*A-(r.beta-r.ef)*B-r.er*A^2 := by
  dsimp [rateA,rateB]
  ring

theorem rate_weighted_identity (r : AssemblyRates) (A B z H X : ℝ) :
    rateZ r A B z H X+(7/4:ℝ)*rateH r z H =
      r.p*A-r.q*B*z+(3/4)*r.u*z-(1/4)*r.v*z^2+
      ((-3*r.h1+r.h2-7*r.d)/4)*H-r.k*z*X := by
  dsimp [rateZ,rateH]
  ring

end RobustPermanence
