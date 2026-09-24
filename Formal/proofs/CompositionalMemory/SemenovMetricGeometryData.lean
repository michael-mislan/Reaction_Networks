import proofs.CompositionalMemory.SemenovMetricPolynomials

namespace CompositionalMemory.Semenov

def coefficientNorm {N : ℕ} (c : Fin N → ℚ) : ℚ := ∑ k,|c k|
def coefficientUpper {N : ℕ} (c : Fin (N+1) → ℚ) : ℚ := c 0+∑ k : Fin N,|c k.succ|
def coefficientLower {N : ℕ} (c : Fin (N+1) → ℚ) : ℚ := c 0-∑ k : Fin N,|c k.succ|

def metricJumpCoefficients (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (r : Fin 11)
    (i : Fin 8) (k : Fin 17) : ℚ := ∑ j,(stoich r j : ℚ)*pc i j k

def jumpEnergyCoefficients (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (r : Fin 11) (k : Fin 17) : ℚ :=
  ∑ i,(stoich r i : ℚ)*metricJumpCoefficients pc r i k

def coordinateUpper (zc : Fin 8 → Fin 17 → ℚ) (radius : ℚ) (j : Fin 8) : ℚ :=
  max 0 (coefficientUpper (zc j))+radius

def propensityUpper (zc : Fin 8 → Fin 17 → ℚ) (radius : ℚ) (r : Fin 11) : ℚ :=
  if r.val=7 then kineticRational r*coordinateUpper zc radius (reactantA r) else
    kineticRational r*coordinateUpper zc radius (reactantA r)*coordinateUpper zc radius (reactantB r)

def noiseUpper (zc : Fin 8 → Fin 17 → ℚ) (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (radius : ℚ) : ℚ :=
  (∑ r,propensityUpper zc radius r*coefficientUpper (jumpEnergyCoefficients pc r))+
    ∑ j,(1/500)*(feedRational j+coordinateUpper zc radius j)*coefficientUpper (pc j j)

def whiteningNormSquared (A : Fin 8 → Fin 8 → ℚ) : ℚ := ∑ i,∑ j,(A i j)^2

def curvatureUpper (nr : Fin 11 → ℚ) : ℚ := ∑ r,if r.val=7 then 0 else kineticRational r*nr r

/-- Finite rational checks whose analytic interpretation is independent of
the data exporter. All source coefficients are the fixed nominal table. -/
def MetricGeometryChecks (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ) : Prop :=
  (0 < eta ∧ 0 < radius ∧ 0 < margin ∧ 0 < whiteningNormSquared A) ∧
  (∀ i j,i < j → A i j=0) ∧ (∀ i,0 < A i i) ∧
  (∀ i,margin ≤ coefficientLower (wc i i)-∑ j,if j=i then 0 else coefficientNorm (wc i j)) ∧
  (∀ r,0 ≤ nr r ∧ (∑ i,(coefficientNorm (metricJumpCoefficients pc r i))^2) ≤ (nr r)^2) ∧
  (curvatureUpper nr*radius ≤ 12/25) ∧
  (eta*whiteningNormSquared A ≤ margin*radius^2) ∧
  (∀ i,(∑ j,coefficientNorm (pc i j)) ≤ L) ∧
  (∀ r,0 ≤ coefficientUpper (jumpEnergyCoefficients pc r) ∧ coefficientUpper (jumpEnergyCoefficients pc r) ≤ H) ∧
  (∀ j,0 ≤ coefficientUpper (pc j j) ∧ coefficientUpper (pc j j) ≤ H) ∧
  noiseUpper zc pc radius ≤ Q

instance metricGeometryChecks_decidable (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ) :
    Decidable (MetricGeometryChecks zc pc wc A nr eta radius margin L Q H) := by
  unfold MetricGeometryChecks
  infer_instance

end CompositionalMemory.Semenov
