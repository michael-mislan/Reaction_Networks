import proofs.CoreCouplingCAC.SourceAdapter

namespace DisguisedToricAssemblies
open CoreCouplingCAC

/-- Source complex order: zero, A, B+z, z, H, 2z, B, 2A. -/
def complexes : Fin 8 → Fin 4 → ℝ :=
  ![![0,0,0,0], ![1,0,0,0], ![0,1,1,0], ![0,0,1,0],
    ![0,0,0,1], ![0,0,2,0], ![0,1,0,0], ![2,0,0,0]]

noncomputable def coefficient (p : Rates) : Fin 8 → Fin 4 → ℝ :=
  ![![p.a,p.b,0,0], ![-2,1,1,0], ![1,-1,-1,0], ![0,0,-p.u,p.u],
    ![0,0,3,-(2+p.d)], ![0,0,-2*p.v,p.v], ![2*p.e,-(1+p.e),0,0],
    ![-2*p.e,p.e,0,0]]

noncomputable def activity (x : State) : Fin 8 → ℝ :=
  ![1,x.A,x.B*x.z,x.z,x.H,x.z^2,x.B,x.A^2]

noncomputable def fluxTable (a b w K jp jm eB eAA B U V H t : ℝ) :
    Fin 8 → Fin 8 → ℝ :=
  ![![0,a,0,0,0,0,b,0],
    ![w+jm,0,w,K,0,0,K,jm],
    ![0,w,0,0,0,0,0,0],
    ![t,0,0,0,U,t,0,0],
    ![K-t,0,0,3*H-2*V+2*t,0,V-t,0,0],
    ![0,0,0,0,V,0,0,0],
    ![B-jp,2*jp,0,0,0,0,0,eB-jp],
    ![0,0,0,0,0,0,eAA,0]]

noncomputable def flux (p : Rates) (x : State) : Fin 8 → Fin 8 → ℝ :=
  fluxTable p.a p.b (x.B*x.z) (x.A-x.B*x.z)
    (max (p.e*(x.B-x.A^2)) 0) (max (-(p.e*(x.B-x.A^2))) 0)
    (p.e*x.B) (p.e*x.A^2) x.B (p.u*x.z) (p.v*x.z^2) x.H
    (max 0 (p.v*x.z^2-3/2*x.H))

def FluxCertificate (p : Rates) (x : State) (q : Fin 8 → Fin 8 → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j) ∧ (∀ i, q i i = 0) ∧
  (∀ i, ∑ j, q i j = ∑ j, q j i) ∧
  (∀ i k, ∑ j, q i j * (complexes j k-complexes i k) =
    activity x i * coefficient p i k)

theorem coefficient_source (p : Rates) (x : State) (k : Fin 4) :
    ∑ i, activity x i * coefficient p i k = sourceDerivative p x k := by
  rw [literal_source_adapter]
  fin_cases k <;>
    norm_num [activity, coefficient, Fin.sum_univ_succ, fA, fB, fZ, fH] <;> ring

theorem flux_table_balanced (a b w K jp jm eB eAA B U V H t : ℝ)
    (ha : a = w+2*K-2*jp+2*jm) (hb : b = B-K+jp-jm)
    (he : eB-eAA = jp-jm) (hk : K = U+2*V-3*H) :
    ∀ i, ∑ j, fluxTable a b w K jp jm eB eAA B U V H t i j =
      ∑ j, fluxTable a b w K jp jm eB eAA B U V H t j i := by
  intro i
  fin_cases i <;> norm_num [fluxTable, Fin.sum_univ_succ] <;> linarith

theorem flux_table_drift (a b w K jp jm eB eAA B U V H t D : ℝ)
    (hk : K = U+2*V-3*H)
    (hh : U+V = D) :
    ∀ i k, ∑ j, fluxTable a b w K jp jm eB eAA B U V H t i j *
      (complexes j k-complexes i k) =
      (![![a,b,0,0], ![-2*(w+K),w+K,w+K,0], ![w,-w,-w,0],
        ![0,0,-U,U], ![0,0,3*H,-D], ![0,0,-2*V,V],
        ![2*eB,-B-eB,0,0], ![-2*eAA,eAA,0,0]] : Fin 8 → Fin 4 → ℝ) i k := by
  intro i k
  fin_cases i <;> fin_cases k <;>
    norm_num [fluxTable, complexes, Fin.sum_univ_succ] <;> linarith

theorem flux_table_nonneg (a b w K jp jm eB eAA B U V H t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) (hK : 0 ≤ K)
    (hp : 0 ≤ jp) (hm : 0 ≤ jm) (he : jp ≤ eB) (heAA : 0 ≤ eAA)
    (hB : jp ≤ B) (hU : 0 ≤ U) (ht : 0 ≤ t) (htV : t ≤ V)
    (htK : t ≤ K) (hH : 0 ≤ 3*H-2*V+2*t) :
    ∀ i j, 0 ≤ fluxTable a b w K jp jm eB eAA B U V H t i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [fluxTable] <;> linarith

theorem flux_nonneg (p : Rates) (x : State) (hp : p.Positive) (hx : x.Positive)
    (hs : Stationary p x) (hK : 0 ≤ x.A-x.B*x.z)
    (hJ : p.e*(x.B-x.A^2) ≤ x.B) : ∀ i j, 0 ≤ flux p x i j := by
  have he := hp.2.2.2.2.1.le
  have hH := hx.2.2.2.le
  have hV : 0 ≤ p.v*x.z^2 := mul_nonneg hp.2.2.2.1.le (sq_nonneg _)
  have hU : 0 ≤ p.u*x.z := mul_nonneg hp.2.2.1.le hx.2.2.1.le
  have hZ := hs.2.2.1
  have hh := hs.2.2.2
  dsimp [fZ] at hZ
  dsimp [fH] at hh
  have hdh : 0 ≤ p.d*x.H := mul_nonneg hp.2.2.2.2.2.le hH
  have htV : max 0 (p.v*x.z^2-3/2*x.H) ≤ p.v*x.z^2 := by
    apply max_le <;> linarith
  have htK : max 0 (p.v*x.z^2-3/2*x.H) ≤ x.A-x.B*x.z := by
    apply max_le
    · exact hK
    · nlinarith
  have htH : 0 ≤ 3*x.H-2*(p.v*x.z^2)+2*max 0 (p.v*x.z^2-3/2*x.H) := by
    linarith [le_max_right (0 : ℝ) (p.v*x.z^2-3/2*x.H)]
  unfold flux
  apply flux_table_nonneg
  · exact hp.1.le
  · exact hp.2.1.le
  · exact mul_nonneg hx.2.1.le hx.2.2.1.le
  · exact hK
  · exact le_max_right _ _
  · exact le_max_right _ _
  · apply max_le
    · nlinarith [mul_nonneg he (sq_nonneg x.A)]
    · exact mul_nonneg he hx.2.1.le
  · exact mul_nonneg he (sq_nonneg _)
  · exact max_le hJ hx.2.1.le
  · exact hU
  · exact le_max_left _ _
  · exact htV
  · exact htK
  · exact htH

end DisguisedToricAssemblies
