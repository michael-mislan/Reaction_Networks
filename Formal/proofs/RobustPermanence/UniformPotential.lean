import proofs.RobustPermanence.UniformGradient

namespace RobustPermanence
open CoreCouplingGlobal Set

/-- Potentials may have arbitrary additive primitive constants. Their oscillation
relative to a fixed physical point has a uniform bound independent of e. -/
theorem uniform_potential_center_bound (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (A B z H : ℝ)
    (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 2 ≤ B) (hB' : B ≤ 34)
    (hz : 0 ≤ z) (hz' : z ≤ 12) (hH : 0 ≤ H) (hH' : H ≤ 1536/7) :
    |responsePotential e p B z H (A+B-responseTotal e B) -
      responsePotential e p 2 0 0 (2-responseTotal e 2)| ≤ 1000000 := by
  let a := fun t : ℝ => t*A
  let b := fun t : ℝ => 2+t*(B-2)
  let c := fun t : ℝ => t*z
  let h := fun t : ℝ => t*H
  let r := fun t => a t+b t-responseTotal e (b t)
  let f := fun t => responsePotential e p (b t) (c t) (h t) (r t)
  have hbox : ∀ t ∈ Icc (0:ℝ) 1, a t ∈ Icc (0:ℝ) 34 ∧ b t ∈ Icc (2:ℝ) 34 ∧
      c t ∈ Icc (0:ℝ) 12 ∧ h t ∈ Icc (0:ℝ) (1536/7) := by
    intro t ht
    dsimp [a,b,c,h]
    constructor
    · constructor <;> nlinarith only [ht.1,ht.2,hA,hA']
    constructor
    · constructor <;> nlinarith only [ht.1,ht.2,hB,hB']
    constructor
    · constructor <;> nlinarith only [ht.1,ht.2,hz,hz']
    · constructor <;> nlinarith only [ht.1,ht.2,hH,hH']
  have hd : ∀ t ∈ Icc (0:ℝ) 1, ∃ v : ℝ, HasDerivAt f v t ∧ |v| ≤ 1000000 := by
    intro t ht
    obtain ⟨ha,hb,hc,hh⟩ := hbox t ht
    have da : HasDerivAt a A t := by simpa using (hasDerivAt_id t).mul_const A
    have db : HasDerivAt b (B-2) t := by simpa only [one_mul] using ((hasDerivAt_id t).mul_const (B-2)).const_add 2
    have dc : HasDerivAt c z t := by simpa using (hasDerivAt_id t).mul_const z
    have dh : HasDerivAt h H t := by simpa using (hasDerivAt_id t).mul_const H
    have dr := (da.add db).sub ((responseTotal_hasDerivAt e (b t) he he' hb.1 hb.2).comp t db)
    have hv := responsePotential_hasDerivAt e p he he' b c h r t _ _ _ _ hb hc hh db dc dh dr
    refine ⟨_,hv,?_⟩
    exact potential_direction_bound e (a t) (b t) (c t) (h t) A (B-2) z H he he'
      ha.1 ha.2 hb.1 hb.2 hc.1 hc.2 hh.1 hh.2
      (abs_le.2 ⟨by linarith,by linarith⟩) (abs_le.2 ⟨by linarith,by linarith⟩)
      (abs_le.2 ⟨by linarith,by linarith⟩) (abs_le.2 ⟨by linarith,by linarith⟩)
  have hfd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (deriv f t) t := by
    intro t ht
    obtain ⟨v,hv,_⟩ := hd t ht
    exact hv.differentiableAt.hasDerivAt
  obtain ⟨m,hm,hm',hmeq⟩ := bounded_secant f (deriv f) 0 1 (-1000000) 1000000
    (by norm_num)
    (fun t ht => hfd t (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht))
    (by
      intro t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
      obtain ⟨v,hv,hvbound⟩ := hd t ht'
      rw [hv.deriv]
      exact abs_le.1 hvbound)
  have hfin : |f 1-f 0| ≤ 1000000 := by
    rw [hmeq]
    simpa using abs_le.2 ⟨hm,hm'⟩
  simpa [f,r,a,b,c,h] using hfin

end RobustPermanence
