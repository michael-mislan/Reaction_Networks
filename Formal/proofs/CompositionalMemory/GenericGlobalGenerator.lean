import proofs.CompositionalMemory.GenericResidentBinding
import proofs.CompositionalMemory.GenericExchangeCountBinding
import proofs.CompositionalMemory.GenericLocalMoments
import proofs.CompositionalMemory.GenericRetainedReactions

namespace CompositionalMemory

theorem general_global_generator_local {k d : ℕ} {R : Type*} [Fintype R]
    (hk : 1 ≤ k) (consume produce : Fin k → R → Fin d → ℕ)
    (coeff : Fin k → R → ℝ) (z : Fin d) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (s : GeneralCountState k d) (hm : 0 < s.2) (i : Fin k) (W : (Fin d → ℝ) → ℝ) :
    let v := (s.2:ℝ)/k
    let u := generalConcentration s i
    let b := fun a => if a=z then (1:ℝ) else 0
    let ν := fun r a => (produce i r a:ℝ)-(consume i r a:ℝ)
    let a := fun r => countReactionDensity (coeff i r) v (consume i r) (s.1 i)
    reactionGenerator (generalGlobalNext consume produce z)
      (generalGlobalRate consume coeff z γ w) (fun t => W (generalConcentration t i)) s =
      ∑ c, localChannelRate a γ v (fun j => generalConcentration s j z) (w i) i c*
        (W (u+localChannelJump ν u b v i c)-W u) := by
  classical
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hm0 : (s.2:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hvol : (k:ℝ)*((s.2:ℝ)/k)=(s.2:ℝ) := by field_simp
  have hcount (j) : ((s.2:ℝ)/k)*generalConcentration s j z=(s.1 j z:ℝ) := by
    unfold generalConcentration
    field_simp
  have hmemrate (j) : γ*((s.2:ℝ)/k)*generalConcentration s j z=γ*(s.1 j z:ℝ) := by
    rw [mul_assoc,hcount]
  have hexrate (j l) : ((s.2:ℝ)/k)*(w i j*generalConcentration s l z)=w i j*(s.1 l z:ℝ) := by
    calc
      _ = w i j*(((s.2:ℝ)/k)*generalConcentration s l z) := by ring
      _ = _ := by rw [hcount]
  have hresjump (r) : generalConcentration s i+(1/((s.2:ℝ)/k)) •
      (fun a => (produce i r a:ℝ)-(consume i r a:ℝ)) =
      (fun a => generalConcentration s i a+((produce i r a:ℝ)-(consume i r a:ℝ))/((s.2:ℝ)/k)) := by
    funext a
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  dsimp only
  simp only [reactionGenerator,generalGlobalNext,generalGlobalRate,localChannelRate,localChannelJump,
    Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,hvol]
  simp_rw [general_resident_observable_local,general_membrane_observable_local hk z s hm,
    general_exchange_observable_local z s w hdiag]
  simp_rw [hmemrate,hexrate,hresjump]
  simp [Finset.sum_ite_irrel,Finset.sum_add_distrib,hsym]
  ring

end CompositionalMemory
