import proofs.OverlappingSiphonInvasion.NormalizedCompact

noncomputable section
open Set
namespace OverlappingSiphonInvasion

theorem physical_closure_eq (ru rv rj R : ℝ) (f g : LiftState → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ x : State, (∀ i, 0 < x i) → total x ≤ R →
      f (normalizedEmbedding ru rv rj x) = g (normalizedEmbedding ru rv rj x))
    (z : LiftState) (hz : z ∈ physicalLiftClosure ru rv rj R) : f z = g z := by
  apply closure_minimal (t := {z | f z = g z}) ?_ (isClosed_eq hf hg) hz
  rintro _ ⟨x,⟨hx,hN⟩,rfl⟩
  exact heq x hx hN

theorem physical_closure_le (ru rv rj R : ℝ) (f g : LiftState → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hle : ∀ x : State, (∀ i, 0 < x i) → total x ≤ R →
      f (normalizedEmbedding ru rv rj x) ≤ g (normalizedEmbedding ru rv rj x))
    (z : LiftState) (hz : z ∈ physicalLiftClosure ru rv rj R) : f z ≤ g z := by
  apply closure_minimal (t := {z | f z ≤ g z}) ?_ (isClosed_le hf hg) hz
  rintro _ ⟨x,⟨hx,hN⟩,rfl⟩
  exact hle x hx hN

theorem closure_direction_bounds (ru rv rj R : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (z : LiftState)
    (hz : z ∈ physicalLiftClosure ru rv rj R) :
    (∀ i, 0 ≤ z.2 i ∧ z.2 i ≤ 1) ∧ z.2 2+z.2 3 ≤ 1 := by
  constructor
  · intro i
    constructor
    · exact physical_closure_le ru rv rj R (fun _ => 0) (fun z => z.2 i)
        (by fun_prop) (by fun_prop)
        (fun x hx _ => (normalized_direction_bounds ru rv rj x hru hrv hrj hx i).1) z hz
    · exact physical_closure_le ru rv rj R (fun z => z.2 i) (fun _ => 1)
        (by fun_prop) (by fun_prop)
        (fun x hx _ => (normalized_direction_bounds ru rv rj x hru hrv hrj hx i).2) z hz
  · apply physical_closure_le ru rv rj R (fun z => z.2 2+z.2 3) (fun _ => 1)
      (by fun_prop) (by fun_prop) ?_ z hz
    intro x hx _
    have hJ := (positive_masses ru rv rj x hru hrv hrj hx).2.2
    change x 1/massJ rj x+x 2/massJ rj x ≤ 1
    rw [← add_div,div_le_one hJ]
    dsimp [massJ]
    nlinarith [mul_pos hrj (hx 3)]

theorem closure_mass_identities (p : Rates) (ru rv rj R : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (z : LiftState)
    (hz : z ∈ physicalLiftClosure ru rv rj R) :
    normalHU p ru z.1 (z.2 0)*massU ru z.1 = field p z.1 1+ru*field p z.1 3 ∧
    normalHV p rv z.1 (z.2 1)*massV rv z.1 = field p z.1 2+rv*field p z.1 3 ∧
    normalHJ p rj z.1 (z.2 2) (z.2 3)*massJ rj z.1 =
      field p z.1 1+field p z.1 2+rj*field p z.1 3 := by
  constructor
  · apply physical_closure_eq ru rv rj R _ _
      (by dsimp [normalHU,privateA,sharedC,massU]; fun_prop)
      (by dsimp [field]; fun_prop) ?_ z hz
    intro x hx _
    exact normalHU_physical p ru x hru.ne'
      (positive_masses ru rv rj x hru hrv hrj hx).1.ne'
  · constructor
    · apply physical_closure_eq ru rv rj R _ _
        (by dsimp [normalHV,privateB,sharedC,massV]; fun_prop)
        (by dsimp [field]; fun_prop) ?_ z hz
      intro x hx _
      exact normalHV_physical p rv x hrv.ne'
        (positive_masses ru rv rj x hru hrv hrj hx).2.1.ne'
    · apply physical_closure_eq ru rv rj R _ _
        (by dsimp [normalHJ,privateA,privateB,sharedC,massJ]; fun_prop)
        (by dsimp [field]; fun_prop) ?_ z hz
      intro x hx _
      exact normalHJ_physical p rj x hrj.ne'
        (positive_masses ru rv rj x hru hrv hrj hx).2.2.ne'

end OverlappingSiphonInvasion
