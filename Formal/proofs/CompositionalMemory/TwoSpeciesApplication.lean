import proofs.CompositionalMemory.GenericUniformWords
import proofs.CompositionalMemory.TwoSpeciesQuality

namespace CompositionalMemory
open FiniteCopy

noncomputable def twoRadius : ℝ := 1/10000
noncomputable def twoOuterEnergy : ℝ := 1/100000000
noncomputable def twoBirthEnergy : ℝ := 1/1000000000
noncomputable def twoParentEnergy : ℝ := 1/10000000000
noncomputable def twoRecoverEnergy : ℝ := 1/100000000000
noncomputable def twoRho : ℝ := 1/100000000000000000

def twoWordCenter {k : ℕ} (σ : Fin k → Bool) (i : Fin k) : TwoPoint := twoCenter (σ i)
def twoWordQ {k : ℕ} (σ : Fin k → Bool) (i : Fin k) := twoQ (σ i)

theorem two_word_center_nonneg {k : ℕ} (σ : Fin k → Bool) (i : Fin k) (a : Fin 2) :
    0 ≤ twoWordCenter σ i a := by
  fin_cases a <;> cases hs : σ i <;> norm_num [twoWordCenter,twoCenter,hs]

theorem two_word_center_cap {k : ℕ} (σ : Fin k → Bool) (i : Fin k) (a : Fin 2) :
    twoWordCenter σ i a ≤ (56:ℝ)-twoRadius := by
  fin_cases a <;> cases hs : σ i <;> norm_num [twoWordCenter,twoCenter,twoRadius,hs]

theorem two_word_coercivity {k : ℕ} (σ : Fin k → Bool) (i : Fin k) (y : TwoPoint) :
    1*‖y‖^2 ≤ twoWordQ σ i y y := by
  simpa only [one_mul] using twoQ_coercive (σ i) y

/-- The five-reaction two-species mechanism instantiates the same general
all-word theorem; all stochastic and geometry hypotheses are discharged. -/
theorem two_species_all_words :
    ∃ coupling N0 γ cgen : ℝ, ∃ (t₀ t₁ : NNReal) (hγ : 0 < γ),
      0 < coupling ∧ γ ≤ coupling ∧ 1 ≤ N0 ∧ 0 < cgen ∧
      0 < (t₀:ℝ) ∧ 0 < (t₁:ℝ) ∧
    ∀ {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (_ : N0 ≤ (N:ℝ))
      (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j)
      (_hdiag : ∀ j, w j j=0) (_hsym : ∀ j l, w j l=w l j)
      (κ : ℝ) (_hκ : 0 ≤ κ) (_hκmax : κ ≤ coupling) (_hrow : ∀ i, (∑ j, w i j) ≤ κ),
    (∃ initial : (Fin k → Bool) → Fin k → Fin 2 → ℕ,
      (∀ σ, initial σ ∈ generalBirthCounts N 56 (twoWordCenter σ) (fun i y => twoWordQ σ i y y) twoBirthEnergy) ∧
      (∀ σ, generalWordReadout N (fun _ => 0) (fun _ => 2) (initial σ)=σ) ∧ Function.Injective initial) ∧
    ∀ σ : Fin k → Bool,
    let center := twoWordCenter σ
    let Q := twoWordQ σ
    let next := generalGlobalNext (fun _ => twoConsume) (fun _ => twoProduce) 0
    let rate := generalGlobalRate (fun _ => twoConsume) (fun _ => twoCoeff) 0 γ w
    let hrate := general_global_rate_nonneg (fun _ => twoConsume) (fun _ => twoCoeff) 0 γ w (fun _ => two_coeff_nonneg) hγ.le hw
    let domain₀ := generalProductDomain N 56 center (fun i y => Q i y y) twoOuterEnergy
    let domain₁ := generalProductDomain N 56 center (fun i y => Q i y y) twoParentEnergy
    ∃ (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
      (hclock₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₀).total s ≤ q₀)
      (hclock₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₁).total s ≤ q₁),
    let K := generalGenerationLaw hk next rate hrate N 56 hN Q center 1 twoRadius twoBirthEnergy twoOuterEnergy twoParentEnergy twoRecoverEnergy
      (by norm_num) (by norm_num [twoRadius]) (by norm_num [twoBirthEnergy,twoOuterEnergy]) (by norm_num [twoOuterEnergy,twoRadius]) (by norm_num [twoRecoverEnergy,twoParentEnergy]) (two_word_center_cap σ) (two_word_coercivity σ) q₀ t₀ q₁ t₁ hq₀ hq₁ hclock₀ hclock₁
    let ε := (k:ℝ)*(7+2*(2:ℝ)+(200*twoRho/2)*((t₀:ℝ)/(twoOuterEnergy-twoBirthEnergy)+(t₁:ℝ)/(twoParentEnergy-twoRecoverEnergy)))*Real.exp (-cgen*N)
    (∀ n, (K n).mass none ≤ ε) ∧
    ∀ (G : ℕ) n, 1-(G:ℝ)*ε ≤ wordLineageSuccess K G n := by
  classical
  obtain ⟨coupling,N0,γ,cgen,t₀,t₁,hγ,hcoupling,hγc,hN0,hcgen,ht₀,ht₁,harch⟩ :=
    general_uniform_word_architecture 2 56 (by norm_num)
      1 twoRadius twoOuterEnergy twoRecoverEnergy twoParentEnergy twoBirthEnergy
      200 twoRho 50000 20000 100000 200000 55 4 50000 160000 (1/10000) (1/2)
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
  refine ⟨coupling,N0,γ,cgen,t₀,t₁,hγ,hcoupling,hγc,hN0,hcgen,ht₀,ht₁,?_⟩
  intro k hk N hN hlarge w hw hdiag hsym κ hκ hκmax hrow
  apply harch hk N hN hlarge (fun _ => twoConsume) (fun _ => twoProduce) (fun _ => twoCoeff) 0 w
    (fun _ => two_coeff_nonneg) hw hdiag hsym twoWordCenter twoWordQ κ hκ hκmax
    two_word_center_nonneg two_word_center_cap (fun σ i => twoQ_symm (σ i)) (fun σ i => twoQ_operator (σ i))
    (fun _ => two_activity_bound)
    (fun _ => by simpa only [show (55:ℝ)+1=56 by norm_num,twoStoich] using two_propensity_bias_bound)
    hrow ?_ ?_ two_word_coercivity ?_ (fun _ => 0) (fun _ => 2) ?_
  · intro σ s hs i
    have he := (Finset.mem_filter.mp hs).2 i
    exact two_module_quality (σ i) (generalConcentration s i) he
  · intro σ s hs i
    have he := (Finset.mem_filter.mp hs).2 i
    have hh := two_well_growth_bounds (σ i) (generalConcentration s i) he
    exact ⟨(by norm_num : (0:ℝ) ≤ 1/2).trans hh.1,hh.2⟩
  · intro σ s hs i
    exact (two_well_growth_bounds (σ i) (generalConcentration s i) ((Finset.mem_filter.mp hs).2 i)).1
  · intro σ i
    cases hs : σ i <;> norm_num [twoWordCenter,twoCenter,twoRadius,hs]

theorem two_birth_relative_readout {k : ℕ} (N : ℕ) (hN : 0 < N) (σ : Fin k → Bool)
    (n : GeneralBirthCount N 56 (twoWordCenter σ) (fun i y => twoWordQ σ i y y) twoBirthEnergy)
    (i : Fin k) :
    if σ i then 0 < (n.val i 1:ℝ)-12*(n.val i 0:ℝ)
    else (n.val i 1:ℝ)-12*(n.val i 0:ℝ) < 0 := by
  classical
  let u : TwoPoint := fun a => (n.val i a:ℝ)/(N:ℝ)
  have he : twoQ (σ i) (u-twoCenter (σ i)) (u-twoCenter (σ i)) < twoBirthEnergy :=
    (Finset.mem_filter.mp n.property).2 i
  have hh := two_well_signed_readout (σ i) u (he.trans (by norm_num [twoBirthEnergy]))
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  dsimp [u] at hh
  cases hs : σ i <;> simp only [hs,Bool.false_eq_true,if_false,if_true] at hh ⊢
  · have hm := mul_lt_mul_of_pos_right hh hNr
    field_simp at hm
    nlinarith only [hm]
  · have hm := mul_lt_mul_of_pos_right hh hNr
    field_simp at hm
    nlinarith only [hm]

/-- The concrete two-species application supports every positive rate in a common interval. -/
theorem two_species_growth_interval :
    ∃ coupling N0 γ₀ cgen : ℝ, ∃ t₀ : NNReal,
      0 < coupling ∧ 0 < γ₀ ∧ γ₀ ≤ coupling ∧ 1 ≤ N0 ∧ 0 < cgen ∧
      0 < (t₀:ℝ) ∧ ∀ (γ : ℝ) (hγ : 0 < γ), γ ≤ γ₀ →
    ∃ t₁ : NNReal, 0 < (t₁:ℝ) ∧
    ∀ {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (_ : N0 ≤ (N:ℝ))
      (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j)
      (_hdiag : ∀ j, w j j=0) (_hsym : ∀ j l, w j l=w l j)
      (κ : ℝ) (_hκ : 0 ≤ κ) (_hκmax : κ ≤ coupling) (_hrow : ∀ i, (∑ j, w i j) ≤ κ),
    (∃ initial : (Fin k → Bool) → Fin k → Fin 2 → ℕ,
      (∀ σ, initial σ ∈ generalBirthCounts N 56 (twoWordCenter σ) (fun i y => twoWordQ σ i y y) twoBirthEnergy) ∧
      (∀ σ, generalWordReadout N (fun _ => 0) (fun _ => 2) (initial σ)=σ) ∧ Function.Injective initial) ∧
    ∀ σ : Fin k → Bool,
    let center := twoWordCenter σ
    let Q := twoWordQ σ
    let next := generalGlobalNext (fun _ => twoConsume) (fun _ => twoProduce) 0
    let rate := generalGlobalRate (fun _ => twoConsume) (fun _ => twoCoeff) 0 γ w
    let hrate := general_global_rate_nonneg (fun _ => twoConsume) (fun _ => twoCoeff) 0 γ w (fun _ => two_coeff_nonneg) hγ.le hw
    let domain₀ := generalProductDomain N 56 center (fun i y => Q i y y) twoOuterEnergy
    let domain₁ := generalProductDomain N 56 center (fun i y => Q i y y) twoParentEnergy
    ∃ (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
      (hclock₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₀).total s ≤ q₀)
      (hclock₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain₁).total s ≤ q₁),
    let K := generalGenerationLaw hk next rate hrate N 56 hN Q center 1 twoRadius twoBirthEnergy twoOuterEnergy twoParentEnergy twoRecoverEnergy
      (by norm_num) (by norm_num [twoRadius]) (by norm_num [twoBirthEnergy,twoOuterEnergy]) (by norm_num [twoOuterEnergy,twoRadius]) (by norm_num [twoRecoverEnergy,twoParentEnergy]) (two_word_center_cap σ) (two_word_coercivity σ) q₀ t₀ q₁ t₁ hq₀ hq₁ hclock₀ hclock₁
    let ε := (k:ℝ)*(7+2*(2:ℝ)+(200*twoRho/2)*((t₀:ℝ)/(twoOuterEnergy-twoBirthEnergy)+(t₁:ℝ)/(twoParentEnergy-twoRecoverEnergy)))*Real.exp (-cgen*N)
    (∀ n, (K n).mass none ≤ ε) ∧
    ∀ (G : ℕ) n, 1-(G:ℝ)*ε ≤ wordLineageSuccess K G n := by
  classical
  obtain ⟨coupling,N0,γ₀,cgen,t₀,hcoupling,hγ₀,hγ₀c,hN0,hcgen,ht₀,hinterval⟩ :=
    general_uniform_word_interval 2 56 (by norm_num)
      1 twoRadius twoOuterEnergy twoRecoverEnergy twoParentEnergy twoBirthEnergy
      200 twoRho 50000 20000 100000 200000 55 4 50000 160000 (1/10000) (1/2)
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
      (by norm_num [twoRadius,twoOuterEnergy,twoRecoverEnergy,twoParentEnergy,twoBirthEnergy,twoRho])
  refine ⟨coupling,N0,γ₀,cgen,t₀,hcoupling,hγ₀,hγ₀c,hN0,hcgen,ht₀,?_⟩
  intro γ hγ hγmax
  obtain ⟨t₁,ht₁,harch⟩ := hinterval γ hγ hγmax
  refine ⟨t₁,ht₁,?_⟩
  intro k hk N hN hlarge w hw hdiag hsym κ hκ hκmax hrow
  apply harch hk N hN hlarge (fun _ => twoConsume) (fun _ => twoProduce) (fun _ => twoCoeff) 0 w
    (fun _ => two_coeff_nonneg) hw hdiag hsym twoWordCenter twoWordQ κ hκ hκmax
    two_word_center_nonneg two_word_center_cap (fun σ i => twoQ_symm (σ i)) (fun σ i => twoQ_operator (σ i))
    (fun _ => two_activity_bound)
    (fun _ => by simpa only [show (55:ℝ)+1=56 by norm_num,twoStoich] using two_propensity_bias_bound)
    hrow ?_ ?_ two_word_coercivity ?_ (fun _ => 0) (fun _ => 2) ?_
  · intro σ s hs i
    have he := (Finset.mem_filter.mp hs).2 i
    exact two_module_quality (σ i) (generalConcentration s i) he
  · intro σ s hs i
    have he := (Finset.mem_filter.mp hs).2 i
    have hh := two_well_growth_bounds (σ i) (generalConcentration s i) he
    exact ⟨(by norm_num : (0:ℝ) ≤ 1/2).trans hh.1,hh.2⟩
  · intro σ s hs i
    exact (two_well_growth_bounds (σ i) (generalConcentration s i) ((Finset.mem_filter.mp hs).2 i)).1
  · intro σ i
    cases hs : σ i <;> norm_num [twoWordCenter,twoCenter,twoRadius,hs]

end CompositionalMemory
