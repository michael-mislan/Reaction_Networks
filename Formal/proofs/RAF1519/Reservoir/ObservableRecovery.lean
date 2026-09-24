import proofs.RAF1519.Reservoir.FeedbackLoad

namespace RAF1519.Reservoir
noncomputable section
open Set

theorem uptake_lipschitz (R z S R₀ z₀ S₀ B e : ℝ)
    (hB : 0 ≤ B) (he : 0 ≤ e)
    (hz : |z| ≤ B) (hS : |S| ≤ B)
    (hR₀ : |R₀| ≤ B) (hz₀ : |z₀| ≤ B)
    (hRe : |R-R₀| ≤ e) (hze : |z-z₀| ≤ e) (hSe : |S-S₀| ≤ e) :
    |R*z*S-R₀*z₀*S₀| ≤ 3*B^2*e := by
  have a := mul_le_mul (mul_le_mul hRe hz (abs_nonneg _) he) hS (abs_nonneg _) (by positivity : 0 ≤ e*B)
  have b := mul_le_mul (mul_le_mul hR₀ hze (abs_nonneg _) hB) hS (abs_nonneg _) (by positivity : 0 ≤ B*e)
  have c := mul_le_mul (mul_le_mul hR₀ hz₀ (abs_nonneg _) hB) hSe (abs_nonneg _) (by positivity : 0 ≤ B*B)
  have hi : R*z*S-R₀*z₀*S₀=(R-R₀)*z*S+R₀*(z-z₀)*S+R₀*z₀*(S-S₀) := by ring
  rw [hi]
  have hab := abs_add_le ((R-R₀)*z*S) (R₀*(z-z₀)*S)
  have habc := abs_add_le ((R-R₀)*z*S+R₀*(z-z₀)*S) (R₀*z₀*(S-S₀))
  simp only [abs_mul] at hab habc
  nlinarith

theorem energy_coordinate_envelope (x c E E₀ t : ℝ)
    (hE₀ : 0 ≤ E₀) (hc : (x-c)^2 ≤ 2000*E)
    (hd : E ≤ E₀*Real.exp (-t/400)) :
    |x-c| ≤ Real.sqrt (2000*E₀)*Real.exp (-t/800) := by
  have hs := Real.sq_sqrt (show 0 ≤ 2000*E₀ by positivity)
  have hex : (Real.exp (-t/800))^2=Real.exp (-t/400) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hn : 0 ≤ Real.sqrt (2000*E₀)*Real.exp (-t/800) := by positivity
  have hsq : (Real.sqrt (2000*E₀)*Real.exp (-t/800))^2=2000*E₀*Real.exp (-t/400) := by
    rw [mul_pow,hs,hex]
  have hx := sq_abs (x-c)
  nlinarith [abs_nonneg (x-c)]

theorem observable_deadline (A δ t : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (ht : 800*Real.log (A/δ) ≤ t) : A*Real.exp (-t/800) ≤ δ := by
  have he : -t/800 ≤ Real.log (δ/A) := by
    rw [Real.log_div hδ.ne' hA.ne',Real.log_div hA.ne' hδ.ne'] at *
    linarith
  have hx := Real.exp_le_exp.mpr he
  rw [Real.exp_log (div_pos hδ hA)] at hx
  have hm := mul_le_mul_of_nonneg_left hx hA.le
  have hi : A*(δ/A)=δ := by field_simp
  rwa [hi] at hm

theorem aggregate_energy_coercive {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) (s : ℝ)
    (hP : ∀ y, (1/1000:ℝ)*(∑ i, (y i)^2) ≤ quadratic P y)
    (x : Community n) (i : Fin 6) :
    (aggregate x i-state s i)^2 ≤ 2000*communityEnergy P q s x := by
  have h := core_coordinate_bound P hP (aggregate x-state s) i
  have he := core_nonnegative P hP (aggregate x-state s)
  have hv := variance_nonnegative q (normalizedDeviation q x) (fun j => (hpos j).le)
  dsimp [communityEnergy]
  change (aggregate x i-state s i)^2 ≤ _ at h
  nlinarith

/-- A local, source-specific recovery guarantee. The sublevel conditions are
exactly the dissipation conditions already established near both equilibria. -/
theorem source_observable_recovery {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (hq : ∑ i, q i=1) (hpos : ∀ i, 0 < q i)
    (s : ℝ) (x₀ : Community n) (R ρ B : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hP : ∀ y, (1/1000:ℝ)*(∑ i, (y i)^2) ≤ quadratic P y)
    (hbounded : ∀ x, communityEnergy P q s x ≤ ρ → ‖x‖ ≤ R)
    (hcore : ∀ x, communityEnergy P q s x ≤ ρ →
      quadraticRate P (field (aggregate x)) (aggregate x-state s) ≤
        -(1/400:ℝ)*quadratic P (aggregate x-state s))
    (hgrad : ∀ x, communityEnergy P q s x ≤ ρ →
      |quadraticRate P consumerAxis (aggregate x-state s)| ≤ 1)
    (hg : ∀ x, communityEnergy P q s x ≤ ρ →
      x (.inl 4)*x (.inl 2)-1/2-2*totalConsumers x ≤ -3/100)
    (hy : ∀ x, communityEnergy P q s x ≤ ρ → ∀ i, -(1/100:ℝ) ≤ normalizedDeviation q x i)
    (hbox : ∀ x, communityEnergy P q s x ≤ ρ →
      |x (.inl 4)| ≤ B ∧ |x (.inl 2)| ≤ B ∧ |totalConsumers x| ≤ B)
    (hcbox : |reservoir s| ≤ B ∧ |resource s| ≤ B)
    (h0 : communityEnergy P q s x₀ ≤ ρ) :
    ∃ X : ℝ → Community n, X 0=x₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt X (communityField q (X t)) t) ∧
      (∀ t, 0 ≤ t → |communityUptake (X t)-communityUptake (lift q s)| ≤
        3*B^2*Real.sqrt (2000*communityEnergy P q s x₀)*Real.exp (-t/800)) := by
  obtain ⟨X,hX0,hXd,hE,_⟩ := energy_sublevel_solution (communityField q)
    (communityEnergy P q s) (fun x => fderiv ℝ (communityEnergy P q s) x)
    (lift q s) x₀ R 2000 ρ (1/400) hR (by norm_num) hρ (by norm_num)
    (communityField_contDiff q)
    (fun x => ((communityEnergy_contDiff P q s).differentiable (by norm_num) x).hasFDerivAt)
    (fun x => communityEnergy_nonnegative P q hpos s x hP)
    (communityEnergy_coercive P q hq hpos s hP) hbounded
    (fun x hx => communityEnergy_source_decay P q s x hq hpos
      (hcore x hx) (hgrad x hx) (hg x hx) (hy x hx)) h0
  refine ⟨X,hX0,hXd,?_⟩
  intro t ht
  have hdec : communityEnergy P q s (X t) ≤ communityEnergy P q s x₀*Real.exp (-t/400) := by
    have hi : -(1/400:ℝ)*t = -t/400 := by ring
    simpa only [hi] using (hE t ht).2
  have ha (i : Fin 6) := energy_coordinate_envelope (aggregate (X t) i) (state s i)
    _ _ t (communityEnergy_nonnegative P q hpos s x₀ hP)
    (aggregate_energy_coercive P q hpos s hP (X t) i) hdec
  have hb := hbox (X t) (hE t ht).1
  have hu := uptake_lipschitz (X t (.inl 4)) (X t (.inl 2)) (totalConsumers (X t))
    (reservoir s) (resource s) s B (Real.sqrt (2000*communityEnergy P q s x₀)*Real.exp (-t/800))
    hB (by positivity) hb.2.1 hb.2.2 hcbox.1 hcbox.2 (ha 4) (ha 2) (ha 5)
  unfold communityUptake
  rw [total_lift q hq s]
  simpa only [mul_assoc] using hu

end
end RAF1519.Reservoir

