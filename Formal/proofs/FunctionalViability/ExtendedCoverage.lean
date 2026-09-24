import proofs.FunctionalViability.RobustCertificate

namespace FunctionalViability.Robust
noncomputable section

/-! ## Full coverage range

The stage-coverage parameter `c` bounds a sum of two probabilities, so its
natural range is `[0,2]`, not `[0,1]`. `hRange c` is the width of the interval
available to a clipped first-stage probability, and `extendedFloor` is the sharp
equally weighted complete-path floor on the full range. -/

def hRange (c : ℝ) : ℝ := min c (2-c)

def extendedFloor (c d : ℝ) : ℝ := (c^2-(min d (hRange c))^2)/4

theorem hRange_le_left (c : ℝ) : hRange c ≤ c := min_le_left _ _

theorem hRange_le_right (c : ℝ) : hRange c ≤ 2-c := min_le_right _ _

theorem hRange_nonneg (c : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 2) : 0 ≤ hRange c :=
  le_min hc (by linarith)

theorem le_hRange (c v : ℝ) (h1 : v ≤ c) (h2 : v ≤ 2-c) : v ≤ hRange c := le_min h1 h2

theorem mismatch_le_d (c d : ℝ) : min d (hRange c) ≤ d := min_le_left _ _

theorem mismatch_le_c (c d : ℝ) : min d (hRange c) ≤ c :=
  le_trans (min_le_right _ _) (hRange_le_left c)

theorem mismatch_le_two (c d : ℝ) : min d (hRange c) ≤ 2-c :=
  le_trans (min_le_right _ _) (hRange_le_right c)

theorem mismatch_nonneg (c d : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 2) (hd : 0 ≤ d) :
    0 ≤ min d (hRange c) := le_min hd (hRange_nonneg c hc hc2)

theorem extendedFloor_nonneg (c d : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 2) (hd : 0 ≤ d) :
    0 ≤ extendedFloor c d := by
  have h0 := mismatch_nonneg c d hc hc2 hd
  have h1 := mismatch_le_c c d
  unfold extendedFloor
  nlinarith

/-- The clipped rectangle identity: on a common interval the two complete-path
products are controlled by the coverage level and the stage mismatch alone. -/
theorem clipped_core (c t X Y : ℝ) (h1 : X-Y ≤ t) (h2 : Y-X ≤ t) :
    (c^2-t^2)/4 ≤ (X*Y+(c-X)*(c-Y))/2 := by
  have hs : (X-Y)^2 ≤ t^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ t-(X-Y) by linarith)
      (show (0:ℝ) ≤ t+(X-Y) by linarith)]
  nlinarith [sq_nonneg (X+Y-c)]

/-- On the manuscript's restricted range the extended floor is the old floor. -/
theorem extended_eq_recoveryFloor (c d : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hd : 0 ≤ d) :
    extendedFloor c d = recoveryFloor c d := by
  have hh : hRange c = c := min_eq_left (by linarith)
  unfold extendedFloor recoveryFloor
  rw [hh]
  rcases le_total d c with h | h
  · have hcd : 0 ≤ c-d := by linarith
    have hpd : 0 ≤ c+d := by linarith
    have hsq : 0 ≤ c^2-d^2 := by nlinarith [mul_nonneg hcd hpd]
    rw [min_eq_left h, max_eq_right hsq]
  · have hcd : 0 ≤ d-c := by linarith
    have hpd : 0 ≤ d+c := by linarith
    have hsq : c^2-d^2 ≤ 0 := by nlinarith [mul_nonneg hcd hpd]
    rw [min_eq_right h, max_eq_left hsq]
    ring

/-- Sharp coverage floor on the full range `0 ≤ c ≤ 2`. -/
theorem extended_coverage_bound (c d x y a b : ℝ) (hc : 0 ≤ c)
    (h : Admissible c d x y a b) : extendedFloor c d ≤ (x*y+a*b)/2 := by
  rcases h with ⟨hx, hy, ha, hb, hca, hcb, hd⟩
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  rcases le_total c 1 with h1 | h1
  · rw [extended_eq_recoveryFloor c d hc h1 hd0]
    exact coverage_bound c d x y a b hc ⟨hx, hy, ha, hb, hca, hcb, hd⟩
  · have hax : c-x ≤ a := by linarith
    have hby : c-y ≤ b := by linarith
    have hxl : c-1 ≤ x := by linarith [ha.2]
    have hyl : c-1 ≤ y := by linarith [hb.2]
    rcases abs_le.mp hd with ⟨hm1, hm2⟩
    have ht1 : x-y ≤ min d (hRange c) :=
      le_min hm2 (le_hRange c _ (by linarith) (by linarith [hx.2]))
    have ht2 : y-x ≤ min d (hRange c) :=
      le_min (by linarith) (le_hRange c _ (by linarith) (by linarith [hy.2]))
    have hprod : (c-x)*(c-y) ≤ a*b := mul_le_mul hax hby (by linarith) ha.1
    have hcore := clipped_core c (min d (hRange c)) x y ht1 ht2
    unfold extendedFloor
    linarith

/-- Attaining sources on the full range: both complete-path products equal the floor. -/
theorem extended_sharp_witness (c d : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 2) (hd : 0 ≤ d) :
    ∃ x y a b, Admissible c d x y a b ∧
      x*y = extendedFloor c d ∧ a*b = extendedFloor c d := by
  have ht0 := mismatch_nonneg c d hc hc2 hd
  have htd := mismatch_le_d c d
  have htc := mismatch_le_c c d
  have ht2 := mismatch_le_two c d
  refine ⟨(c+min d (hRange c))/2, (c-min d (hRange c))/2,
    (c-min d (hRange c))/2, (c+min d (hRange c))/2, ?_, ?_, ?_⟩
  · unfold Admissible
    have he : (c+min d (hRange c))/2-(c-min d (hRange c))/2 = min d (hRange c) := by ring
    rw [he, abs_of_nonneg ht0]
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      by linarith, by linarith, htd⟩
  · unfold extendedFloor; ring
  · unfold extendedFloor; ring

/-- Equal allocation is maximin on the full range. -/
theorem extended_minimax (c d : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 2) (hd : 0 ≤ d) :
    (∀ x y a b, Admissible c d x y a b → extendedFloor c d ≤ (x*y+a*b)/2) ∧
    (∀ w : ℝ, ∃ x y a b, Admissible c d x y a b ∧
      w*(x*y)+(1-w)*(a*b) = extendedFloor c d) := by
  refine ⟨fun x y a b h => extended_coverage_bound c d x y a b hc h, ?_⟩
  intro w
  obtain ⟨x, y, a, b, h, hu, hv⟩ := extended_sharp_witness c d hc hc2 hd
  exact ⟨x, y, a, b, h, by rw [hu, hv]; ring⟩

/-- High coverage gives a positive floor with no mismatch information at all. -/
theorem extended_high_coverage (c d : ℝ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hd : 0 ≤ d) :
    c-1 ≤ extendedFloor c d := by
  have ht0 := mismatch_nonneg c d (by linarith) hc2 hd
  have ht := mismatch_le_two c d
  unfold extendedFloor
  nlinarith [mul_nonneg (show (0:ℝ) ≤ 2-c-min d (hRange c) by linarith)
    (show (0:ℝ) ≤ 2-c+min d (hRange c) by linarith)]

/-! ## Coverage without a mismatch hypothesis -/

/-- Stage coverage alone, with no mismatch bound. -/
def Covers (c x y a b : ℝ) : Prop :=
  (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧ (0 ≤ a ∧ a ≤ 1) ∧
  (0 ≤ b ∧ b ≤ 1) ∧ c ≤ x+a ∧ c ≤ y+b

theorem covers_admissible (c x y a b : ℝ) (h : Covers c x y a b) :
    Admissible c |x-y| x y a b := by
  rcases h with ⟨hx, hy, ha, hb, hca, hcb⟩
  exact ⟨hx, hy, ha, hb, hca, hcb, le_rfl⟩

theorem covers_floor (c x y a b : ℝ) (hc : 0 ≤ c)
    (h : Covers c x y a b) : extendedFloor c |x-y| ≤ (x*y+a*b)/2 :=
  extended_coverage_bound c |x-y| x y a b hc (covers_admissible c x y a b h)

/-- The approximate-complementarity floor is attained: the witnesses deviate from
exact complementarity by exactly `eps` in both stages. -/
theorem approximate_complementarity_sharp (eps d : ℝ) (he : 0 ≤ eps ∧ eps ≤ 1)
    (hd : 0 ≤ d) :
    ∃ x y a b, Admissible (1-eps) d x y a b ∧
      |a-(1-x)| ≤ eps ∧ |b-(1-y)| ≤ eps ∧
      (x*y+a*b)/2 = recoveryFloor (1-eps) d := by
  have hc0 : (0:ℝ) ≤ 1-eps := by linarith [he.2]
  have hc2 : (1:ℝ)-eps ≤ 2 := by linarith [he.1]
  have ht0 := mismatch_nonneg (1-eps) d hc0 hc2 hd
  have htd := mismatch_le_d (1-eps) d
  have htc := mismatch_le_c (1-eps) d
  have ht2 := mismatch_le_two (1-eps) d
  refine ⟨(1-eps+min d (hRange (1-eps)))/2, (1-eps-min d (hRange (1-eps)))/2,
    (1-eps-min d (hRange (1-eps)))/2, (1-eps+min d (hRange (1-eps)))/2, ?_, ?_, ?_, ?_⟩
  · unfold Admissible
    have hq : (1-eps+min d (hRange (1-eps)))/2-(1-eps-min d (hRange (1-eps)))/2
        = min d (hRange (1-eps)) := by ring
    rw [hq, abs_of_nonneg ht0]
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      by linarith, by linarith, htd⟩
  · have hq : (1-eps-min d (hRange (1-eps)))/2
        -(1-(1-eps+min d (hRange (1-eps)))/2) = -eps := by ring
    rw [hq, abs_neg, abs_of_nonneg he.1]
  · have hq : (1-eps+min d (hRange (1-eps)))/2
        -(1-(1-eps-min d (hRange (1-eps)))/2) = -eps := by ring
    rw [hq, abs_neg, abs_of_nonneg he.1]
  · rw [← extended_eq_recoveryFloor (1-eps) d hc0 (by linarith [he.1]) hd]
    unfold extendedFloor
    ring

/-! ## Recording, exceptional mass and a mean-square mismatch budget -/

/-- Conditional recording at level `kappa` preserves any certified path floor. -/
theorem recorded_floor (L kappa : ℝ) (z : Stages) (hk : 0 ≤ kappa)
    (hcov : L ≤ (z.x*z.y+z.a*z.b)/2) (hr : kappa ≤ z.r) (hs : kappa ≤ z.s) :
    kappa*L ≤ (z.x*z.y*z.r+z.a*z.b*z.s)/2 := by
  have h := mul_le_mul_of_nonneg_left hcov hk
  have h1 := mul_le_mul_of_nonneg_left hr (mul_nonneg z.hx.1 z.hy.1)
  have h2 := mul_le_mul_of_nonneg_left hs (mul_nonneg z.ha.1 z.hb.1)
  nlinarith

/-- A recoverable-type population whose covered types are stage-covered at level
`c`, whose covered mismatch is controlled only in mean square, and whose covered
completed paths are recorded with conditional probability at least `kappa`. -/
structure MomentPopulation (K : Type*) [Fintype K] (c D kappa eta : ℝ) where
  μ : K → ℝ
  z : K → Stages
  cover : Finset K
  nonneg : ∀ k, 0 ≤ μ k
  normalized : ∑ k, μ k = 1
  mass : 1-eta ≤ ∑ k ∈ cover, μ k
  covers : ∀ k ∈ cover, Covers c (z k).x (z k).y (z k).a (z k).b
  moment : ∑ k ∈ cover, μ k*((z k).x-(z k).y)^2 ≤ (∑ k ∈ cover, μ k)*D^2
  recording : ∀ k ∈ cover, kappa ≤ (z k).r ∧ kappa ≤ (z k).s

def momentFloor (c D kappa eta : ℝ) : ℝ := (1-eta)*kappa*extendedFloor c D

theorem moment_population_floor {K : Type*} [Fintype K] {c D kappa eta : ℝ}
    (M : MomentPopulation K c D kappa eta) (hc : 0 ≤ c) (hc2 : c ≤ 2)
    (hD : 0 ≤ D) (hk : 0 ≤ kappa) :
    momentFloor c D kappa eta ≤
      (recordedMean M.μ (fun k => (M.z k).x) (fun k => (M.z k).y) (fun k => (M.z k).r) +
       recordedMean M.μ (fun k => (M.z k).a) (fun k => (M.z k).b) (fun k => (M.z k).s))/2 := by
  have hh0 : 0 ≤ hRange c := hRange_nonneg c hc hc2
  have htau0 : 0 ≤ min D (hRange c) := le_min hD hh0
  have htauc : min D (hRange c) ≤ c := mismatch_le_c c D
  -- pointwise certified floor on the covered set
  have hpt : ∀ k ∈ M.cover,
      (kappa*c^2/4)*M.μ k
        -(kappa/4)*(M.μ k*(min |(M.z k).x-(M.z k).y| (hRange c))^2)
      ≤ M.μ k*((M.z k).x*(M.z k).y*(M.z k).r+(M.z k).a*(M.z k).b*(M.z k).s)/2 := by
    intro k hk'
    have hcov := covers_floor c (M.z k).x (M.z k).y (M.z k).a (M.z k).b hc
      (M.covers k hk')
    have hrec := recorded_floor (extendedFloor c |(M.z k).x-(M.z k).y|) kappa (M.z k) hk
      hcov (M.recording k hk').1 (M.recording k hk').2
    have hm := mul_le_mul_of_nonneg_left hrec (M.nonneg k)
    have e1 : (kappa*c^2/4)*M.μ k
        -(kappa/4)*(M.μ k*(min |(M.z k).x-(M.z k).y| (hRange c))^2)
        = M.μ k*(kappa*extendedFloor c |(M.z k).x-(M.z k).y|) := by
      unfold extendedFloor; ring
    have e2 : M.μ k*(((M.z k).x*(M.z k).y*(M.z k).r+(M.z k).a*(M.z k).b*(M.z k).s)/2)
        = M.μ k*((M.z k).x*(M.z k).y*(M.z k).r+(M.z k).a*(M.z k).b*(M.z k).s)/2 := by ring
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  -- the covered partial sum is dominated by the full population sum
  have hfull : ∑ k ∈ M.cover,
      M.μ k*((M.z k).x*(M.z k).y*(M.z k).r+(M.z k).a*(M.z k).b*(M.z k).s)/2
      ≤ ∑ k, M.μ k*((M.z k).x*(M.z k).y*(M.z k).r+(M.z k).a*(M.z k).b*(M.z k).s)/2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro k _ _
    exact div_nonneg (mul_nonneg (M.nonneg k) (add_nonneg
      (triple_bounds _ _ _ (M.z k).hx (M.z k).hy (M.z k).hr).1
      (triple_bounds _ _ _ (M.z k).ha (M.z k).hb (M.z k).hs).1)) (by norm_num)
  have hid : (∑ k, M.μ k*((M.z k).x*(M.z k).y*(M.z k).r+
      (M.z k).a*(M.z k).b*(M.z k).s)/2) =
      (recordedMean M.μ (fun k => (M.z k).x) (fun k => (M.z k).y) (fun k => (M.z k).r)+
       recordedMean M.μ (fun k => (M.z k).a) (fun k => (M.z k).b) (fun k => (M.z k).s))/2 := by
    simp only [recordedMean, mul_add, add_div, Finset.sum_add_distrib, Finset.sum_div]
  -- the clipped mean-square mismatch budget
  have hT : ∑ k ∈ M.cover, M.μ k*(min |(M.z k).x-(M.z k).y| (hRange c))^2
      ≤ (∑ k ∈ M.cover, M.μ k)*(min D (hRange c))^2 := by
    rcases le_total D (hRange c) with hDh | hDh
    · rw [min_eq_left hDh]
      refine le_trans (Finset.sum_le_sum ?_) M.moment
      intro k hk'
      have h0 : 0 ≤ min |(M.z k).x-(M.z k).y| (hRange c) := le_min (abs_nonneg _) hh0
      have h1 : min |(M.z k).x-(M.z k).y| (hRange c) ≤ |(M.z k).x-(M.z k).y| :=
        min_le_left _ _
      have h2 : (min |(M.z k).x-(M.z k).y| (hRange c))^2 ≤ ((M.z k).x-(M.z k).y)^2 := by
        nlinarith [sq_abs ((M.z k).x-(M.z k).y), abs_nonneg ((M.z k).x-(M.z k).y)]
      exact mul_le_mul_of_nonneg_left h2 (M.nonneg k)
    · rw [min_eq_right hDh]
      have hstep : ∀ k ∈ M.cover,
          M.μ k*(min |(M.z k).x-(M.z k).y| (hRange c))^2 ≤ M.μ k*(hRange c)^2 := by
        intro k hk'
        have h0 : 0 ≤ min |(M.z k).x-(M.z k).y| (hRange c) := le_min (abs_nonneg _) hh0
        have h1 : min |(M.z k).x-(M.z k).y| (hRange c) ≤ hRange c := min_le_right _ _
        exact mul_le_mul_of_nonneg_left (by nlinarith) (M.nonneg k)
      calc ∑ k ∈ M.cover, M.μ k*(min |(M.z k).x-(M.z k).y| (hRange c))^2
          ≤ ∑ k ∈ M.cover, M.μ k*(hRange c)^2 := Finset.sum_le_sum hstep
        _ = (∑ k ∈ M.cover, M.μ k)*(hRange c)^2 := by rw [← Finset.sum_mul]
  have hSnn : 0 ≤ ∑ k ∈ M.cover, M.μ k :=
    Finset.sum_nonneg (fun k _ => M.nonneg k)
  have hgap : 0 ≤ c^2-(min D (hRange c))^2 := by nlinarith
  have hmassgap : (1-eta)*(c^2-(min D (hRange c))^2)
      ≤ (∑ k ∈ M.cover, M.μ k)*(c^2-(min D (hRange c))^2) :=
    mul_le_mul_of_nonneg_right M.mass hgap
  have hTk : (kappa/4)*(∑ k ∈ M.cover, M.μ k*(min |(M.z k).x-(M.z k).y| (hRange c))^2)
      ≤ (kappa/4)*((∑ k ∈ M.cover, M.μ k)*(min D (hRange c))^2) :=
    mul_le_mul_of_nonneg_left hT (by linarith)
  rw [← hid]
  unfold momentFloor extendedFloor
  nlinarith [hsum, hfull, hTk, hmassgap]

/-! ## The decision chain over any certified detection floor -/

theorem mean_floor_certificate {K : Type*} [Fintype K] (μ : K → ℝ) (z : K → Stages)
    (G p theta : ℝ) (m : ℕ) (hμ : ∀ k, 0 ≤ μ k) (hnorm : ∑ k, μ k = 1)
    (hp : 0 ≤ p ∧ p ≤ 1) (ht : 0 ≤ theta ∧ theta ≤ p) (hG : 0 ≤ G)
    (hfloor : G ≤ (recordedMean μ (fun k => (z k).x) (fun k => (z k).y) (fun k => (z k).r) +
      recordedMean μ (fun k => (z k).a) (fun k => (z k).b) (fun k => (z k).s))/2) :
    balancedNegative μ (fun k => (z k).x) (fun k => (z k).y) (fun k => (z k).a)
        (fun k => (z k).b) (fun k => (z k).r) (fun k => (z k).s) p m
      ≤ (1-theta*G)^(2*m) := by
  rw [balanced_identity _ _ _ _ _ _ _ _ _ hnorm]
  apply balanced_bound
  · exact mean_bounds _ _ _ _ hμ hnorm (fun k => (z k).hx) (fun k => (z k).hy)
      (fun k => (z k).hr)
  · exact mean_bounds _ _ _ _ hμ hnorm (fun k => (z k).ha) (fun k => (z k).hb)
      (fun k => (z k).hs)
  · exact hp
  · exact ht
  · exact hG
  · exact hfloor

def momentExperiment {K : Type*} [Fintype K] {c D kappa eta : ℝ}
    (M : MomentPopulation K c D kappa eta) (p : ℝ) (m : ℕ) :=
  balancedNegative M.μ (fun k => (M.z k).x) (fun k => (M.z k).y)
    (fun k => (M.z k).a) (fun k => (M.z k).b)
    (fun k => (M.z k).r) (fun k => (M.z k).s) p m

theorem moment_source_certificate {K : Type*} [Fintype K] {c D kappa eta : ℝ}
    (M : MomentPopulation K c D kappa eta) (p theta : ℝ) (m : ℕ)
    (hc : 0 ≤ c) (hc2 : c ≤ 2) (hD : 0 ≤ D) (hk : 0 ≤ kappa) (heta : eta ≤ 1)
    (hp : 0 ≤ p ∧ p ≤ 1) (ht : 0 ≤ theta ∧ theta ≤ p) :
    momentExperiment M p m ≤ (1-theta*momentFloor c D kappa eta)^(2*m) := by
  unfold momentExperiment
  refine mean_floor_certificate M.μ M.z _ p theta m M.nonneg M.normalized hp ht ?_ ?_
  · unfold momentFloor
    exact mul_nonneg (mul_nonneg (by linarith) hk) (extendedFloor_nonneg c D hc hc2 hD)
  · exact moment_population_floor M hc hc2 hD hk

theorem calibrated_composition {E : Type*} [Fintype E] (ν expt bad : E → ℝ)
    (good : E → Bool) (B delta : ℝ) (hν : ∀ e, 0 ≤ ν e) (hs : ∑ e, ν e = 1)
    (hbad : ∀ e, bad e ≤ 1) (hB : B ≤ 1)
    (hgood : ∀ e, good e = true → expt e ≤ B)
    (hb : (∑ e, if good e then 0 else ν e) ≤ delta) :
    (∑ e, ν e*(if good e then expt e else bad e)) ≤ delta+(1-delta)*B := by
  apply sharp_calibration ν _ good B delta hν hs
  · intro e
    cases he : good e
    · simpa using hbad e
    · simpa using le_trans (hgood e he) hB
  · intro e he
    simpa [he] using hgood e he
  · exact hB
  · exact hb

/-- Full-range calibrated certificate: stage coverage on `[0,2]`, a mean-square
mismatch budget, conditional recording, exceptional recoverable mass, a fixed
balanced design, and a conditional calibration-failure allowance. -/
theorem moment_calibrated_certificate {K E : Type*} [Fintype K] [Fintype E]
    {c D kappa eta : ℝ} (M : E → MomentPopulation K c D kappa eta)
    (ν bad : E → ℝ) (good : E → Bool) (p theta B delta : ℝ) (m : ℕ)
    (hc : 0 ≤ c) (hc2 : c ≤ 2) (hD : 0 ≤ D) (hk : 0 ≤ kappa) (heta : eta ≤ 1)
    (hp : 0 ≤ p ∧ p ≤ 1) (ht : 0 ≤ theta ∧ theta ≤ p)
    (hν : ∀ e, 0 ≤ ν e) (hs : ∑ e, ν e = 1) (hbad : ∀ e, bad e ≤ 1) (hB : B ≤ 1)
    (budget : (1-theta*momentFloor c D kappa eta)^(2*m) ≤ B)
    (hb : (∑ e, if good e then 0 else ν e) ≤ delta) :
    (∑ e, ν e*(if good e then momentExperiment (M e) p m else bad e))
      ≤ delta+(1-delta)*B := by
  refine calibrated_composition ν _ bad good B delta hν hs hbad hB ?_ hb
  intro e _
  exact le_trans (moment_source_certificate (M e) p theta m hc hc2 hD hk heta hp ht) budget

/-- A uniform per-type mismatch bound is a mean-square budget, so the uniform
model of the previous root is a special case of the full-range certificate. -/
def ofUniform {K : Type*} [Fintype K] {c d kappa eta : ℝ} (μ : K → ℝ) (z : K → Stages)
    (cover : Finset K) (hnn : ∀ k, 0 ≤ μ k) (hnorm : ∑ k, μ k = 1)
    (hmass : 1-eta ≤ ∑ k ∈ cover, μ k)
    (hcov : ∀ k ∈ cover, Admissible c d (z k).x (z k).y (z k).a (z k).b)
    (hrec : ∀ k ∈ cover, kappa ≤ (z k).r ∧ kappa ≤ (z k).s) :
    MomentPopulation K c d kappa eta where
  μ := μ
  z := z
  cover := cover
  nonneg := hnn
  normalized := hnorm
  mass := hmass
  covers := fun k hk => by
    obtain ⟨hx, hy, ha, hb, hca, hcb, _⟩ := hcov k hk
    exact ⟨hx, hy, ha, hb, hca, hcb⟩
  moment := by
    have hstep : ∀ k ∈ cover, μ k*((z k).x-(z k).y)^2 ≤ μ k*d^2 := by
      intro k hk
      obtain ⟨_, _, _, _, _, _, hd⟩ := hcov k hk
      have h0 : 0 ≤ d := le_trans (abs_nonneg _) hd
      have h1 := abs_le.mp hd
      exact mul_le_mul_of_nonneg_left (by nlinarith [h1.1, h1.2]) (hnn k)
    calc ∑ k ∈ cover, μ k*((z k).x-(z k).y)^2
        ≤ ∑ k ∈ cover, μ k*d^2 := Finset.sum_le_sum hstep
      _ = (∑ k ∈ cover, μ k)*d^2 := by rw [← Finset.sum_mul]
  recording := hrec

end
end FunctionalViability.Robust
