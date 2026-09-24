import proofs.PowerLawSmallRAF.SourceSplitBlockTail

namespace PowerLawSmallRAF

noncomputable section

open Filter Topology
open RAF RAF.Polymer RAF.Concrete

noncomputable def sourceSplitTailRatio (c : ℝ) : ℝ :=
  2 * Real.exp (-c)

theorem sourceSplitTailRatio_nonneg (c : ℝ) :
    0 ≤ sourceSplitTailRatio c := by
  dsimp [sourceSplitTailRatio]
  positivity

theorem sourceSplitTailRatio_lt_one {c : ℝ} (hc : Real.log 2 < c) :
    sourceSplitTailRatio c < 1 := by
  rw [sourceSplitTailRatio, ← Real.exp_log (by norm_num : (0 : ℝ) < 2),
    ← Real.exp_add, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem two_mul_geometric_Ico_le {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (K N : Nat) :
    (∑ k ∈ Finset.Ico K N, 2 * q ^ k) ≤
      2 * q ^ K / (1 - q) := by
  calc
    (∑ k ∈ Finset.Ico K N, 2 * q ^ k) =
        2 * ∑ k ∈ Finset.Ico K N, q ^ k := by rw [Finset.mul_sum]
    _ ≤ 2 * (q ^ K / (1 - q)) := by
      gcongr
      exact geom_sum_Ico_le_of_lt_one hq0 hq1
    _ = 2 * q ^ K / (1 - q) := by ring

theorem one_sub_sum_le_prod_one_sub
    {I : Type*} [DecidableEq I] (S : Finset I) (u : I → ℝ)
    (hu0 : ∀ i ∈ S, 0 ≤ u i) (hu1 : ∀ i ∈ S, u i ≤ 1) :
    1 - ∑ i ∈ S, u i ≤ ∏ i ∈ S, (1 - u i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hua0 := hu0 a (Finset.mem_insert_self a S)
      have hua1 := hu1 a (Finset.mem_insert_self a S)
      have hsum0 : 0 ≤ ∑ i ∈ S, u i :=
        Finset.sum_nonneg fun i hi => hu0 i (Finset.mem_insert_of_mem hi)
      have hih := ih
        (fun i hi => hu0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hu1 i (Finset.mem_insert_of_mem hi))
      calc
        1 - (u a + ∑ i ∈ S, u i) ≤
            (1 - u a) * (1 - ∑ i ∈ S, u i) := by
          nlinarith [mul_nonneg hua0 hsum0]
        _ ≤ (1 - u a) * ∏ i ∈ S, (1 - u i) :=
          mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr hua1)

theorem binary_layer_exponential_eq_ratio
    (c : ℝ) (k : Nat) :
    ((2 ^ (k + 1) : Nat) : ℝ) * Real.exp (-c * (k : ℝ)) =
      2 * sourceSplitTailRatio c ^ k := by
  calc
    ((2 ^ (k + 1) : Nat) : ℝ) * Real.exp (-c * (k : ℝ)) =
        (2 : ℝ) ^ (k + 1) * Real.exp (-c * (k : ℝ)) := by norm_num
    _ = 2 * ((2 : ℝ) ^ k * Real.exp (-c * (k : ℝ))) := by
      rw [pow_succ]
      ring
    _ = 2 * ((2 : ℝ) ^ k * (Real.exp (-c)) ^ k) := by
      rw [← Real.exp_nat_mul]
      congr 3
      ring
    _ = 2 * sourceSplitTailRatio c ^ k := by
      rw [sourceSplitTailRatio, mul_pow]

/-- Union-bound budget for all product words longer than `K`. -/
noncomputable def sourceSplitTailBudget (c : ℝ) (K n : Nat) : ℝ :=
  ∑ x : Molecule n,
    if K < molLength x then Real.exp (-c * (molLength x - 1 : Nat)) else 0

theorem sourceSplitTailBudget_eq (c : ℝ) (K n : Nat) :
    sourceSplitTailBudget c K n =
      ∑ k : Fin n,
        if K < k.val + 1 then
          ((2 ^ (k.val + 1) : Nat) : ℝ) * Real.exp (-c * (k.val : ℝ))
        else 0 := by
  rw [sourceSplitTailBudget]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  simp [molLength]

theorem sourceSplitTailBudget_le_geometric
    {c : ℝ} (hc : Real.log 2 < c) (K n : Nat) :
    sourceSplitTailBudget c K n ≤
      2 * sourceSplitTailRatio c ^ K / (1 - sourceSplitTailRatio c) := by
  rw [sourceSplitTailBudget_eq,
    Fin.sum_univ_eq_sum_range (fun k : Nat =>
      if K < k + 1 then
        ((2 ^ (k + 1) : Nat) : ℝ) * Real.exp (-c * (k : ℝ))
      else 0)]
  have hfilter : (Finset.range n).filter (fun k => K ≤ k) =
      Finset.Ico K n := by
    ext k
    simp [and_comm]
  calc
    (∑ k ∈ Finset.range n,
      if K < k + 1 then
        ((2 ^ (k + 1) : Nat) : ℝ) * Real.exp (-c * (k : ℝ))
      else 0) =
        ∑ k ∈ Finset.Ico K n,
          ((2 ^ (k + 1) : Nat) : ℝ) * Real.exp (-c * (k : ℝ)) := by
      rw [← hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Nat.lt_add_one_iff]
    _ = ∑ k ∈ Finset.Ico K n,
        2 * sourceSplitTailRatio c ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact binary_layer_exponential_eq_ratio c k
    _ ≤ 2 * sourceSplitTailRatio c ^ K /
        (1 - sourceSplitTailRatio c) :=
      two_mul_geometric_Ico_le (sourceSplitTailRatio_nonneg c)
        (sourceSplitTailRatio_lt_one hc) K n

/-- Fixed nonfood word window, used as an `n`-independent index type. -/
abbrev SourceFixedSplitIndex (K : Nat) :=
  {x : Molecule K // 2 < molLength x}

noncomputable def sourceFixedSplitBlock (K n : Nat)
    (i : SourceFixedSplitIndex K) : Finset (Reaction n) :=
  if h : K ≤ n then sourceSplitBlock (liftBinaryMolecule h i.1) else ∅

def sourceFixedSplitBlockSize {K : Nat}
    (i : SourceFixedSplitIndex K) : Nat := molLength i.1 - 1

theorem sourceFixedSplitBlock_card_eventually (K : Nat) :
    ∀ᶠ n : Nat in atTop, ∀ T : Finset (SourceFixedSplitIndex K),
      (T.biUnion (sourceFixedSplitBlock K n)).card =
        ∑ i ∈ T, sourceFixedSplitBlockSize i := by
  filter_upwards [eventually_ge_atTop K] with n hKn
  intro T
  have hlift : Function.Injective (liftBinaryMolecule hKn) := by
    intro x z hxz
    rcases x with ⟨kx, wx⟩
    rcases z with ⟨kz, wz⟩
    have hkval : kx.val = kz.val :=
      congrArg (fun q : Molecule n => q.1.val) hxz
    have hk : kx = kz := Fin.ext hkval
    subst kz
    cases hxz
    rfl
  have hpair : (T : Set (SourceFixedSplitIndex K)).PairwiseDisjoint
      (sourceFixedSplitBlock K n) := by
    intro i hi j hj hij
    have hne : liftBinaryMolecule hKn i.1 ≠ liftBinaryMolecule hKn j.1 := by
      intro heq
      apply hij
      apply Subtype.ext
      exact hlift heq
    change Disjoint (sourceFixedSplitBlock K n i)
      (sourceFixedSplitBlock K n j)
    rw [sourceFixedSplitBlock, dif_pos hKn,
      sourceFixedSplitBlock, dif_pos hKn]
    exact sourceSplitBlock_disjoint hne
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sourceFixedSplitBlock, dif_pos hKn, card_sourceSplitBlock]
  rfl

noncomputable def sourceFixedSplitWindowWeight
    (a : ℝ) (K n : Nat) : ℝ :=
  sourceIndexedBlocksCoveredWeight a (sourceFixedSplitBlock K n)

def SourceFixedSplitWindowCovered (K n : Nat)
    (config : SourceMoleculeFibreConfig n) : Prop :=
  ∀ i : SourceFixedSplitIndex K,
    ¬ ∀ y : Molecule n,
      Disjoint (config y) (sourceFixedSplitBlock K n i)

local instance instDecidableSourceFixedSplitWindowCovered (K n : Nat) :
    DecidablePred (SourceFixedSplitWindowCovered K n) := Classical.decPred _

theorem sourceFixedSplitWindowWeight_eq_sum_if
    (a : ℝ) (K n : Nat) :
    sourceFixedSplitWindowWeight a K n =
      ∑ config : SourceMoleculeFibreConfig n,
        if SourceFixedSplitWindowCovered K n config then
          sourcePowerLawConfigWeight a n config else 0 := by
  classical
  rw [sourceFixedSplitWindowWeight, sourceIndexedBlocksCoveredWeight,
    allCoveredWeight]
  rw [show (Finset.univ : Finset (SourceFixedSplitIndex K)).inf
      (fun i => (sourceIndexedBlockMissEvent
        (sourceFixedSplitBlock K n) i)ᶜ) =
      (Finset.univ : Finset (SourceMoleculeFibreConfig n)).filter
        (SourceFixedSplitWindowCovered K n) by
    ext config
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_inf]
    constructor
    · intro h i
      have hi := h i trivial
      simpa [sourceIndexedBlockMissEvent] using hi
    · intro h i hi
      simpa [sourceIndexedBlockMissEvent] using h i]
  rw [Finset.sum_filter]

theorem sourceFixedSplitWindowCovered_and_noTail_imp_core
    {K n : Nat} (hKn : K ≤ n) (config : SourceMoleculeFibreConfig n)
    (hwindow : SourceFixedSplitWindowCovered K n config)
    (hnoTail : ¬ ∃ x : Molecule n, K < molLength x ∧
      ∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x)) :
    SourceCatalyzedSplitCore config := by
  rw [sourceCatalyzedSplitCore_iff_blocks]
  intro x hx
  have hhit : ¬ ∀ y : Molecule n,
      Disjoint (config y) (sourceSplitBlock x) := by
    by_cases hxlong : K < molLength x
    · intro hmiss
      exact hnoTail ⟨x, hxlong, hmiss⟩
    · rcases x with ⟨k, w⟩
      have hkK : k.val < K := by
        dsimp [molLength] at hxlong
        omega
      let xK : Molecule K := ⟨⟨k.val, hkK⟩, w⟩
      have hxKlen : 2 < molLength xK := by
        dsimp [xK, molLength]
        simpa only using hx
      let i : SourceFixedSplitIndex K := ⟨xK, hxKlen⟩
      have hi := hwindow i
      rw [sourceFixedSplitBlock, dif_pos hKn] at hi
      have hlift : liftBinaryMolecule hKn xK = ⟨k, w⟩ := by
        apply Sigma.ext
        · apply Fin.ext
          rfl
        · rfl
      rw [hlift] at hi
      exact hi
  push Not at hhit
  obtain ⟨y, hy⟩ := hhit
  obtain ⟨r, hry, hrx⟩ := Finset.not_disjoint_iff.mp hy
  exact ⟨r, hrx, y, hry⟩

local instance instDecidableSourceCatalyzedSplitCore (n : Nat) :
    DecidablePred (@SourceCatalyzedSplitCore n) := Classical.decPred _

noncomputable def sourceCatalyzedSplitCoreWeight (a : ℝ) (n : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if SourceCatalyzedSplitCore config then
      sourcePowerLawConfigWeight a n config else 0

theorem calibrated_sourceFixedSplitWindowWeight_tendsto
    (lam : ℝ) (hlam : 0 < lam) (K : Nat) :
    Tendsto (fun n : Nat => sourceFixedSplitWindowWeight
      (calibrationExponent lam hlam n) K n) atTop
      (𝓝 (∏ i : SourceFixedSplitIndex K,
        (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam))))) := by
  simpa [sourceFixedSplitWindowWeight] using
    calibrated_sourceIndexedBlocksCoveredWeight_tendsto_product
      lam hlam (sourceFixedSplitBlock K) sourceFixedSplitBlockSize
        (sourceFixedSplitBlock_card_eventually K)

theorem sourceFixedSplitWindowLimit_pos
    (lam : ℝ) (hlam : 0 < lam) (K : Nat) :
    0 < ∏ i : SourceFixedSplitIndex K,
      (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam))) := by
  apply Finset.prod_pos
  intro i hi
  apply sub_pos.mpr
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hsize : 0 < sourceFixedSplitBlockSize i := by
    dsimp [sourceFixedSplitBlockSize]
    omega
  exact neg_lt_zero.mpr (mul_pos (by exact_mod_cast hsize) hlam)

theorem sourceFixedSplitTailSum_eq_budget
    (lam : ℝ) {L K : Nat} (hL : 2 ≤ L) :
    (∑ i ∈ (Finset.univ : Finset (SourceFixedSplitIndex K)).filter
        (fun i => L < molLength i.1),
      Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam))) =
      sourceSplitTailBudget lam L K := by
  let s := (Finset.univ : Finset (SourceFixedSplitIndex K)).filter
    (fun i => L < molLength i.1)
  let t := (Finset.univ : Finset (Molecule K)).filter
    (fun x => L < molLength x)
  let emb : SourceFixedSplitIndex K ↪ Molecule K := Function.Embedding.subtype _
  have hmap : s.map emb = t := by
    ext x
    simp only [s, t, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, emb]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      let i : SourceFixedSplitIndex K := ⟨x, by omega⟩
      exact ⟨i, hx, rfl⟩
  calc
    (∑ i ∈ (Finset.univ : Finset (SourceFixedSplitIndex K)).filter
        (fun i => L < molLength i.1),
      Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam))) =
        ∑ x ∈ t, Real.exp (-((molLength x - 1 : Nat) : ℝ) * lam) := by
      rw [← hmap, Finset.sum_map]
      simp [s, emb, sourceFixedSplitBlockSize]
    _ = sourceSplitTailBudget lam L K := by
      rw [sourceSplitTailBudget]
      dsimp [t]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      ring_nf

theorem sourceFixedSplitTailProduct_ge_one_sub_budget
    (lam : ℝ) (hlam : 0 < lam) {L K : Nat} (hL : 2 ≤ L) :
    1 - sourceSplitTailBudget lam L K ≤
      ∏ i ∈ (Finset.univ : Finset (SourceFixedSplitIndex K)).filter
          (fun i => L < molLength i.1),
        (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam))) := by
  rw [← sourceFixedSplitTailSum_eq_budget lam hL]
  apply one_sub_sum_le_prod_one_sub
  · intro i hi
    positivity
  · intro i hi
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact (neg_nonpos.mpr (mul_nonneg (by positivity) hlam.le))

def sourceFixedSplitPrefixDowncast {L K : Nat}
    (i : {j : SourceFixedSplitIndex K // molLength j.1 ≤ L}) : Molecule L :=
  ⟨⟨i.1.1.1.val, by
      have hi := i.2
      dsimp [molLength] at hi
      omega⟩,
    i.1.1.2⟩

theorem sourceFixedSplitPrefixDowncast_injective {L K : Nat} :
    Function.Injective (@sourceFixedSplitPrefixDowncast L K) := by
  intro i j hij
  apply Subtype.ext
  apply Subtype.ext
  have hkval : i.1.1.1.val = j.1.1.1.val :=
    congrArg (fun x : Molecule L => x.1.val) hij
  apply Sigma.ext (Fin.ext hkval)
  dsimp [sourceFixedSplitPrefixDowncast] at hij
  exact (Sigma.mk.inj_iff.mp hij).2

theorem card_sourceFixedSplitPrefix_le (L K : Nat) :
    ((Finset.univ : Finset (SourceFixedSplitIndex K)).filter
      (fun i => molLength i.1 ≤ L)).card ≤ sourceMoleculeCount L := by
  have hcard : Fintype.card
      {j : SourceFixedSplitIndex K // molLength j.1 ≤ L} ≤
      Fintype.card (Molecule L) := Fintype.card_le_of_injective
    (@sourceFixedSplitPrefixDowncast L K)
    sourceFixedSplitPrefixDowncast_injective
  calc
    ((Finset.univ : Finset (SourceFixedSplitIndex K)).filter
        (fun i => molLength i.1 ≤ L)).card =
        Fintype.card {j : SourceFixedSplitIndex K // molLength j.1 ≤ L} := by
      rw [Fintype.card_subtype]
    _ ≤ Fintype.card (Molecule L) := hcard
    _ = sourceMoleculeCount L := card_binaryMolecule_eq_sourceMoleculeCount L

noncomputable def sourceSplitMinFactor (lam : ℝ) : ℝ :=
  1 - Real.exp (-2 * lam)

theorem sourceSplitMinFactor_pos {lam : ℝ} (hlam : 0 < lam) :
    0 < sourceSplitMinFactor lam := by
  rw [sourceSplitMinFactor, sub_pos, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem sourceSplitMinFactor_le_one (lam : ℝ) :
    sourceSplitMinFactor lam ≤ 1 := by
  dsimp [sourceSplitMinFactor]
  have hexp := Real.exp_pos (-2 * lam)
  linarith

theorem sourceSplitMinFactor_le_factor
    {lam : ℝ} (hlam : 0 < lam) {K : Nat}
    (i : SourceFixedSplitIndex K) :
    sourceSplitMinFactor lam ≤
      1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam)) := by
  have hsize : 2 ≤ sourceFixedSplitBlockSize i := by
    dsimp [sourceFixedSplitBlockSize]
    omega
  have hcast : (2 : ℝ) ≤ (sourceFixedSplitBlockSize i : ℝ) := by
    exact_mod_cast hsize
  dsimp [sourceSplitMinFactor]
  gcongr
  nlinarith

/-- The limiting probability of covering every split block through `K` has a
positive lower bound depending only on a shorter cutoff `L`, provided the
geometric tail beyond `L` costs at most one half. -/
theorem sourceFixedSplitLimitProduct_uniform_lower
    (lam : ℝ) (hlam : 0 < lam) (hlam2 : Real.log 2 < lam)
    {L : Nat} (hL : 2 ≤ L)
    (htail : 2 * sourceSplitTailRatio lam ^ L /
        (1 - sourceSplitTailRatio lam) ≤ (1 : ℝ) / 2)
    (K : Nat) :
    sourceSplitMinFactor lam ^ sourceMoleculeCount L / 2 ≤
      ∏ i : SourceFixedSplitIndex K,
        (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam))) := by
  classical
  let f : SourceFixedSplitIndex K → ℝ := fun i =>
    1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam))
  let S : Finset (SourceFixedSplitIndex K) :=
    Finset.univ.filter (fun i => molLength i.1 ≤ L)
  let T : Finset (SourceFixedSplitIndex K) :=
    Finset.univ.filter (fun i => L < molLength i.1)
  have hb0 : 0 ≤ sourceSplitMinFactor lam :=
    (sourceSplitMinFactor_pos hlam).le
  have hb1 : sourceSplitMinFactor lam ≤ 1 :=
    sourceSplitMinFactor_le_one lam
  have hScard : S.card ≤ sourceMoleculeCount L := by
    exact card_sourceFixedSplitPrefix_le L K
  have hSpow : sourceSplitMinFactor lam ^ sourceMoleculeCount L ≤
      sourceSplitMinFactor lam ^ S.card :=
    pow_le_pow_of_le_one hb0 hb1 hScard
  have hSprod : sourceSplitMinFactor lam ^ S.card ≤ ∏ i ∈ S, f i := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro i hi
      exact hb0
    · intro i hi
      exact sourceSplitMinFactor_le_factor hlam i
  have hprefix : sourceSplitMinFactor lam ^ sourceMoleculeCount L ≤
      ∏ i ∈ S, f i := hSpow.trans hSprod
  have hprefix0 : 0 ≤ ∏ i ∈ S, f i :=
    (pow_nonneg hb0 _).trans hprefix
  have hbudget : sourceSplitTailBudget lam L K ≤ (1 : ℝ) / 2 :=
    (sourceSplitTailBudget_le_geometric hlam2 L K).trans htail
  have htailprod : (1 : ℝ) / 2 ≤ ∏ i ∈ T, f i := by
    have hprod := sourceFixedSplitTailProduct_ge_one_sub_budget lam hlam hL
      (K := K)
    change 1 - sourceSplitTailBudget lam L K ≤ ∏ i ∈ T, f i at hprod
    linarith
  have hpartition : (∏ i ∈ S, f i) * (∏ i ∈ T, f i) =
      ∏ i : SourceFixedSplitIndex K, f i := by
    rw [show T = Finset.univ.filter
        (fun i : SourceFixedSplitIndex K => ¬ molLength i.1 ≤ L) by
      ext i
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      omega]
    exact Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i : SourceFixedSplitIndex K => molLength i.1 ≤ L) f
  calc
    sourceSplitMinFactor lam ^ sourceMoleculeCount L / 2 =
        sourceSplitMinFactor lam ^ sourceMoleculeCount L * ((1 : ℝ) / 2) := by
      ring
    _ ≤ (∏ i ∈ S, f i) * (∏ i ∈ T, f i) := by
      exact mul_le_mul hprefix htailprod (by norm_num)
        hprefix0
    _ = ∏ i : SourceFixedSplitIndex K, f i := hpartition
    _ = ∏ i : SourceFixedSplitIndex K,
        (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam))) := rfl

theorem sourceSplitGeometricTail_tendsto_zero
    {c : ℝ} (hc : Real.log 2 < c) :
    Tendsto (fun K : Nat => 2 * sourceSplitTailRatio c ^ K /
      (1 - sourceSplitTailRatio c)) atTop (nhds 0) := by
  have hpow : Tendsto (fun K : Nat => sourceSplitTailRatio c ^ K)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (sourceSplitTailRatio_nonneg c) (sourceSplitTailRatio_lt_one hc)
  simpa using (hpow.const_mul 2).div_const (1 - sourceSplitTailRatio c)

theorem exists_sourceSplitGeometricTail_le
    {c eps : ℝ} (hc : Real.log 2 < c) (heps : 0 < eps) (K₀ : Nat) :
    ∃ K ≥ K₀, 2 * sourceSplitTailRatio c ^ K /
      (1 - sourceSplitTailRatio c) ≤ eps := by
  have hsmall : ∀ᶠ K : Nat in atTop,
      2 * sourceSplitTailRatio c ^ K /
        (1 - sourceSplitTailRatio c) < eps :=
    (tendsto_order.1 (sourceSplitGeometricTail_tendsto_zero hc)).2 eps heps
  have hboth : ∀ᶠ K : Nat in atTop, K₀ ≤ K ∧
      2 * sourceSplitTailRatio c ^ K /
        (1 - sourceSplitTailRatio c) ≤ eps := by
    filter_upwards [eventually_ge_atTop K₀, hsmall] with K hK hs
    exact ⟨hK, hs.le⟩
  exact hboth.exists

/-- Source mass of configurations missing at least one split block above the
fixed word-length cutoff `K`. -/
noncomputable def sourceSplitTailMissWeight
    (a : ℝ) (K n : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if ∃ x : Molecule n, K < molLength x ∧
        ∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x) then
      sourcePowerLawConfigWeight a n config
    else 0

theorem sourceSplitTailMissWeight_le_sum
    (a : ℝ) (ha : 1 < a) {n : Nat} (hn : 4 ≤ n) (K : Nat) :
    sourceSplitTailMissWeight a K n ≤
      ∑ x : Molecule n,
        if K < molLength x then
          coverageMissProfile (cappedZipfDegreeMass a (sourceReactionCount n))
              (sourceReactionCount n) (molLength x - 1) ^
            sourceMoleculeCount n
        else 0 := by
  rw [sourceSplitTailMissWeight]
  calc
    (∑ config : SourceMoleculeFibreConfig n,
      if ∃ x : Molecule n, K < molLength x ∧
          ∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x) then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ config : SourceMoleculeFibreConfig n,
        ∑ x : Molecule n,
          if K < molLength x then
            if ∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x) then
              sourcePowerLawConfigWeight a n config else 0
          else 0 := by
      apply Finset.sum_le_sum
      intro config hconfig
      by_cases hex : ∃ x : Molecule n, K < molLength x ∧
          ∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x)
      · rw [if_pos hex]
        obtain ⟨x, hxK, hxmiss⟩ := hex
        calc
          sourcePowerLawConfigWeight a n config =
              (if K < molLength x then
                if ∀ y : Molecule n,
                    Disjoint (config y) (sourceSplitBlock x) then
                  sourcePowerLawConfigWeight a n config else 0
                else 0) := by simp [hxK, hxmiss]
          _ ≤ ∑ z : Molecule n,
              if K < molLength z then
                if ∀ y : Molecule n,
                    Disjoint (config y) (sourceSplitBlock z) then
                  sourcePowerLawConfigWeight a n config else 0
                else 0 := by
            have hs := Finset.single_le_sum
              (s := (Finset.univ : Finset (Molecule n)))
              (f := fun z : Molecule n =>
                if K < molLength z then
                  if ∀ y : Molecule n,
                      Disjoint (config y) (sourceSplitBlock z) then
                    sourcePowerLawConfigWeight a n config else 0
                  else 0)
              (fun z hz => by
                dsimp
                split_ifs
                · exact sourcePowerLawConfigWeight_nonneg a n ha config
                · exact le_rfl
                · exact le_rfl)
              (Finset.mem_univ x)
            exact hs
      · rw [if_neg hex]
        apply Finset.sum_nonneg
        intro x hx
        split_ifs
        · exact sourcePowerLawConfigWeight_nonneg a n ha config
        · exact le_rfl
        · exact le_rfl
    _ = ∑ x : Molecule n,
        if K < molLength x then
          ∑ config : SourceMoleculeFibreConfig n,
            if ∀ y : Molecule n,
                Disjoint (config y) (sourceSplitBlock x) then
              sourcePowerLawConfigWeight a n config else 0
        else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp
    _ = ∑ x : Molecule n,
        if K < molLength x then
          coverageMissProfile (cappedZipfDegreeMass a (sourceReactionCount n))
              (sourceReactionCount n) (molLength x - 1) ^
            sourceMoleculeCount n
        else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs with hK
      · rw [source_splitBlock_jointMiss_mass a ha hn x]
      · rfl

theorem eventually_calibrated_sourceSplitTailMissWeight_le_budget
    (lam c : ℝ) (hlam : 0 < lam) (hc : c < lam) (K : Nat) (hK : 1 ≤ K) :
    ∀ᶠ n : Nat in atTop,
      sourceSplitTailMissWeight (calibrationExponent lam hlam n) K n ≤
        sourceSplitTailBudget c K n := by
  have hmiss := eventually_calibrated_splitBlockMiss_le_exp lam c hlam hc
  have ha : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  filter_upwards [eventually_ge_atTop 16, hmiss, ha] with n hn hmn han
  calc
    sourceSplitTailMissWeight (calibrationExponent lam hlam n) K n ≤
        ∑ x : Molecule n,
          if K < molLength x then
            coverageMissProfile
                (cappedZipfDegreeMass (calibrationExponent lam hlam n)
                  (sourceReactionCount n))
                (sourceReactionCount n) (molLength x - 1) ^
              sourceMoleculeCount n
          else 0 := sourceSplitTailMissWeight_le_sum
            (calibrationExponent lam hlam n) han (by omega) K
    _ ≤ sourceSplitTailBudget c K n := by
      rw [sourceSplitTailBudget]
      apply Finset.sum_le_sum
      intro x hx
      split_ifs with hxK
      · apply hmn (molLength x - 1)
        · omega
        · rcases x with ⟨k, w⟩
          dsimp [molLength]
          omega
      · exact le_rfl

theorem eventually_calibrated_sourceSplitTailMissWeight_le_geometric
    (lam c : ℝ) (hlam : 0 < lam)
    (hc2 : Real.log 2 < c) (hclam : c < lam)
    (K : Nat) (hK : 1 ≤ K) :
    ∀ᶠ n : Nat in atTop,
      sourceSplitTailMissWeight (calibrationExponent lam hlam n) K n ≤
        2 * sourceSplitTailRatio c ^ K /
          (1 - sourceSplitTailRatio c) := by
  filter_upwards [eventually_calibrated_sourceSplitTailMissWeight_le_budget
    lam c hlam hclam K hK] with n hn
  exact hn.trans (sourceSplitTailBudget_le_geometric hc2 K n)

/-- A fixed window can fail to extend to the full macro core only through one
of the explicitly charged tail miss events. -/
theorem sourceFixedWindow_sub_tail_le_core
    (a : ℝ) (ha : 1 < a) {K n : Nat} (hKn : K ≤ n) :
    sourceFixedSplitWindowWeight a K n - sourceSplitTailMissWeight a K n ≤
      sourceCatalyzedSplitCoreWeight a n := by
  rw [sourceFixedSplitWindowWeight_eq_sum_if, sourceSplitTailMissWeight,
    sourceCatalyzedSplitCoreWeight, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro config hconfig
  let tailMiss : Prop := ∃ x : Molecule n, K < molLength x ∧
    ∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x)
  by_cases hw : SourceFixedSplitWindowCovered K n config
  · by_cases ht : tailMiss
    · dsimp [tailMiss] at ht
      simp only [if_pos hw, if_pos ht]
      have hweight := sourcePowerLawConfigWeight_nonneg a n ha config
      split_ifs <;> linarith
    · dsimp [tailMiss] at ht
      have hcore : SourceCatalyzedSplitCore config :=
        sourceFixedSplitWindowCovered_and_noTail_imp_core hKn config hw ht
      simp [hw, ht, hcore]
  · simp only [if_neg hw, zero_sub]
    split_ifs
    all_goals
      have hweight := sourcePowerLawConfigWeight_nonneg a n ha config
      linarith

theorem eventually_calibrated_sourceCatalyzedSplitCoreWeight_pos_of_gap
    (lam c : ℝ) (hlam : 0 < lam)
    (hc2 : Real.log 2 < c) (hclam : c < lam)
    (K : Nat) (hK : 1 ≤ K)
    (hgap : 2 * sourceSplitTailRatio c ^ K /
        (1 - sourceSplitTailRatio c) <
      ∏ i : SourceFixedSplitIndex K,
        (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam)))) :
    ∀ᶠ n : Nat in atTop,
      0 < sourceCatalyzedSplitCoreWeight
        (calibrationExponent lam hlam n) n := by
  let P : ℝ := ∏ i : SourceFixedSplitIndex K,
    (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam)))
  let B : ℝ := 2 * sourceSplitTailRatio c ^ K /
    (1 - sourceSplitTailRatio c)
  have hmid : (P + B) / 2 < P := by dsimp [P, B]; linarith
  have hwindow : ∀ᶠ n : Nat in atTop,
      (P + B) / 2 < sourceFixedSplitWindowWeight
        (calibrationExponent lam hlam n) K n :=
    (calibrated_sourceFixedSplitWindowWeight_tendsto lam hlam K)
      (Ioi_mem_nhds hmid)
  have htail := eventually_calibrated_sourceSplitTailMissWeight_le_geometric
    lam c hlam hc2 hclam K hK
  have ha : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  filter_upwards [eventually_ge_atTop K, hwindow, htail, ha] with
    n hKn hnwindow hntail han
  have hcore := sourceFixedWindow_sub_tail_le_core
    (calibrationExponent lam hlam n) han hKn
  dsimp [P, B] at hnwindow hntail ⊢
  linarith

/-- Quantitative form of the fixed-window/tail argument: a strict limiting
gap supplies a fixed positive lower bound, not merely pointwise positivity. -/
theorem eventually_calibrated_sourceCatalyzedSplitCoreWeight_ge_of_gap
    (lam c : ℝ) (hlam : 0 < lam)
    (hc2 : Real.log 2 < c) (hclam : c < lam)
    (K : Nat) (hK : 1 ≤ K)
    (hgap : 2 * sourceSplitTailRatio c ^ K /
        (1 - sourceSplitTailRatio c) <
      ∏ i : SourceFixedSplitIndex K,
        (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam)))) :
    ∀ᶠ n : Nat in atTop,
      ((∏ i : SourceFixedSplitIndex K,
          (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam)))) -
        2 * sourceSplitTailRatio c ^ K /
          (1 - sourceSplitTailRatio c)) / 2 ≤
      sourceCatalyzedSplitCoreWeight
        (calibrationExponent lam hlam n) n := by
  let P : ℝ := ∏ i : SourceFixedSplitIndex K,
    (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam)))
  let B : ℝ := 2 * sourceSplitTailRatio c ^ K /
    (1 - sourceSplitTailRatio c)
  have hmid : (P + B) / 2 < P := by dsimp [P, B]; linarith
  have hwindow : ∀ᶠ n : Nat in atTop,
      (P + B) / 2 < sourceFixedSplitWindowWeight
        (calibrationExponent lam hlam n) K n :=
    (calibrated_sourceFixedSplitWindowWeight_tendsto lam hlam K)
      (Ioi_mem_nhds hmid)
  have htail := eventually_calibrated_sourceSplitTailMissWeight_le_geometric
    lam c hlam hc2 hclam K hK
  have ha : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  filter_upwards [eventually_ge_atTop K, hwindow, htail, ha] with
    n hKn hnwindow hntail han
  have hcore := sourceFixedWindow_sub_tail_le_core
    (calibrationExponent lam hlam n) han hKn
  dsimp [P, B] at hnwindow hntail ⊢
  linarith

/-- Above the entropy threshold `log 2`, the complete catalyzed split core has
probability bounded below by a fixed positive constant along the calibrated
power-law model. -/
theorem calibrated_sourceCatalyzedSplitCoreWeight_eventually_ge_pos
    (lam : ℝ) (hlam2 : Real.log 2 < lam) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : Nat in atTop,
      δ ≤ sourceCatalyzedSplitCoreWeight
        (calibrationExponent lam
          (lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hlam2) n) n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlam : 0 < lam := hlog2.trans hlam2
  let c : ℝ := (Real.log 2 + lam) / 2
  have hc2 : Real.log 2 < c := by dsimp [c]; linarith
  have hclam : c < lam := by dsimp [c]; linarith
  obtain ⟨L, hL, hLtail⟩ :=
    exists_sourceSplitGeometricTail_le hlam2 (by norm_num : (0 : ℝ) < 1 / 2) 2
  let A : ℝ := sourceSplitMinFactor lam ^ sourceMoleculeCount L / 2
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (pow_pos (sourceSplitMinFactor_pos hlam) _) (by norm_num)
  obtain ⟨K, hK, hKtail⟩ :=
    exists_sourceSplitGeometricTail_le hc2 (half_pos hA) 1
  let P : ℝ := ∏ i : SourceFixedSplitIndex K,
    (1 - Real.exp (-((sourceFixedSplitBlockSize i : ℝ) * lam)))
  let B : ℝ := 2 * sourceSplitTailRatio c ^ K /
    (1 - sourceSplitTailRatio c)
  have hAP : A ≤ P := by
    exact sourceFixedSplitLimitProduct_uniform_lower lam hlam hlam2 hL hLtail K
  have hBA : B ≤ A / 2 := hKtail
  have hgap : B < P := by linarith
  let δ : ℝ := (P - B) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨δ, hδ, ?_⟩
  simpa [δ, P, B] using
    (eventually_calibrated_sourceCatalyzedSplitCoreWeight_ge_of_gap
      lam c hlam hc2 hclam K hK (by simpa [P, B] using hgap))

end

end PowerLawSmallRAF
