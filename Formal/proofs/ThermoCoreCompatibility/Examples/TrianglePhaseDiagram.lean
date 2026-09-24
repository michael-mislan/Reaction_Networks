import proofs.ThermoCoreCompatibility.Examples.MagnitudeObstructionPair

/-! Exact barrier phase diagram for the two interacting autocatalytic
triangles. The right private barriers are the positive parameter `k`. -/

namespace ThermoCoreCompatibility.TrianglePhaseDiagram

open scoped BigOperators
open ThermoCoreCompatibility
open MagnitudePair

def barrierAt (k : ℝ) (r : Reaction) : ℝ := if r.val < 3 then 1 else k

theorem barrierAt_pos (k : ℝ) (hk : 0 < k) (r : Reaction) :
    0 < barrierAt k r := by
  fin_cases r <;> simp [barrierAt, hk]

def networkAt (k : ℝ) (hk : 0 < k) : ReversibleCRN Species Reaction where
  reactant := reactant
  product := product
  barrier := barrierAt k
  barrier_pos := barrierAt_pos k hk

def leftMotifAt (k : ℝ) (hk : 0 < k) : Motif (networkAt k hk) where
  species := {.A, .B, .C}
  reactions := {.r0, .r1, .r2}

def rightMotifAt (k : ℝ) (hk : 0 < k) : Motif (networkAt k hk) where
  species := {.A, .B, .D}
  reactions := {.r0, .r3, .r4}

/-- The literal common thermodynamic realization predicate for the two cores.
It is the specialization of `MultiCAC` to their common forward orientation;
PAC minimality is already barrier-independent and proved for the fixed fixture. -/
def PairMultiCAC (k : ℝ) (hk : 0 < k) : Prop :=
  ∃ z : Species → ℝ,
    (∀ s, 0 < z s) ∧
    (∀ r, 0 < (networkAt k hk).current z r) ∧
    (leftMotifAt k hk).Productive ((networkAt k hk).current z) ∧
    (rightMotifAt k hk).Productive ((networkAt k hk).current z)

private theorem sum_left_at {M : Type*} [AddCommMonoid M] (f : Reaction → M) :
    ∑ r ∈ ({.r0, .r1, .r2} : Finset Reaction), f r = f .r0 + f .r1 + f .r2 := by
  simp [Finset.sum_insert, add_assoc]

private theorem sum_right_at {M : Type*} [AddCommMonoid M] (f : Reaction → M) :
    ∑ r ∈ ({.r0, .r3, .r4} : Finset Reaction), f r = f .r0 + f .r3 + f .r4 := by
  simp [Finset.sum_insert, add_assoc]

theorem pairMultiCAC_onlyIf_window (k : ℝ) (hk : 0 < k) :
    PairMultiCAC k hk → 1 / 2 < k ∧ k < 2 := by
  rintro ⟨z, _hz, hcurrent, hL, hR⟩
  have hj0 := hcurrent Reaction.r0
  have hLA := hL .A (by simp [leftMotifAt])
  have hLB := hL .B (by simp [leftMotifAt])
  have hLC := hL .C (by simp [leftMotifAt])
  have hRA := hR .A (by simp [rightMotifAt])
  have hRB := hR .B (by simp [rightMotifAt])
  have hRD := hR .D (by simp [rightMotifAt])
  simp only [leftMotifAt] at hLA hLB hLC
  simp only [rightMotifAt] at hRA hRB hRD
  rw [sum_left_at] at hLA hLB hLC
  rw [sum_right_at] at hRA hRB hRD
  norm_num [networkAt, ReversibleCRN.stoich, reactant, product,
    ReversibleCRN.current, ReversibleCRN.complexActivity, barrierAt,
    Fin.prod_univ_succ] at hj0 hLA hLB hLC hRA hRB hRD
  let j : ℝ := z .A - z .B
  let x : ℝ := z .B - z .A ^ 2
  have hj : 0 < j := by simpa [j] using hj0
  have hx_lower : j < x := by
    dsimp [j, x]
    nlinarith
  have hx_upper : x < 2 * j := by
    dsimp [j, x]
    nlinarith
  have hkx_lower : j < k * x := by
    dsimp [j, x]
    nlinarith
  have hkx_upper : k * x < 2 * j := by
    dsimp [j, x]
    nlinarith
  have hx : 0 < x := lt_trans hj hx_lower
  constructor
  · by_contra h
    have hkle : k ≤ 1 / 2 := le_of_not_gt h
    have hmul : k * x ≤ (1 / 2 : ℝ) * x :=
      mul_le_mul_of_nonneg_right hkle (le_of_lt hx)
    linarith
  · by_contra h
    have hkge : 2 ≤ k := le_of_not_gt h
    have hmul : (2 : ℝ) * x ≤ k * x :=
      mul_le_mul_of_nonneg_right hkge (le_of_lt hx)
    linarith

noncomputable def splitDelta (p : ℝ) : ℝ := (p - 1) * (2 - p) / 4
noncomputable def splitUpper (p : ℝ) : ℝ := p / 2 + splitDelta p
noncomputable def splitLower (p : ℝ) : ℝ := p / 2 - splitDelta p

theorem split_properties {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    1 / 2 < splitLower p ∧ splitLower p < splitUpper p ∧
      splitUpper p < 1 ∧ splitUpper p + splitLower p = p := by
  have ha : 0 < p - 1 := by linarith
  have hb : 0 < 2 - p := by linarith
  have hab : 0 < (p - 1) * (2 - p) := mul_pos ha hb
  have hba : (p - 1) * (2 - p) < 2 * (p - 1) := by
    nlinarith [mul_lt_mul_of_pos_left (show 2 - p < 2 by linarith) ha]
  have hab' : (p - 1) * (2 - p) < 2 * (2 - p) := by
    nlinarith [mul_lt_mul_of_pos_right (show p - 1 < 2 by linarith) hb]
  constructor
  · dsimp [splitLower, splitDelta]
    linarith
  constructor
  · dsimp [splitLower, splitUpper, splitDelta]
    linarith
  constructor
  · dsimp [splitUpper, splitDelta]
    linarith
  · dsimp [splitUpper, splitLower]
    ring

noncomputable def qOf (k : ℝ) : ℝ := 3 / (1 + k)

theorem q_window {k : ℝ} (hklo : 1 / 2 < k) (hkhi : k < 2) :
    1 < qOf k ∧ qOf k < 2 ∧ 1 < k * qOf k ∧ k * qOf k < 2 := by
  have hk : 0 < k := by linarith
  have hd : 0 < 1 + k := by linarith
  have hq1 : 1 < qOf k := by
    apply (lt_div_iff₀ hd).2
    dsimp [qOf]
    linarith
  have hq2 : qOf k < 2 := by
    apply (div_lt_iff₀ hd).2
    dsimp [qOf]
    linarith
  have hrewrite : k * qOf k = (3 * k) / (1 + k) := by
    dsimp [qOf]
    field_simp
  have hp1 : 1 < k * qOf k := by
    rw [hrewrite]
    apply (lt_div_iff₀ hd).2
    nlinarith
  have hp2 : k * qOf k < 2 := by
    rw [hrewrite]
    apply (div_lt_iff₀ hd).2
    nlinarith
  exact ⟨hq1, hq2, hp1, hp2⟩

/- Monolithic construction retained as a diagnostic record; the compiled proof
below factors its scalar and source-level obligations into separate lemmas.
theorem window_implies_pairMultiCAC (k : ℝ) (hk : 0 < k)
    (hklo : 1 / 2 < k) (hkhi : k < 2) : PairMultiCAC k hk := by
  rcases q_window hklo hkhi with ⟨hq1, hq2, hp1, hp2⟩
  let q : ℝ := qOf k
  let p : ℝ := k * q
  let uL : ℝ := splitUpper q
  let vL : ℝ := splitLower q
  let uR : ℝ := splitUpper p
  let vR : ℝ := splitLower p
  have hq1' : 1 < q := by simpa [q] using hq1
  have hq2' : q < 2 := by simpa [q] using hq2
  have hp1' : 1 < p := by simpa [p, q] using hp1
  have hp2' : p < 2 := by simpa [p, q] using hp2
  rcases split_properties hq1' hq2' with ⟨hvLhalf, hvLuL, huLone, hsumL⟩
  rcases split_properties hp1' hp2' with ⟨hvRhalf, hvRuR, huRone, hsumR⟩
  change 1 / 2 < vL at hvLhalf
  change vL < uL at hvLuL
  change uL < 1 at huLone
  change uL + vL = q at hsumL
  change 1 / 2 < vR at hvRhalf
  change vR < uR at hvRuR
  change uR < 1 at huRone
  change uR + vR = p at hsumR
  let j : ℝ := 1 / (4 * (q + 1))
  let a : ℝ := 1 / 2
  let b : ℝ := a - j
  let c : ℝ := b - uL * j
  let d : ℝ := b - (uR * j) / k
  let z : Species → ℝ := fun s =>
    match s.val with
    | 0 => a
    | 1 => b
    | 2 => c
    | _ => d
  have hj : 0 < j := by
    dsimp [j]
    positivity
  have hjEq : 4 * (q + 1) * j = 1 := by
    dsimp [j]
    field_simp
  have hjSmall : j < 1 / 8 := by
    nlinarith [mul_pos (show 0 < q - 1 by linarith) hj]
  have ha : 0 < a := by norm_num [a]
  have hb : 0 < b := by dsimp [b, a]; linarith
  have hBdrop : b - a ^ 2 = q * j := by
    dsimp [b, a]
    nlinarith
  have huLj : uL * j < j := by
    simpa using mul_lt_mul_of_pos_right huLone hj
  have hc : 0 < c := by
    dsimp [c, b, a]
    linarith
  have huRp : uR < p := by linarith
  have huRq : uR / k < q := by
    apply (div_lt_iff₀ hk).2
    simpa [p, mul_comm] using huRp
  have hd : 0 < d := by
    have hmul : (uR / k) * j < q * j :=
      mul_lt_mul_of_pos_right huRq hj
    dsimp [d]
    rw [div_mul_eq_mul_div] at hmul
    nlinarith
  have hj0 : a - b = j := by simp [b]
  have hj1 : b - c = uL * j := by simp [c]
  have hj2 : c - a ^ 2 = vL * j := by
    dsimp [c]
    nlinarith
  have hj3 : k * (b - d) = uR * j := by
    dsimp [d]
    field_simp
    ring
  have hj4 : k * (d - a ^ 2) = vR * j := by
    calc
      k * (d - a ^ 2) = k * (b - a ^ 2) - uR * j := by
        dsimp [d]
        field_simp
        ring
      _ = k * (q * j) - uR * j := by rw [hBdrop]
      _ = (k * q - uR) * j := by ring
      _ = vR * j := by
        congr 1
        dsimp [p] at hsumR
        linarith
  have hcur0 : (networkAt k hk).current z .r0 = j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact hj0
  have hcur1 : (networkAt k hk).current z .r1 = uL * j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact hj1
  have hcur2 : (networkAt k hk).current z .r2 = vL * j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact hj2
  have hcur3 : (networkAt k hk).current z .r3 = uR * j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact hj3
  have hcur4 : (networkAt k hk).current z .r4 = vR * j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact hj4
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro s
    fin_cases s
    · simpa [z] using ha
    · simpa [z] using hb
    · simpa [z] using hc
    · simpa [z] using hd
  · intro r
    fin_cases r
    · rw [hcur0]; exact hj
    · rw [hcur1]; exact mul_pos (by linarith) hj
    · rw [hcur2]; exact mul_pos (by linarith) hj
    · rw [hcur3]; exact mul_pos (by linarith) hj
    · rw [hcur4]; exact mul_pos (by linarith) hj
  · intro s hs
    fin_cases s
    · simp only [leftMotifAt]; rw [sum_left_at, hcur0, hcur1, hcur2]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      nlinarith [mul_pos (show 0 < vL by linarith) hj]
    · simp only [leftMotifAt]; rw [sum_left_at, hcur0, hcur1, hcur2]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      nlinarith [mul_pos (show 0 < uL - vL by linarith) hj]
    · simp only [leftMotifAt]; rw [sum_left_at, hcur0, hcur1, hcur2]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      nlinarith [mul_pos (show 0 < uL - vL by linarith) hj]
    · simp [leftMotifAt] at hs
  · intro s hs
    fin_cases s
    · simp only [rightMotifAt]; rw [sum_right_at, hcur0, hcur3, hcur4]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      nlinarith [mul_pos (show 0 < vR by linarith) hj]
    · simp only [rightMotifAt]; rw [sum_right_at, hcur0, hcur3, hcur4]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      nlinarith [mul_pos (show 0 < uR - vR by linarith) hj]
    · simp [rightMotifAt] at hs
    · simp only [rightMotifAt]; rw [sum_right_at, hcur0, hcur3, hcur4]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      nlinarith [mul_pos (show 0 < uR - vR by linarith) hj]

theorem pairMultiCAC_iff_window (k : ℝ) (hk : 0 < k) :
    PairMultiCAC k hk ↔ 1 / 2 < k ∧ k < 2 := by
  constructor
  · exact pairMultiCAC_onlyIf_window k hk
  · rintro ⟨hklo, hkhi⟩
    exact window_implies_pairMultiCAC k hk hklo hkhi
-/

structure PairData (k : ℝ) where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  j : ℝ
  uL : ℝ
  vL : ℝ
  uR : ℝ
  vR : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  d_pos : 0 < d
  j_pos : 0 < j
  vL_half : 1 / 2 < vL
  vL_lt_uL : vL < uL
  uL_lt_one : uL < 1
  vR_half : 1 / 2 < vR
  vR_lt_uR : vR < uR
  uR_lt_one : uR < 1
  current0 : a - b = j
  current1 : b - c = uL * j
  current2 : c - a ^ 2 = vL * j
  current3 : k * (b - d) = uR * j
  current4 : k * (d - a ^ 2) = vR * j

theorem pairMultiCAC_of_data (k : ℝ) (hk : 0 < k) (W : PairData k) :
    PairMultiCAC k hk := by
  let z : Species → ℝ := fun s =>
    match s.val with
    | 0 => W.a
    | 1 => W.b
    | 2 => W.c
    | _ => W.d
  have hcur0 : (networkAt k hk).current z .r0 = W.j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact W.current0
  have hcur1 : (networkAt k hk).current z .r1 = W.uL * W.j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact W.current1
  have hcur2 : (networkAt k hk).current z .r2 = W.vL * W.j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact W.current2
  have hcur3 : (networkAt k hk).current z .r3 = W.uR * W.j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact W.current3
  have hcur4 : (networkAt k hk).current z .r4 = W.vR * W.j := by
    norm_num [networkAt, ReversibleCRN.current, ReversibleCRN.complexActivity,
      barrierAt, reactant, product, z, Fin.prod_univ_succ]
    exact W.current4
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro s
    fin_cases s
    · simpa [z] using W.a_pos
    · simpa [z] using W.b_pos
    · simpa [z] using W.c_pos
    · simpa [z] using W.d_pos
  · intro r
    fin_cases r
    · change 0 < (networkAt k hk).current z .r0
      rw [hcur0]; exact W.j_pos
    · change 0 < (networkAt k hk).current z .r1
      rw [hcur1]; exact mul_pos (by linarith [W.vL_half, W.vL_lt_uL]) W.j_pos
    · change 0 < (networkAt k hk).current z .r2
      rw [hcur2]; exact mul_pos (by linarith [W.vL_half]) W.j_pos
    · change 0 < (networkAt k hk).current z .r3
      rw [hcur3]; exact mul_pos (by linarith [W.vR_half, W.vR_lt_uR]) W.j_pos
    · change 0 < (networkAt k hk).current z .r4
      rw [hcur4]; exact mul_pos (by linarith [W.vR_half]) W.j_pos
  · intro s hs
    fin_cases s
    · simp only [leftMotifAt]; rw [sum_left_at, hcur0, hcur1, hcur2]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      have := mul_lt_mul_of_pos_right W.vL_half W.j_pos
      nlinarith
    · simp only [leftMotifAt]; rw [sum_left_at, hcur0, hcur1, hcur2]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      have := mul_lt_mul_of_pos_right W.uL_lt_one W.j_pos
      nlinarith
    · simp only [leftMotifAt]; rw [sum_left_at, hcur0, hcur1, hcur2]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      have := mul_lt_mul_of_pos_right W.vL_lt_uL W.j_pos
      nlinarith
    · simp [leftMotifAt] at hs
  · intro s hs
    fin_cases s
    · simp only [rightMotifAt]; rw [sum_right_at, hcur0, hcur3, hcur4]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      have := mul_lt_mul_of_pos_right W.vR_half W.j_pos
      nlinarith
    · simp only [rightMotifAt]; rw [sum_right_at, hcur0, hcur3, hcur4]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      have := mul_lt_mul_of_pos_right W.uR_lt_one W.j_pos
      nlinarith
    · simp [rightMotifAt] at hs
    · simp only [rightMotifAt]; rw [sum_right_at, hcur0, hcur3, hcur4]
      norm_num [networkAt, ReversibleCRN.stoich, reactant, product]
      have := mul_lt_mul_of_pos_right W.vR_lt_uR W.j_pos
      nlinarith

theorem window_has_pairData (k : ℝ) (hk : 0 < k)
    (hklo : 1 / 2 < k) (hkhi : k < 2) : Nonempty (PairData k) := by
  rcases q_window hklo hkhi with ⟨hq1, hq2, hp1, hp2⟩
  let q : ℝ := qOf k
  let p : ℝ := k * q
  let uL : ℝ := splitUpper q
  let vL : ℝ := splitLower q
  let uR : ℝ := splitUpper p
  let vR : ℝ := splitLower p
  have hq1' : 1 < q := by simpa [q] using hq1
  have hq2' : q < 2 := by simpa [q] using hq2
  have hp1' : 1 < p := by simpa [p, q] using hp1
  have hp2' : p < 2 := by simpa [p, q] using hp2
  rcases split_properties hq1' hq2' with ⟨hvLhalf, hvLuL, huLone, hsumL⟩
  rcases split_properties hp1' hp2' with ⟨hvRhalf, hvRuR, huRone, hsumR⟩
  change 1 / 2 < vL at hvLhalf
  change vL < uL at hvLuL
  change uL < 1 at huLone
  change uL + vL = q at hsumL
  change 1 / 2 < vR at hvRhalf
  change vR < uR at hvRuR
  change uR < 1 at huRone
  change uR + vR = p at hsumR
  let j : ℝ := 1 / (4 * (q + 1))
  let a : ℝ := 1 / 2
  let b : ℝ := a - j
  let c : ℝ := b - uL * j
  let d : ℝ := b - (uR * j) / k
  have hj : 0 < j := by dsimp [j]; positivity
  have hjEq : 4 * (q + 1) * j = 1 := by dsimp [j]; field_simp
  have hjSmall : j < 1 / 8 := by
    nlinarith [mul_pos (show 0 < q - 1 by linarith) hj]
  have ha : 0 < a := by norm_num [a]
  have hb : 0 < b := by dsimp [b, a]; linarith
  have hBdrop : b - a ^ 2 = q * j := by dsimp [b, a]; nlinarith
  have huLj : uL * j < j := by
    simpa using mul_lt_mul_of_pos_right huLone hj
  have hc : 0 < c := by dsimp [c, b, a]; linarith
  have huRp : uR < p := by linarith
  have huRq : uR / k < q := by
    apply (div_lt_iff₀ hk).2
    simpa [p, mul_comm] using huRp
  have hd : 0 < d := by
    have hmul : (uR / k) * j < q * j := mul_lt_mul_of_pos_right huRq hj
    dsimp [d]
    rw [div_mul_eq_mul_div] at hmul
    nlinarith
  have h0 : a - b = j := by simp [b]
  have h1 : b - c = uL * j := by simp [c]
  have h2 : c - a ^ 2 = vL * j := by dsimp [c]; nlinarith
  have h3 : k * (b - d) = uR * j := by
    dsimp [d]
    field_simp
    ring
  have h4 : k * (d - a ^ 2) = vR * j := by
    calc
      k * (d - a ^ 2) = k * (b - a ^ 2) - uR * j := by
        dsimp [d]
        field_simp
        ring
      _ = k * (q * j) - uR * j := by rw [hBdrop]
      _ = (k * q - uR) * j := by ring
      _ = vR * j := by
        congr 1
        dsimp [p] at hsumR
        linarith
  exact ⟨{
    a := a, b := b, c := c, d := d, j := j,
    uL := uL, vL := vL, uR := uR, vR := vR,
    a_pos := ha, b_pos := hb, c_pos := hc, d_pos := hd, j_pos := hj,
    vL_half := hvLhalf, vL_lt_uL := hvLuL, uL_lt_one := huLone,
    vR_half := hvRhalf, vR_lt_uR := hvRuR, uR_lt_one := huRone,
    current0 := h0, current1 := h1, current2 := h2,
    current3 := h3, current4 := h4 }⟩

theorem window_implies_pairMultiCAC (k : ℝ) (hk : 0 < k)
    (hklo : 1 / 2 < k) (hkhi : k < 2) : PairMultiCAC k hk := by
  rcases window_has_pairData k hk hklo hkhi with ⟨W⟩
  exact pairMultiCAC_of_data k hk W

theorem pairMultiCAC_iff_window (k : ℝ) (hk : 0 < k) :
    PairMultiCAC k hk ↔ 1 / 2 < k ∧ k < 2 := by
  constructor
  · exact pairMultiCAC_onlyIf_window k hk
  · rintro ⟨hklo, hkhi⟩
    exact window_implies_pairMultiCAC k hk hklo hkhi

/-! ## Literal parameterized PAC family

The following wrapper closes a semantic gap in the phase-diagram statement:
PAC minimality is transported across the positive barrier parameter rather than
left implicit in the fixed-barrier fixture. -/

theorem left_isPACAt (k : ℝ) (hk : 0 < k) :
    (leftMotifAt k hk).IsPAC := by
  have h := Motif.rebase_isPAC MagnitudePair.leftMotif
    (Q' := networkAt k hk) rfl rfl MagnitudePair.left_isPAC
  simpa [leftMotifAt, Motif.rebase, MagnitudePair.leftMotif] using h

theorem right_isPACAt (k : ℝ) (hk : 0 < k) :
    (rightMotifAt k hk).IsPAC := by
  have h := Motif.rebase_isPAC MagnitudePair.rightMotif
    (Q' := networkAt k hk) rfl rfl MagnitudePair.right_isPAC
  simpa [rightMotifAt, Motif.rebase, MagnitudePair.rightMotif] using h

/-- The actual two-core family at a positive private-barrier ratio `k`. -/
def familyAt (k : ℝ) (hk : 0 < k) :
    CoreFamily (Core := MagnitudePair.Core) (networkAt k hk) where
  core
    | .left => leftMotifAt k hk
    | .right => rightMotifAt k hk
  core_isPAC
    | .left => left_isPACAt k hk
    | .right => right_isPACAt k hk
  orientation := fun _ => 1
  orientation_unit := by simp
  owner := fun r => if r.val < 3 then .left else .right
  owner_mem := by
    intro r
    fin_cases r <;> simp [leftMotifAt, rightMotifAt]

theorem familyAt_multiPAC (k : ℝ) (hk : 0 < k) :
    (familyAt k hk).MultiPAC := by
  refine ⟨MagnitudePair.commonFlow, ?_, ?_⟩
  · intro r
    fin_cases r <;> norm_num [familyAt, MagnitudePair.commonFlow]
  · intro c
    cases c with
    | left =>
        have h := (Motif.rebase_productive_iff MagnitudePair.leftMotif
          MagnitudePair.commonFlow (Q' := networkAt k hk) rfl rfl).2
          MagnitudePair.left_productive
        simpa [familyAt, leftMotifAt, Motif.rebase, MagnitudePair.leftMotif] using h
    | right =>
        have h := (Motif.rebase_productive_iff MagnitudePair.rightMotif
          MagnitudePair.commonFlow (Q' := networkAt k hk) rfl rfl).2
          MagnitudePair.right_productive
        simpa [familyAt, rightMotifAt, Motif.rebase, MagnitudePair.rightMotif] using h

theorem familyAt_directionCompatible (k : ℝ) (hk : 0 < k) :
    (familyAt k hk).DirectionCompatible := by
  refine ⟨MagnitudePair.directionPotential, ?_⟩
  intro r
  fin_cases r <;>
    norm_num [CoreFamily.directionalAffinity, CoreFamily.orientedDisplacement,
      familyAt, networkAt, reactant, product, MagnitudePair.directionPotential,
      Fin.sum_univ_succ]

theorem familyAt_multiCAC_iff_pairMultiCAC (k : ℝ) (hk : 0 < k) :
    (familyAt k hk).MultiCAC ↔ PairMultiCAC k hk := by
  simp only [CoreFamily.MultiCAC, PairMultiCAC]
  apply exists_congr
  intro z
  simp only [familyAt, Int.cast_one, one_mul]
  constructor
  · rintro ⟨hz, hcurrent, hproductive⟩
    exact ⟨hz, hcurrent, hproductive .left, hproductive .right⟩
  · rintro ⟨hz, hcurrent, hleft, hright⟩
    refine ⟨hz, hcurrent, ?_⟩
    intro c
    cases c with
    | left => exact hleft
    | right => exact hright

/-- Exact literal phase diagram: PAC and direction compatibility hold for
every positive barrier ratio, while common thermodynamic realizability holds
exactly in the open window `(1/2, 2)`. -/
theorem familyAt_complete_phaseDiagram (k : ℝ) (hk : 0 < k) :
    (familyAt k hk).MultiPAC ∧
      (familyAt k hk).DirectionCompatible ∧
      ((familyAt k hk).MultiCAC ↔ 1 / 2 < k ∧ k < 2) := by
  exact ⟨familyAt_multiPAC k hk, familyAt_directionCompatible k hk,
    (familyAt_multiCAC_iff_pairMultiCAC k hk).trans
      (pairMultiCAC_iff_window k hk)⟩

end ThermoCoreCompatibility.TrianglePhaseDiagram
