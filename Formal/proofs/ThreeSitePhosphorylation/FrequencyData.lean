import proofs.ThreeSitePhosphorylation.Frequency

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 1000000

def even0 (t : ℝ) : ℝ :=
    (21549480866197/53063010000:ℝ)*t^4 +
    (-3070471513831161895424219/2522151194062500000:ℝ)*t^3 +
    (3747333761964530151289376279869/151329071643750000000000:ℝ)*t^2 +
    (-676438287388827146536247537/1269894307500000000000:ℝ)*t^1 +
    (1182316803067886887/3061327500000000:ℝ)

def odd0 (t : ℝ) : ℝ :=
    (1/1:ℝ)*t^4 +
    (-1914250662484005497/49272795000000:ℝ)*t^3 +
    (178228249672628679513269034107/15132907164375000000000:ℝ)*t^2 +
    (-1095227502621761760478226249101/226993607465625000000000:ℝ)*t^1 +
    (2365405597729059858828139/17908765875000000000:ℝ)

def even1 (t : ℝ) : ℝ :=
    (716/6045:ℝ)*t^4 +
    (-1743145840777470340069/403544191050000000:ℝ)*t^3 +
    (19351917652493567002237891771/15132907164375000000000:ℝ)*t^2 +
    (-15669391757369638993598066707/13968837382500000000000:ℝ)*t^1 +
    (1182316803067886887/3061327500000000:ℝ)

def odd1 (t : ℝ) : ℝ :=
    (-244167141079021/5173643475000:ℝ)*t^3 +
    (41210428898350734288350941/302658143287500000000:ℝ)*t^2 +
    (-298391200108946577505242797723/113496803732812500000000:ℝ)*t^1 +
    (2369048939115567901134889/17908765875000000000:ℝ)

theorem frequency_elimination_identity (t : ℝ) :
    frequencyPolynomial t = odd0 t*even1 t-even0 t*odd1 t := by
  unfold frequencyPolynomial even0 odd0 even1 odd1
  ring

theorem frequency_even_signs (t : ℝ) (ht : frequencyLower ≤ t ∧ t ≤ frequencyUpper) :
    0 < even0 t ∧ even1 t < 0 := by
  have hl : (0:ℝ) ≤ frequencyLower := by norm_num [frequencyLower]
  have ht0 : 0 ≤ t := hl.trans ht.1
  have h2 : frequencyLower^2 ≤ t^2 ∧ t^2 ≤ frequencyUpper^2 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  have h3 : frequencyLower^3 ≤ t^3 ∧ t^3 ≤ frequencyUpper^3 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  have h4 : frequencyLower^4 ≤ t^4 ∧ t^4 ≤ frequencyUpper^4 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  norm_num [frequencyLower,frequencyUpper] at ht h2 h3 h4
  constructor
  · unfold even0
    linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  · unfold even1
    linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

def reconstructedRatio (t : ℝ) : ℝ := -(even0 t)/(even1 t)

theorem admissible_frequency_exists : ∃ t r : ℝ,
    0 < t ∧ 0 < r ∧ frequencyLower ≤ t ∧ t ≤ frequencyUpper ∧
    even0 t+r*even1 t = 0 ∧ odd0 t+r*odd1 t = 0 := by
  obtain ⟨t,hl,hu,ht,hphi⟩ := positive_frequency_exists
  have hs := frequency_even_signs t ⟨hl,hu⟩
  have hn : even1 t ≠ 0 := ne_of_lt hs.2
  have hr : 0 < reconstructedRatio t := div_pos_of_neg_of_neg (neg_neg_of_pos hs.1) hs.2
  refine ⟨t,reconstructedRatio t,ht,hr,hl,hu,?_,?_⟩
  · unfold reconstructedRatio
    field_simp
    ring
  · rw [frequency_elimination_identity] at hphi
    unfold reconstructedRatio
    field_simp
    nlinarith only [hphi]

end
end ThreeSitePhosphorylation
