import proofs.DiagnosticWindows.Instance
import proofs.DiagnosticWindows.ExtraCapacity
import proofs.DiagnosticWindows.ExponentialBounds

set_option maxRecDepth 8192
noncomputable section
namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

def blank6 (t : NNReal) : ℝ := 1-kernel6.poissonized ((5/2)*t) uncalled 0
def miss6 (t : NNReal) : ℝ := loadedSurvival kernel6 4 ((5/2)*t)
def blank7 (t : NNReal) : ℝ := 1-kernel7.poissonized ((5/2)*t) uncalled 0
def miss7 (t : NNReal) : ℝ := loadedSurvival kernel7 4 ((5/2)*t)
def blank8 (t : NNReal) : ℝ := 1-kernel8.poissonized ((5/2)*t) uncalled 0
def miss8 (t : NNReal) : ℝ := loadedSurvival kernel8 4 ((5/2)*t)
def blank9 (t : NNReal) : ℝ := 1-kernel9.poissonized ((5/2)*t) uncalled 0
def miss9 (t : NNReal) : ℝ := loadedSurvival kernel9 4 ((5/2)*t)
theorem post_exp_0 : (960789439/1000000000) ≤ Real.exp (-1/25) ∧ Real.exp (-1/25) ≤ (3002467/3125000) := by
  have h := exp_enclosure16 (-1/25) (997503122397/1000000000000) (498751561199/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((960789439/1000000000):ℝ) ≤ (997503122397/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((498751561199/500000000000):ℝ)^16 ≤ (3002467/3125000))⟩

theorem post_exp_1 : (1725223/50000000) ≤ Real.exp (-101/30) ∧ Real.exp (-101/30) ≤ (34504461/1000000000) := by
  have h := exp_enclosure16 (-101/30) (810246572887/1000000000000) (101280821611/125000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((1725223/50000000):ℝ) ≤ (810246572887/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((101280821611/125000000000):ℝ)^16 ≤ (34504461/1000000000))⟩

theorem post_exp_2 : (2350453/500000000) ≤ Real.exp (-134/25) ∧ Real.exp (-134/25) ≤ (4700907/1000000000) := by
  have h := exp_enclosure16 (-134/25) (44708630397/62500000000) (715338086353/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((2350453/500000000):ℝ) ≤ (44708630397/62500000000)^16).trans h.1,
    h.2.trans (by norm_num : ((715338086353/1000000000000):ℝ)^16 ≤ (4700907/1000000000))⟩

theorem post_exp_3 : (2429669/1000000000) ≤ Real.exp (-301/50) ∧ Real.exp (-301/50) ≤ (242967/100000000) := by
  have h := exp_enclosure16 (-301/50) (686430703913/1000000000000) (343215351957/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((2429669/1000000000):ℝ) ≤ (686430703913/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((343215351957/500000000000):ℝ)^16 ≤ (242967/100000000))⟩

theorem post_exp_4 : (1191001/250000000) ≤ Real.exp (-401/75) ∧ Real.exp (-401/75) ≤ (952801/200000000) := by
  have h := exp_enclosure16 (-401/75) (357967224937/500000000000) (5727475599/8000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((1191001/250000000):ℝ) ≤ (357967224937/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((5727475599/8000000000):ℝ)^16 ≤ (952801/200000000))⟩

theorem post_exp_5 : (9157819/500000000) ≤ Real.exp (-4/1) ∧ Real.exp (-4/1) ≤ (18315639/1000000000) := by
  have h := exp_enclosure16 (-4/1) (778800783071/1000000000000) (24337524471/31250000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((9157819/500000000):ℝ) ≤ (778800783071/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((24337524471/31250000000):ℝ)^16 ≤ (18315639/1000000000))⟩

def r6_b : ℝ := (583416905/564128981)*Real.exp (-1/25) +
    (-64695736/326600989)*Real.exp (-101/30) +
    (-8707715/187473)*Real.exp (-134/25) +
    (1074680/1963533)*Real.exp (-301/50) +
    (100835/2189)*Real.exp (-401/75)
def r6_m : ℝ := (583416905/564128981)*Real.exp (-1/25) +
    (323478680/4923633)*Real.exp (-101/30) +
    (-861822383/187473)*Real.exp (-134/25) +
    (104089976/996567)*Real.exp (-301/50) +
    (986101031/221089)*Real.exp (-401/75)
theorem r6_blank_exact : blank6 (4/1) = 1-r6_b := by
  unfold blank6
  rw [capacity6_survival]
  norm_num [r6_b,eigen6,modes6,Fin.sum_univ_succ]
  ring
theorem r6_miss_exact : loadedSurvival kernel6 (4/1) ((5/2)*(4/1)) = Real.exp (-4/1)*r6_m := by
  rw [show kernel6 = birthKernel rates6 rates6_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (4/1) n * kernel6.poissonized
    ((5/2)*(4/1)) uncalled (loadIndex n)) = _
  simp_rw [capacity6_survival]
  norm_num [r6_m,eigen6,modes6,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem r6_blank_bound : 1/100 < blank6 (4/1) := by
  rw [r6_blank_exact]
  have h0 := post_exp_0
  have h1 := post_exp_1
  have h2 := post_exp_2
  have h3 := post_exp_3
  have h4 := post_exp_4
  unfold r6_b
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
theorem r6_miss_bound : 1/20 < loadedSurvival kernel6 (4/1) ((5/2)*(4/1)) := by
  rw [r6_miss_exact]
  have h0 := post_exp_0
  have h1 := post_exp_1
  have h2 := post_exp_2
  have h3 := post_exp_3
  have h4 := post_exp_4
  have hb : (3151/1000) < r6_m := by
    unfold r6_m
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hp := Real.exp_pos ((-4/1))
  have he := post_exp_5
  nlinarith [mul_pos hp (sub_pos.mpr hb)]
theorem post_exp_6 : (963965281/1000000000) ≤ Real.exp (-367/10000) ∧ Real.exp (-367/10000) ≤ (481982641/500000000) := by
  have h := exp_enclosure16 (-367/10000) (498854439317/500000000000) (199541775727/200000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((963965281/1000000000):ℝ) ≤ (498854439317/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((199541775727/200000000000):ℝ)^16 ≤ (481982641/500000000))⟩

theorem post_exp_7 : (41703449/1000000000) ≤ Real.exp (-111201/35000) ∧ Real.exp (-111201/35000) ≤ (834069/20000000) := by
  have h := exp_enclosure16 (-111201/35000) (819899740169/1000000000000) (81989974017/100000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((41703449/1000000000):ℝ) ≤ (819899740169/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((81989974017/100000000000):ℝ)^16 ≤ (834069/20000000))⟩

theorem post_exp_8 : (5148389/1000000000) ≤ Real.exp (-73767/14000) ∧ Real.exp (-73767/14000) ≤ (514839/100000000) := by
  have h := exp_enclosure16 (-73767/14000) (359707475879/500000000000) (719414951759/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((5148389/1000000000):ℝ) ≤ (359707475879/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((719414951759/1000000000000):ℝ)^16 ≤ (514839/100000000))⟩

theorem post_exp_9 : (72547/40000000) ≤ Real.exp (-15781/2500) ∧ Real.exp (-15781/2500) ≤ (453419/250000000) := by
  have h := exp_enclosure16 (-15781/2500) (674000113279/1000000000000) (1053125177/1562500000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((72547/40000000):ℝ) ≤ (674000113279/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((1053125177/1562500000):ℝ)^16 ≤ (453419/250000000))⟩

theorem post_exp_10 : (1823209/1000000000) ≤ Real.exp (-441501/70000) ∧ Real.exp (-441501/70000) ≤ (182321/100000000) := by
  have h := exp_enclosure16 (-441501/70000) (337110502431/500000000000) (674221004863/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((1823209/1000000000):ℝ) ≤ (337110502431/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((674221004863/1000000000000):ℝ)^16 ≤ (182321/100000000))⟩

def r7_b : ℝ := (1750250715/1698056581)*Real.exp (-367/10000) +
    (-80869670/677180881)*Real.exp (-111201/35000) +
    (24381602/62261727)*Real.exp (-73767/14000) +
    (40703505/1130519)*Real.exp (-15781/2500) +
    (-71290345/1963533)*Real.exp (-441501/70000)
def r7_m : ℝ := (1750250715/1698056581)*Real.exp (-367/10000) +
    (27599663090/677180881)*Real.exp (-111201/35000) +
    (1476587062/20753909)*Real.exp (-73767/14000) +
    (12639999997/1130519)*Real.exp (-15781/2500) +
    (-22108020905/1963533)*Real.exp (-441501/70000)
theorem r7_blank_exact : blank7 (367/100) = 1-r7_b := by
  unfold blank7
  rw [capacity7_survival]
  norm_num [r7_b,eigen7,modes7,Fin.sum_univ_succ]
  ring
theorem r7_miss_exact : loadedSurvival kernel7 (4/1) ((5/2)*(367/100)) = Real.exp (-4/1)*r7_m := by
  rw [show kernel7 = birthKernel rates7 rates7_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (4/1) n * kernel7.poissonized
    ((5/2)*(367/100)) uncalled (loadIndex n)) = _
  simp_rw [capacity7_survival]
  norm_num [r7_m,eigen7,modes7,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem r7_blank_bound : 1/100 < blank7 (367/100) := by
  rw [r7_blank_exact]
  have h0 := post_exp_6
  have h1 := post_exp_7
  have h2 := post_exp_8
  have h3 := post_exp_9
  have h4 := post_exp_10
  unfold r7_b
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
theorem r7_miss_bound : 1/20 < loadedSurvival kernel7 (4/1) ((5/2)*(367/100)) := by
  rw [r7_miss_exact]
  have h0 := post_exp_6
  have h1 := post_exp_7
  have h2 := post_exp_8
  have h3 := post_exp_9
  have h4 := post_exp_10
  have hb : (351/125) < r7_m := by
    unfold r7_m
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hp := Real.exp_pos ((-4/1))
  have he := post_exp_5
  nlinarith [mul_pos hp (sub_pos.mpr hb)]
theorem post_exp_11 : (966088339/1000000000) ≤ Real.exp (-69/2000) ∧ Real.exp (-69/2000) ≤ (48304417/50000000) := by
  have h := exp_enclosure16 (-69/2000) (997846073037/1000000000000) (498923036519/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((966088339/1000000000):ℝ) ≤ (997846073037/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((498923036519/500000000000):ℝ)^16 ≤ (48304417/50000000))⟩

theorem post_exp_12 : (47409269/1000000000) ≤ Real.exp (-48783/16000) ∧ Real.exp (-48783/16000) ≤ (4740927/100000000) := by
  have h := exp_enclosure16 (-48783/16000) (206624332183/250000000000) (826497328733/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((47409269/1000000000):ℝ) ≤ (206624332183/250000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((826497328733/1000000000000):ℝ)^16 ≤ (4740927/100000000))⟩

theorem post_exp_13 : (5511739/1000000000) ≤ Real.exp (-41607/8000) ∧ Real.exp (-41607/8000) ≤ (275587/50000000) := by
  have h := exp_enclosure16 (-41607/8000) (722487841507/1000000000000) (180621960377/250000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((5511739/1000000000):ℝ) ≤ (722487841507/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((180621960377/250000000000):ℝ)^16 ≤ (275587/50000000))⟩

theorem post_exp_14 : (759037/500000000) ≤ Real.exp (-20769/3200) ∧ Real.exp (-20769/3200) ≤ (60723/40000000) := by
  have h := exp_enclosure16 (-20769/3200) (41659191373/62500000000) (66654706197/100000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((759037/500000000):ℝ) ≤ (41659191373/62500000000)^16).trans h.1,
    h.2.trans (by norm_num : ((66654706197/100000000000):ℝ)^16 ≤ (60723/40000000))⟩

theorem post_exp_15 : (19811/20000000) ≤ Real.exp (-27669/4000) ∧ Real.exp (-27669/4000) ≤ (990551/1000000000) := by
  have h := exp_enclosure16 (-27669/4000) (648996389803/1000000000000) (162249097451/250000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((19811/20000000):ℝ) ≤ (648996389803/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((162249097451/250000000000):ℝ)^16 ≤ (990551/1000000000))⟩

def r8_b : ℝ := (4083918335/3969704181)*Real.exp (-69/2000) +
    (-184844960/1981538481)*Real.exp (-48783/16000) +
    (3413424280/17784908401)*Real.exp (-41607/8000) +
    (-86834144/280647081)*Real.exp (-20769/3200) +
    (20368670/111921381)*Real.exp (-27669/4000)
def r8_m : ℝ := (4083918335/3969704181)*Real.exp (-69/2000) +
    (64418468560/1981538481)*Real.exp (-48783/16000) +
    (844984248640/17784908401)*Real.exp (-41607/8000) +
    (-99935417104/841941243)*Real.exp (-20769/3200) +
    (24168424342/335764143)*Real.exp (-27669/4000)
theorem r8_blank_exact : blank8 (69/20) = 1-r8_b := by
  unfold blank8
  rw [capacity8_survival]
  norm_num [r8_b,eigen8,modes8,Fin.sum_univ_succ]
  ring
theorem r8_miss_exact : loadedSurvival kernel8 (4/1) ((5/2)*(69/20)) = Real.exp (-4/1)*r8_m := by
  rw [show kernel8 = birthKernel rates8 rates8_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (4/1) n * kernel8.poissonized
    ((5/2)*(69/20)) uncalled (loadIndex n)) = _
  simp_rw [capacity8_survival]
  norm_num [r8_m,eigen8,modes8,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem r8_blank_bound : blank8 (69/20) ≤ 1/100 := by
  rw [r8_blank_exact]
  have h0 := post_exp_11
  have h1 := post_exp_12
  have h2 := post_exp_13
  have h3 := post_exp_14
  have h4 := post_exp_15
  unfold r8_b
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
theorem r8_miss_bound : loadedSurvival kernel8 (4/1) ((5/2)*(69/20)) ≤ 1/20 := by
  rw [r8_miss_exact]
  have h0 := post_exp_11
  have h1 := post_exp_12
  have h2 := post_exp_13
  have h3 := post_exp_14
  have h4 := post_exp_15
  have hb : r8_m ≤ (269/100) := by
    unfold r8_m
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hp := Real.exp_pos ((-4/1))
  have he := post_exp_5
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hb)]
theorem post_exp_16 : (60410719/62500000) ≤ Real.exp (-17/500) ∧ Real.exp (-17/500) ≤ (193314301/200000000) := by
  have h := exp_enclosure16 (-17/500) (498938628107/500000000000) (199575451243/200000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((60410719/62500000):ℝ) ≤ (498938628107/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((199575451243/200000000000):ℝ)^16 ≤ (193314301/200000000))⟩

theorem post_exp_17 : (2477557/50000000) ≤ Real.exp (-12019/4000) ∧ Real.exp (-12019/4000) ≤ (49551141/1000000000) := by
  have h := exp_enclosure16 (-12019/4000) (82878303669/100000000000) (828783036691/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((2477557/50000000):ℝ) ≤ (82878303669/100000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((828783036691/1000000000000):ℝ)^16 ≤ (49551141/1000000000))⟩

theorem post_exp_18 : (1485811/250000000) ≤ Real.exp (-10251/2000) ∧ Real.exp (-10251/2000) ≤ (1188649/200000000) := by
  have h := exp_enclosure16 (-10251/2000) (725899466239/1000000000000) (283554479/390625000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((1485811/250000000):ℝ) ≤ (725899466239/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((283554479/390625000):ℝ)^16 ≤ (1188649/200000000))⟩

theorem post_exp_19 : (1667799/1000000000) ≤ Real.exp (-5117/800) ∧ Real.exp (-5117/800) ≤ (8339/5000000) := by
  have h := exp_enclosure16 (-5117/800) (167619292677/250000000000) (670477170709/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((1667799/1000000000):ℝ) ≤ (167619292677/250000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((670477170709/1000000000000):ℝ)^16 ≤ (8339/5000000))⟩

theorem post_exp_20 : (1095001/1000000000) ≤ Real.exp (-6817/1000) ∧ Real.exp (-6817/1000) ≤ (547501/500000000) := by
  have h := exp_enclosure16 (-6817/1000) (81634440453/125000000000) (5224604189/8000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((1095001/1000000000):ℝ) ≤ (81634440453/125000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((5224604189/8000000000):ℝ)^16 ≤ (547501/500000000))⟩

def r8early_b : ℝ := (4083918335/3969704181)*Real.exp (-17/500) +
    (-184844960/1981538481)*Real.exp (-12019/4000) +
    (3413424280/17784908401)*Real.exp (-10251/2000) +
    (-86834144/280647081)*Real.exp (-5117/800) +
    (20368670/111921381)*Real.exp (-6817/1000)
def r8early_m : ℝ := (4083918335/3969704181)*Real.exp (-17/500) +
    (64418468560/1981538481)*Real.exp (-12019/4000) +
    (844984248640/17784908401)*Real.exp (-10251/2000) +
    (-99935417104/841941243)*Real.exp (-5117/800) +
    (24168424342/335764143)*Real.exp (-6817/1000)
theorem r8early_blank_exact : blank8 (17/5) = 1-r8early_b := by
  unfold blank8
  rw [capacity8_survival]
  norm_num [r8early_b,eigen8,modes8,Fin.sum_univ_succ]
  ring
theorem r8early_miss_exact : loadedSurvival kernel8 (4/1) ((5/2)*(17/5)) = Real.exp (-4/1)*r8early_m := by
  rw [show kernel8 = birthKernel rates8 rates8_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (4/1) n * kernel8.poissonized
    ((5/2)*(17/5)) uncalled (loadIndex n)) = _
  simp_rw [capacity8_survival]
  norm_num [r8early_m,eigen8,modes8,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem r8early_miss_bound : 1/20 < loadedSurvival kernel8 (4/1) ((5/2)*(17/5)) := by
  rw [r8early_miss_exact]
  have h0 := post_exp_16
  have h1 := post_exp_17
  have h2 := post_exp_18
  have h3 := post_exp_19
  have h4 := post_exp_20
  have hb : (2767/1000) < r8early_m := by
    unfold r8early_m
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hp := Real.exp_pos ((-4/1))
  have he := post_exp_5
  nlinarith [mul_pos hp (sub_pos.mpr hb)]
theorem post_exp_21 : (120700677/125000000) ≤ Real.exp (-7/200) ∧ Real.exp (-7/200) ≤ (965605417/1000000000) := by
  have h := exp_enclosure16 (-7/200) (498907445417/500000000000) (199562978167/200000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((120700677/125000000):ℝ) ≤ (498907445417/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((199562978167/200000000000):ℝ)^16 ≤ (965605417/1000000000))⟩

theorem post_exp_22 : (22679991/500000000) ≤ Real.exp (-4949/1600) ∧ Real.exp (-4949/1600) ≤ (45359983/1000000000) := by
  have h := exp_enclosure16 (-4949/1600) (206054481137/250000000000) (824217924549/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((22679991/500000000):ℝ) ≤ (206054481137/250000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((824217924549/1000000000000):ℝ)^16 ≤ (45359983/1000000000))⟩

theorem post_exp_23 : (5111563/1000000000) ≤ Real.exp (-4221/800) ∧ Real.exp (-4221/800) ≤ (1277891/250000000) := by
  have h := exp_enclosure16 (-4221/800) (719092250929/1000000000000) (71909225093/100000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((5111563/1000000000):ℝ) ≤ (719092250929/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((71909225093/100000000000):ℝ)^16 ≤ (1277891/250000000))⟩

theorem post_exp_24 : (138179/100000000) ≤ Real.exp (-2107/320) ∧ Real.exp (-2107/320) ≤ (1381791/1000000000) := by
  have h := exp_enclosure16 (-2107/320) (662639990187/1000000000000) (165659997547/250000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((138179/100000000):ℝ) ≤ (662639990187/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((165659997547/250000000000):ℝ)^16 ≤ (1381791/1000000000))⟩

theorem post_exp_25 : (448031/500000000) ≤ Real.exp (-2807/400) ∧ Real.exp (-2807/400) ≤ (896063/1000000000) := by
  have h := exp_enclosure16 (-2807/400) (322471367201/500000000000) (644942734403/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((448031/500000000):ℝ) ≤ (322471367201/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((644942734403/1000000000000):ℝ)^16 ≤ (896063/1000000000))⟩

def r8late_b : ℝ := (4083918335/3969704181)*Real.exp (-7/200) +
    (-184844960/1981538481)*Real.exp (-4949/1600) +
    (3413424280/17784908401)*Real.exp (-4221/800) +
    (-86834144/280647081)*Real.exp (-2107/320) +
    (20368670/111921381)*Real.exp (-2807/400)
def r8late_m : ℝ := (4083918335/3969704181)*Real.exp (-7/200) +
    (64418468560/1981538481)*Real.exp (-4949/1600) +
    (844984248640/17784908401)*Real.exp (-4221/800) +
    (-99935417104/841941243)*Real.exp (-2107/320) +
    (24168424342/335764143)*Real.exp (-2807/400)
theorem r8late_blank_exact : blank8 (7/2) = 1-r8late_b := by
  unfold blank8
  rw [capacity8_survival]
  norm_num [r8late_b,eigen8,modes8,Fin.sum_univ_succ]
  ring
theorem r8late_miss_exact : loadedSurvival kernel8 (4/1) ((5/2)*(7/2)) = Real.exp (-4/1)*r8late_m := by
  rw [show kernel8 = birthKernel rates8 rates8_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (4/1) n * kernel8.poissonized
    ((5/2)*(7/2)) uncalled (loadIndex n)) = _
  simp_rw [capacity8_survival]
  norm_num [r8late_m,eigen8,modes8,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem r8late_blank_bound : 1/100 < blank8 (7/2) := by
  rw [r8late_blank_exact]
  have h0 := post_exp_21
  have h1 := post_exp_22
  have h2 := post_exp_23
  have h3 := post_exp_24
  have h4 := post_exp_25
  unfold r8late_b
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
theorem post_exp_26 : (967538559/1000000000) ≤ Real.exp (-33/1000) ∧ Real.exp (-33/1000) ≤ (1511779/1562500) := by
  have h := exp_enclosure16 (-33/1000) (997939625491/1000000000000) (249484906373/250000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((967538559/1000000000):ℝ) ≤ (997939625491/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((249484906373/250000000000):ℝ)^16 ≤ (1511779/1562500))⟩

theorem post_exp_27 : (51680917/1000000000) ≤ Real.exp (-1111/375) ∧ Real.exp (-1111/375) ≤ (25840459/500000000) := by
  have h := exp_enclosure16 (-1111/375) (830965778013/1000000000000) (415482889007/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((51680917/1000000000):ℝ) ≤ (830965778013/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((415482889007/500000000000):ℝ)^16 ≤ (25840459/500000000))⟩

theorem post_exp_28 : (1436861/250000000) ≤ Real.exp (-5159/1000) ∧ Real.exp (-5159/1000) ≤ (1149489/200000000) := by
  have h := exp_enclosure16 (-5159/1000) (724381204217/1000000000000) (362190602109/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((1436861/250000000):ℝ) ≤ (724381204217/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((362190602109/500000000000):ℝ)^16 ≤ (1149489/200000000))⟩

theorem post_exp_29 : (665383/500000000) ≤ Real.exp (-3311/500) ∧ Real.exp (-3311/500) ≤ (1330767/1000000000) := by
  have h := exp_enclosure16 (-3311/500) (165270895387/250000000000) (13221671631/20000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((665383/500000000):ℝ) ≤ (165270895387/250000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((13221671631/20000000000):ℝ)^16 ≤ (1330767/1000000000))⟩

theorem post_exp_30 : (320761/500000000) ≤ Real.exp (-4411/600) ∧ Real.exp (-4411/600) ≤ (641523/1000000000) := by
  have h := exp_enclosure16 (-4411/600) (63161252471/100000000000) (631612524711/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((320761/500000000):ℝ) ≤ (63161252471/100000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((631612524711/1000000000000):ℝ)^16 ≤ (641523/1000000000))⟩

def r9_b : ℝ := (57174856690/55645502467)*Real.exp (-33/1000) +
    (-363913515/4537616081)*Real.exp (-1111/375) +
    (104492580/792880127)*Real.exp (-5159/1000) +
    (-162814020/1130144681)*Real.exp (-3311/500) +
    (36663606/564128981)*Real.exp (-4411/600)
def r9_m : ℝ := (57174856690/55645502467)*Real.exp (-33/1000) +
    (128865819145/4537616081)*Real.exp (-1111/375) +
    (31441920780/792880127)*Real.exp (-5159/1000) +
    (-209682555140/3390434043)*Real.exp (-3311/500) +
    (45857612218/1692386943)*Real.exp (-4411/600)
theorem r9_blank_exact : blank9 (33/10) = 1-r9_b := by
  unfold blank9
  rw [capacity9_survival]
  norm_num [r9_b,eigen9,modes9,Fin.sum_univ_succ]
  ring
theorem r9_miss_exact : loadedSurvival kernel9 (4/1) ((5/2)*(33/10)) = Real.exp (-4/1)*r9_m := by
  rw [show kernel9 = birthKernel rates9 rates9_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (4/1) n * kernel9.poissonized
    ((5/2)*(33/10)) uncalled (loadIndex n)) = _
  simp_rw [capacity9_survival]
  norm_num [r9_m,eigen9,modes9,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem r9_blank_bound : blank9 (33/10) ≤ 1/100 := by
  rw [r9_blank_exact]
  have h0 := post_exp_26
  have h1 := post_exp_27
  have h2 := post_exp_28
  have h3 := post_exp_29
  have h4 := post_exp_30
  unfold r9_b
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
theorem r9_miss_bound : loadedSurvival kernel9 (4/1) ((5/2)*(33/10)) ≤ 1/20 := by
  rw [r9_miss_exact]
  have h0 := post_exp_26
  have h1 := post_exp_27
  have h2 := post_exp_28
  have h3 := post_exp_29
  have h4 := post_exp_30
  have hb : r9_m ≤ (1313/500) := by
    unfold r9_m
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hp := Real.exp_pos ((-4/1))
  have he := post_exp_5
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hb)]
theorem post_exp_31 : (242247739/250000000) ≤ Real.exp (-63/2000) ∧ Real.exp (-63/2000) ≤ (968990957/1000000000) := by
  have h := exp_enclosure16 (-63/2000) (998033186717/1000000000000) (499016593359/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((242247739/250000000):ℝ) ≤ (998033186717/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((499016593359/500000000000):ℝ)^16 ≤ (968990957/1000000000))⟩

theorem post_exp_32 : (5707723/100000000) ≤ Real.exp (-57267/20000) ∧ Real.exp (-57267/20000) ≤ (57077231/1000000000) := by
  have h := exp_enclosure16 (-57267/20000) (836139866889/1000000000000) (83613986689/100000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((5707723/100000000):ℝ) ≤ (836139866889/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((83613986689/100000000000):ℝ)^16 ≤ (57077231/1000000000))⟩

theorem post_exp_33 : (789081/125000000) ≤ Real.exp (-12663/2500) ∧ Real.exp (-12663/2500) ≤ (6312649/1000000000) := by
  have h := exp_enclosure16 (-12663/2500) (728640361483/1000000000000) (182160090371/250000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((789081/125000000):ℝ) ≤ (728640361483/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((182160090371/250000000000):ℝ)^16 ≤ (6312649/1000000000))⟩

theorem post_exp_34 : (163861/125000000) ≤ Real.exp (-132741/20000) ∧ Real.exp (-132741/20000) ≤ (1310889/1000000000) := by
  have h := exp_enclosure16 (-132741/20000) (82557755271/125000000000) (660462042169/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((163861/125000000):ℝ) ≤ (82557755271/125000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((660462042169/1000000000000):ℝ)^16 ≤ (1310889/1000000000))⟩

theorem post_exp_35 : (511123/1000000000) ≤ Real.exp (-75789/10000) ∧ Real.exp (-75789/10000) ≤ (127781/250000000) := by
  have h := exp_enclosure16 (-75789/10000) (622705708381/1000000000000) (311352854191/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((511123/1000000000):ℝ) ≤ (622705708381/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((311352854191/500000000000):ℝ)^16 ≤ (127781/250000000))⟩

def interval_early_b : ℝ := (102914742042/100251115667)*Real.exp (-63/2000) +
    (-4528701520/62609895767)*Real.exp (-57267/20000) +
    (182862015/1765049327)*Real.exp (-12663/2500) +
    (-1953768240/20823535967)*Real.exp (-132741/20000) +
    (61106010/1698056581)*Real.exp (-75789/10000)
def interval_early_m : ℝ := (102914742042/100251115667)*Real.exp (-63/2000) +
    (1623992365072/62609895767)*Real.exp (-57267/20000) +
    (63061806563/1765049327)*Real.exp (-12663/2500) +
    (-38934745328/905371129)*Real.exp (-132741/20000) +
    (3243570002/221485641)*Real.exp (-75789/10000)
theorem interval_early_blank_exact : blank10 (63/20) = 1-interval_early_b := by
  unfold blank10
  rw [capacity10_survival]
  norm_num [interval_early_b,eigen10,modes10,Fin.sum_univ_succ]
  ring
theorem interval_early_miss_exact : loadedSurvival kernel10 (4/1) ((5/2)*(63/20)) = Real.exp (-4/1)*interval_early_m := by
  rw [show kernel10 = birthKernel rates10 rates10_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (4/1) n * kernel10.poissonized
    ((5/2)*(63/20)) uncalled (loadIndex n)) = _
  simp_rw [capacity10_survival]
  norm_num [interval_early_m,eigen10,modes10,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem interval_early_miss_bound : loadedSurvival kernel10 (4/1) ((5/2)*(63/20)) ≤ 1/20 := by
  rw [interval_early_miss_exact]
  have h0 := post_exp_31
  have h1 := post_exp_32
  have h2 := post_exp_33
  have h3 := post_exp_34
  have h4 := post_exp_35
  have hb : interval_early_m ≤ (2653/1000) := by
    unfold interval_early_m
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hp := Real.exp_pos ((-4/1))
  have he := post_exp_5
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hb)]
theorem post_exp_36 : (24901003/500000000) ≤ Real.exp (-29997/10000) ∧ Real.exp (-29997/10000) ≤ (49802007/1000000000) := by
  have h := exp_enclosure16 (-29997/10000) (414522331311/500000000000) (829044662623/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((24901003/500000000):ℝ) ≤ (414522331311/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((829044662623/1000000000000):ℝ)^16 ≤ (49802007/1000000000))⟩

theorem post_exp_37 : (4959749/1000000000) ≤ Real.exp (-6633/1250) ∧ Real.exp (-6633/1250) ≤ (19839/4000000) := by
  have h := exp_enclosure16 (-6633/1250) (89717310921/125000000000) (717738487369/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((4959749/1000000000):ℝ) ≤ (89717310921/125000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((717738487369/1000000000000):ℝ)^16 ≤ (19839/4000000))⟩

theorem post_exp_38 : (955667/1000000000) ≤ Real.exp (-69531/10000) ∧ Real.exp (-69531/10000) ≤ (238917/250000000) := by
  have h := exp_enclosure16 (-69531/10000) (323771930081/500000000000) (647543860163/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((955667/1000000000):ℝ) ≤ (323771930081/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((647543860163/1000000000000):ℝ)^16 ≤ (238917/250000000))⟩

theorem post_exp_39 : (356277/1000000000) ≤ Real.exp (-39699/5000) ∧ Real.exp (-39699/5000) ≤ (178139/500000000) := by
  have h := exp_enclosure16 (-39699/5000) (121763405971/200000000000) (608817029857/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((356277/1000000000):ℝ) ≤ (121763405971/200000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((608817029857/1000000000000):ℝ)^16 ≤ (178139/500000000))⟩

def interval_late_b : ℝ := (102914742042/100251115667)*Real.exp (-33/1000) +
    (-4528701520/62609895767)*Real.exp (-29997/10000) +
    (182862015/1765049327)*Real.exp (-6633/1250) +
    (-1953768240/20823535967)*Real.exp (-69531/10000) +
    (61106010/1698056581)*Real.exp (-39699/5000)
def interval_late_m : ℝ := (102914742042/100251115667)*Real.exp (-33/1000) +
    (1623992365072/62609895767)*Real.exp (-29997/10000) +
    (63061806563/1765049327)*Real.exp (-6633/1250) +
    (-38934745328/905371129)*Real.exp (-69531/10000) +
    (3243570002/221485641)*Real.exp (-39699/5000)
theorem interval_late_blank_exact : blank10 (33/10) = 1-interval_late_b := by
  unfold blank10
  rw [capacity10_survival]
  norm_num [interval_late_b,eigen10,modes10,Fin.sum_univ_succ]
  ring
theorem interval_late_miss_exact : loadedSurvival kernel10 (4/1) ((5/2)*(33/10)) = Real.exp (-4/1)*interval_late_m := by
  rw [show kernel10 = birthKernel rates10 rates10_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (4/1) n * kernel10.poissonized
    ((5/2)*(33/10)) uncalled (loadIndex n)) = _
  simp_rw [capacity10_survival]
  norm_num [interval_late_m,eigen10,modes10,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem interval_late_blank_bound : blank10 (33/10) ≤ 1/100 := by
  rw [interval_late_blank_exact]
  have h0 := post_exp_26
  have h1 := post_exp_36
  have h2 := post_exp_37
  have h3 := post_exp_38
  have h4 := post_exp_39
  unfold interval_late_b
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
theorem post_exp_40 : (120973527/125000000) ≤ Real.exp (-16371/500000) ∧ Real.exp (-16371/500000) ≤ (967788217/1000000000) := by
  have h := exp_enclosure16 (-16371/500000) (997955717397/1000000000000) (498977858699/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((120973527/125000000):ℝ) ≤ (997955717397/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((498977858699/500000000000):ℝ)^16 ≤ (967788217/1000000000))⟩

theorem post_exp_41 : (1593243/31250000) ≤ Real.exp (-14881239/5000000) ∧ Real.exp (-14881239/5000000) ≤ (50983777/1000000000) := by
  have h := exp_enclosure16 (-14881239/5000000) (830260736219/1000000000000) (41513036811/50000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((1593243/31250000):ℝ) ≤ (830260736219/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((41513036811/50000000000):ℝ)^16 ≤ (50983777/1000000000))⟩

theorem post_exp_42 : (5169839/1000000000) ≤ Real.exp (-3290571/625000) ∧ Real.exp (-3290571/625000) ≤ (64623/12500000) := by
  have h := exp_enclosure16 (-3290571/625000) (719601926303/1000000000000) (22487560197/31250000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((5169839/1000000000):ℝ) ≤ (719601926303/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((22487560197/31250000000):ℝ)^16 ≤ (64623/12500000))⟩

theorem post_exp_43 : (31533/31250000) ≤ Real.exp (-34493697/5000000) ∧ Real.exp (-34493697/5000000) ≤ (1009057/1000000000) := by
  have h := exp_enclosure16 (-34493697/5000000) (64974765633/100000000000) (649747656331/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((31533/31250000):ℝ) ≤ (64974765633/100000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((649747656331/1000000000000):ℝ)^16 ≤ (1009057/1000000000))⟩

theorem post_exp_44 : (189547/500000000) ≤ Real.exp (-19694313/2500000) ∧ Real.exp (-19694313/2500000) ≤ (75819/200000000) := by
  have h := exp_enclosure16 (-19694313/2500000) (152795907479/250000000000) (305591814959/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((189547/500000000):ℝ) ≤ (152795907479/250000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((305591814959/500000000000):ℝ)^16 ≤ (75819/200000000))⟩

def robust_blank_b : ℝ := (102914742042/100251115667)*Real.exp (-16371/500000) +
    (-4528701520/62609895767)*Real.exp (-14881239/5000000) +
    (182862015/1765049327)*Real.exp (-3290571/625000) +
    (-1953768240/20823535967)*Real.exp (-34493697/5000000) +
    (61106010/1698056581)*Real.exp (-19694313/2500000)
def robust_blank_m : ℝ := (102914742042/100251115667)*Real.exp (-16371/500000) +
    (1623992365072/62609895767)*Real.exp (-14881239/5000000) +
    (63061806563/1765049327)*Real.exp (-3290571/625000) +
    (-38934745328/905371129)*Real.exp (-34493697/5000000) +
    (3243570002/221485641)*Real.exp (-19694313/2500000)
theorem robust_blank_blank_exact : blank10 (16371/5000) = 1-robust_blank_b := by
  unfold blank10
  rw [capacity10_survival]
  norm_num [robust_blank_b,eigen10,modes10,Fin.sum_univ_succ]
  ring
theorem robust_blank_miss_exact : loadedSurvival kernel10 (4/1) ((5/2)*(16371/5000)) = Real.exp (-4/1)*robust_blank_m := by
  rw [show kernel10 = birthKernel rates10 rates10_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (4/1) n * kernel10.poissonized
    ((5/2)*(16371/5000)) uncalled (loadIndex n)) = _
  simp_rw [capacity10_survival]
  norm_num [robust_blank_m,eigen10,modes10,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem robust_blank_blank_bound : blank10 (16371/5000) ≤ 1/100 := by
  rw [robust_blank_blank_exact]
  have h0 := post_exp_40
  have h1 := post_exp_41
  have h2 := post_exp_42
  have h3 := post_exp_43
  have h4 := post_exp_44
  unfold robust_blank_b
  linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
theorem post_exp_45 : (969221603/1000000000) ≤ Real.exp (-15631/500000) ∧ Real.exp (-15631/500000) ≤ (242305401/250000000) := by
  have h := exp_enclosure16 (-15631/500000) (998048032571/1000000000000) (249512008143/250000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((969221603/1000000000):ℝ) ≤ (998048032571/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((249512008143/250000000000):ℝ)^16 ≤ (242305401/250000000))⟩

theorem post_exp_46 : (11665101/200000000) ≤ Real.exp (-14208579/5000000) ∧ Real.exp (-14208579/5000000) ≤ (29162753/500000000) := by
  have h := exp_enclosure16 (-14208579/5000000) (16745424153/20000000000) (837271207651/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((11665101/200000000):ℝ) ≤ (16745424153/20000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((837271207651/1000000000000):ℝ)^16 ≤ (29162753/500000000))⟩

theorem post_exp_47 : (3279459/500000000) ≤ Real.exp (-3141831/625000) ∧ Real.exp (-3141831/625000) ≤ (6558919/1000000000) := by
  have h := exp_enclosure16 (-3141831/625000) (73038528237/100000000000) (730385282371/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((3279459/500000000):ℝ) ≤ (73038528237/100000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((730385282371/1000000000000):ℝ)^16 ≤ (6558919/1000000000))⟩

theorem post_exp_48 : (1378301/1000000000) ≤ Real.exp (-32934517/5000000) ∧ Real.exp (-32934517/5000000) ≤ (689151/500000000) := by
  have h := exp_enclosure16 (-32934517/5000000) (82816910597/125000000000) (662535284777/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((1378301/1000000000):ℝ) ≤ (82816910597/125000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((662535284777/1000000000000):ℝ)^16 ≤ (689151/500000000))⟩

theorem post_exp_49 : (108249/200000000) ≤ Real.exp (-18804093/2500000) ∧ Real.exp (-18804093/2500000) ≤ (270623/500000000) := by
  have h := exp_enclosure16 (-18804093/2500000) (624938318197/1000000000000) (312469159099/500000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((108249/200000000):ℝ) ≤ (624938318197/1000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((312469159099/500000000000):ℝ)^16 ≤ (270623/500000000))⟩

theorem post_exp_50 : (9249857/500000000) ≤ Real.exp (-399/100) ∧ Real.exp (-399/100) ≤ (3699943/200000000) := by
  have h := exp_enclosure16 (-399/100) (389643842851/500000000000) (779287685703/1000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((9249857/500000000):ℝ) ≤ (389643842851/500000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((779287685703/1000000000000):ℝ)^16 ≤ (3699943/200000000))⟩

def robust_miss_b : ℝ := (102914742042/100251115667)*Real.exp (-15631/500000) +
    (-4528701520/62609895767)*Real.exp (-14208579/5000000) +
    (182862015/1765049327)*Real.exp (-3141831/625000) +
    (-1953768240/20823535967)*Real.exp (-32934517/5000000) +
    (61106010/1698056581)*Real.exp (-18804093/2500000)
def robust_miss_m : ℝ := (102914742042/100251115667)*Real.exp (-15631/500000) +
    (40498026560138/1565247394175)*Real.exp (-14208579/5000000) +
    (1249126437348867/35300986540000)*Real.exp (-3141831/625000) +
    (-891396231856578333/20823535967000000)*Real.exp (-32934517/5000000) +
    (19859959148858366727/1358445264800000000)*Real.exp (-18804093/2500000)
theorem robust_miss_blank_exact : blank10 (15631/5000) = 1-robust_miss_b := by
  unfold blank10
  rw [capacity10_survival]
  norm_num [robust_miss_b,eigen10,modes10,Fin.sum_univ_succ]
  ring
theorem robust_miss_miss_exact : loadedSurvival kernel10 (399/100) ((5/2)*(15631/5000)) = Real.exp (-399/100)*robust_miss_m := by
  rw [show kernel10 = birthKernel rates10 rates10_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight (399/100) n * kernel10.poissonized
    ((5/2)*(15631/5000)) uncalled (loadIndex n)) = _
  simp_rw [capacity10_survival]
  norm_num [robust_miss_m,eigen10,modes10,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem robust_miss_miss_bound : loadedSurvival kernel10 (399/100) ((5/2)*(15631/5000)) ≤ 1/20 := by
  rw [robust_miss_miss_exact]
  have h0 := post_exp_45
  have h1 := post_exp_46
  have h2 := post_exp_47
  have h3 := post_exp_48
  have h4 := post_exp_49
  have hb : robust_miss_m ≤ (2687/1000) := by
    unfold robust_miss_m
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hp := Real.exp_pos ((-399/100))
  have he := post_exp_50
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hb)]
end DiagnosticWindows
