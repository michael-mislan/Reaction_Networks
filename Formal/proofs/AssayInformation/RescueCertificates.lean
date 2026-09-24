import proofs.DiagnosticWindows.Main
import proofs.DiagnosticWindows.ExponentialBounds
set_option maxRecDepth 8192
noncomputable section
namespace AssayInformation
open DiagnosticWindows FiniteCopy
open scoped BigOperators

theorem rescue_exp_0 : (9323938199/10000000000) ≤ Real.exp (-7/100) ∧ Real.exp (-7/100) ≤ (93239381991/100000000000) := by
  have h := exp_enclosure16 (-7/100) (6222715977319/6250000000000) (19912691127421/20000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((9323938199/10000000000):ℝ) ≤ (6222715977319/6250000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((19912691127421/20000000000000):ℝ)^16 ≤ (93239381991/100000000000))⟩

theorem rescue_exp_1 : (174823743/50000000000) ≤ Real.exp (-707/125) ∧ Real.exp (-707/125) ≤ (349647487/100000000000) := by
  have h := exp_enclosure16 (-707/125) (14044519851761/20000000000000) (70222599258807/100000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((174823743/50000000000):ℝ) ≤ (14044519851761/20000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((70222599258807/100000000000000):ℝ)^16 ≤ (349647487/100000000000))⟩

theorem rescue_exp_2 : (2695231/12500000000) ≤ Real.exp (-4221/500) ∧ Real.exp (-4221/500) ≤ (21561849/100000000000) := by
  have h := exp_enclosure16 (-4221/500) (59000456784429/100000000000000) (59000456784641/100000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((2695231/12500000000):ℝ) ≤ (59000456784429/100000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((59000456784641/100000000000000):ℝ)^16 ≤ (21561849/100000000000))⟩

theorem rescue_exp_3 : (21865837/100000000000) ≤ Real.exp (-2107/250) ∧ Real.exp (-2107/250) ≤ (10932919/50000000000) := by
  have h := exp_enclosure16 (-2107/250) (59052104776821/100000000000000) (14763026194257/25000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((21865837/100000000000):ℝ) ≤ (59052104776821/100000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((14763026194257/25000000000000):ℝ)^16 ≤ (10932919/50000000000))⟩

theorem rescue_exp_4 : (45580679/12500000000) ≤ Real.exp (-2807/500) ∧ Real.exp (-2807/500) ≤ (364645433/100000000000) := by
  have h := exp_enclosure16 (-2807/500) (35203587866247/50000000000000) (4400448483281/6250000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((45580679/12500000000):ℝ) ≤ (35203587866247/50000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((4400448483281/6250000000000):ℝ)^16 ≤ (364645433/100000000000))⟩

theorem rescue_exp_5 : (114472743/6250000000) ≤ Real.exp (-4/1) ∧ Real.exp (-4/1) ≤ (1831563889/100000000000) := by
  have h := exp_enclosure16 (-4/1) (3894003915357/5000000000000) (77880078307141/100000000000000)
    (by norm_num) (by norm_num)
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
    (by norm_num [taylor12,error12,Finset.sum_range_succ,Nat.factorial])
  exact ⟨(by norm_num : ((114472743/6250000000):ℝ) ≤ (3894003915357/5000000000000)^16).trans h.1,
    h.2.trans (by norm_num : ((77880078307141/100000000000000):ℝ)^16 ≤ (1831563889/100000000000))⟩

def rescue_blank : ℝ := (116683381/111921381)*Real.exp (-7/100) +
    (5776405/374319)*Real.exp (-707/125) +
    (1207010/59501)*Real.exp (-4221/500) +
    (-405010/19701)*Real.exp (-2107/250) +
    (-1505/99)*Real.exp (-2807/500)
def rescue_loaded : ℝ := (116683381/111921381)*Real.exp (-7/100) +
    (-1838052071/374319)*Real.exp (-707/125) +
    (-744242366/6009601)*Real.exp (-4221/500) +
    (67136222/439989)*Real.exp (-2107/250) +
    (1097559347/223311)*Real.exp (-2807/500)
theorem rescue_blank_exact : blank5 7 = 1-rescue_blank := by
  unfold blank5
  rw [capacity5_survival]
  norm_num [rescue_blank,eigen5,modes5,Fin.sum_univ_succ]
  ring
theorem rescue_miss_exact : miss5 7 = Real.exp (-4)*rescue_loaded := by
  unfold miss5
  rw [show kernel5 = birthKernel rates5 rates5_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight 4 n * kernel5.poissonized
    ((5/2)*7) uncalled (loadIndex n)) = _
  simp_rw [capacity5_survival]
  norm_num [rescue_loaded,eigen5,modes5,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring
theorem rescue_source_bounds : blank5 7 < 3/100 ∧ miss5 7 < 4/125 ∧ Real.exp (-4) < 19/1000 := by
  have h0 := rescue_exp_0
  have h1 := rescue_exp_1
  have h2 := rescue_exp_2
  have h3 := rescue_exp_3
  have h4 := rescue_exp_4
  have h5 := rescue_exp_5
  have hb : 97/100 < rescue_blank := by
    unfold rescue_blank
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hm : rescue_loaded < 174/100 := by
    unfold rescue_loaded
    linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  refine ⟨?_,?_,by linarith [h5.2]⟩
  · rw [rescue_blank_exact]; linarith
  · rw [rescue_miss_exact]
    nlinarith [mul_pos (Real.exp_pos (-4)) (sub_pos.mpr hm), h5.2]

end AssayInformation
