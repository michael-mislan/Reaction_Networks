import proofs.DiagnosticWindows.Capacity
import proofs.DiagnosticWindows.Loading

set_option maxRecDepth 4096
noncomputable section
namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

def blank10 (t : NNReal) : ℝ := 1-kernel10.poissonized ((5/2)*t) uncalled 0
def miss10 (t : NNReal) : ℝ := loadedSurvival kernel10 4 ((5/2)*t)
def blankSum10 : ℝ := (102914742042/100251115667)*Real.exp (-4/125) +
      (-4528701520/62609895767)*Real.exp (-1818/625) +
      (182862015/1765049327)*Real.exp (-3216/625) +
      (-1953768240/20823535967)*Real.exp (-4214/625) +
      (61106010/1698056581)*Real.exp (-4812/625)
def targetSum10 : ℝ := (102914742042/100251115667)*Real.exp (-4/125) +
      (1623992365072/62609895767)*Real.exp (-1818/625) +
      (63061806563/1765049327)*Real.exp (-3216/625) +
      (-38934745328/905371129)*Real.exp (-4214/625) +
      (3243570002/221485641)*Real.exp (-4812/625)
theorem blank10_exact : blank10 (16/5) = 1-blankSum10 := by
  unfold blank10
  rw [capacity10_survival]
  norm_num [blankSum10,eigen10,modes10,Fin.sum_univ_succ]
  ring
theorem miss10_exact : miss10 (16/5) = Real.exp (-4)*targetSum10 := by
  unfold miss10
  rw [show kernel10 = birthKernel rates10 rates10_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight 4 n * kernel10.poissonized
    ((5/2)*(16/5)) uncalled (loadIndex n)) = _
  simp_rw [capacity10_survival]
  norm_num [targetSum10,eigen10,modes10,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring

def blank5 (t : NNReal) : ℝ := 1-kernel5.poissonized ((5/2)*t) uncalled 0
def miss5 (t : NNReal) : ℝ := loadedSurvival kernel5 4 ((5/2)*t)
def blankSum5 : ℝ := (116683381/111921381)*Real.exp (-1/20) +
      (5776405/374319)*Real.exp (-101/25) +
      (1207010/59501)*Real.exp (-603/100) +
      (-405010/19701)*Real.exp (-301/50) +
      (-1505/99)*Real.exp (-401/100)
def targetSum5 : ℝ := (116683381/111921381)*Real.exp (-1/20) +
      (-1838052071/374319)*Real.exp (-101/25) +
      (-744242366/6009601)*Real.exp (-603/100) +
      (67136222/439989)*Real.exp (-301/50) +
      (1097559347/223311)*Real.exp (-401/100)
theorem blank5_exact : blank5 5 = 1-blankSum5 := by
  unfold blank5
  rw [capacity5_survival]
  norm_num [blankSum5,eigen5,modes5,Fin.sum_univ_succ]
  ring
theorem miss5_exact : miss5 5 = Real.exp (-4)*targetSum5 := by
  unfold miss5
  rw [show kernel5 = birthKernel rates5 rates5_valid from rfl,loading_finite]
  change (∑ n ∈ Finset.range 5, poissonWeight 4 n * kernel5.poissonized
    ((5/2)*5) uncalled (loadIndex n)) = _
  simp_rw [capacity5_survival]
  norm_num [targetSum5,eigen5,modes5,Fin.sum_univ_succ,
    Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  ring

end DiagnosticWindows
