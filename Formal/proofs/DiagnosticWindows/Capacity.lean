import proofs.DiagnosticWindows.BirthSource

set_option maxRecDepth 4096
noncomputable section
namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

def rates10 : Fin 6 → ℝ := ![(1/250), (909/2500), (402/625), (2107/2500), (1203/1250), 0]
theorem rates10_valid (z : Fin 6) : rates10 z ∈ Set.Icc 0 1 := by
  fin_cases z <;> norm_num [rates10]
noncomputable def kernel10 := birthKernel rates10 rates10_valid
def modes10 : Fin 5 → Fin 6 → ℝ := ![![(102914742042/100251115667), 0, 0, 0, 0, 0],
  ![(-4528701520/62609895767), (452870152/69643933), 0, 0, 0, 0],
  ![(182862015/1765049327), (-36572403/2209073), (120701/9481), 0, 0, 0],
  ![(-1953768240/20823535967), (1758391416/89371399), (-3868848/149201), (2406/299), 0, 0],
  ![(61106010/1698056581), (-24442404/2834819), (80668/5681), (-2107/299), 1, 0]]
def eigen10 : Fin 5 → ℝ := ![(249/250), (1591/2500), (223/625), (393/2500), (47/1250)]
theorem capacity10_rates (z : Fin 6) (hz : z ≠ 5) :
    (5/2:ℝ)*rates10 z = (1/100+(z.val:ℝ))*(10-(z.val:ℝ))/10 := by
  fin_cases z <;> norm_num [rates10,Fin.ext_iff] at *
theorem capacity10_sum (z : Fin 6) : uncalled z = ∑ i, modes10 i z := by
  fin_cases z <;> norm_num [uncalled,modes10,Fin.sum_univ_succ]
theorem capacity10_eigen (i : Fin 5) (z : Fin 6) :
    kernel10.step (modes10 i) z = eigen10 i*modes10 i z := by
  fin_cases i <;> fin_cases z <;>
    norm_num [kernel10,birthKernel,FiniteKernel.step,rates10,modes10,eigen10,Fin.sum_univ_succ]
theorem capacity10_survival (t : NNReal) (z : Fin 6) :
    kernel10.poissonized t uncalled z =
      ∑ i, Real.exp ((t:ℝ)*(eigen10 i-1))*modes10 i z :=
  spectral_survival kernel10 uncalled modes10 eigen10 capacity10_sum capacity10_eigen t z

def rates5 : Fin 6 → ℝ := ![(1/250), (202/625), (603/1250), (301/625), (401/1250), 0]
theorem rates5_valid (z : Fin 6) : rates5 z ∈ Set.Icc 0 1 := by
  fin_cases z <;> norm_num [rates5]
noncomputable def kernel5 := birthKernel rates5 rates5_valid
def modes5 : Fin 5 → Fin 6 → ℝ := ![![(116683381/111921381), 0, 0, 0, 0, 0],
  ![(5776405/374319), (-8086967/6567), 0, 0, 0, 0],
  ![(1207010/59501), (-482804/199), (120701/101), 0, 0, 0],
  ![(-405010/19701), (81002/33), -1203, (-401/201), 0, 0],
  ![(-1505/99), 1204, (903/101), (602/201), 1, 0]]
def eigen5 : Fin 5 → ℝ := ![(249/250), (423/625), (647/1250), (324/625), (849/1250)]
theorem capacity5_rates (z : Fin 6) (hz : z ≠ 5) :
    (5/2:ℝ)*rates5 z = (1/100+(z.val:ℝ))*(5-(z.val:ℝ))/5 := by
  fin_cases z <;> norm_num [rates5,Fin.ext_iff] at *
theorem capacity5_sum (z : Fin 6) : uncalled z = ∑ i, modes5 i z := by
  fin_cases z <;> norm_num [uncalled,modes5,Fin.sum_univ_succ]
theorem capacity5_eigen (i : Fin 5) (z : Fin 6) :
    kernel5.step (modes5 i) z = eigen5 i*modes5 i z := by
  fin_cases i <;> fin_cases z <;>
    norm_num [kernel5,birthKernel,FiniteKernel.step,rates5,modes5,eigen5,Fin.sum_univ_succ]
theorem capacity5_survival (t : NNReal) (z : Fin 6) :
    kernel5.poissonized t uncalled z =
      ∑ i, Real.exp ((t:ℝ)*(eigen5 i-1))*modes5 i z :=
  spectral_survival kernel5 uncalled modes5 eigen5 capacity5_sum capacity5_eigen t z

end DiagnosticWindows
