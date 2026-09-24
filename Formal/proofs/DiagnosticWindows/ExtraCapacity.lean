import proofs.DiagnosticWindows.BirthSource

set_option maxRecDepth 4096
noncomputable section
namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

def rates6 : Fin 6 → ℝ := ![(1/250), (101/300), (67/125), (301/500), (401/750), 0]
theorem rates6_valid (z : Fin 6) : rates6 z ∈ Set.Icc 0 1 := by
  fin_cases z <;> norm_num [rates6]
noncomputable def kernel6 := birthKernel rates6 rates6_valid
def modes6 : Fin 5 → Fin 6 → ℝ := ![![(583416905/564128981), 0, 0, 0, 0, 0],
  ![(-64695736/326600989), (32347868/1963533), 0, 0, 0, 0],
  ![(-8707715/187473), (60954005/9867), (-120701/33), 0, 0, 0],
  ![(1074680/1963533), (-537340/6567), (214936/3333), (-802/101), 0, 0],
  ![(100835/2189), (-201670/33), (363006/101), (903/101), 1, 0]]
def eigen6 : Fin 5 → ℝ := ![(249/250), (199/300), (58/125), (199/500), (349/750)]
theorem capacity6_rates (z : Fin 6) (hz : z ≠ 5) :
    (5/2:ℝ)*rates6 z = (1/100+(z.val:ℝ))*(6-(z.val:ℝ))/6 := by
  fin_cases z <;> norm_num [rates6,Fin.ext_iff] at *
theorem capacity6_sum (z : Fin 6) : uncalled z = ∑ i, modes6 i z := by
  fin_cases z <;> norm_num [uncalled,modes6,Fin.sum_univ_succ]
theorem capacity6_eigen (i : Fin 5) (z : Fin 6) :
    kernel6.step (modes6 i) z = eigen6 i*modes6 i z := by
  fin_cases i <;> fin_cases z <;>
    norm_num [kernel6,birthKernel,FiniteKernel.step,rates6,modes6,eigen6,Fin.sum_univ_succ]
theorem capacity6_survival (t : NNReal) (z : Fin 6) :
    kernel6.poissonized t uncalled z =
      ∑ i, Real.exp ((t:ℝ)*(eigen6 i-1))*modes6 i z :=
  spectral_survival kernel6 uncalled modes6 eigen6 capacity6_sum capacity6_eigen t z

def rates7 : Fin 6 → ℝ := ![(1/250), (303/875), (201/350), (86/125), (1203/1750), 0]
theorem rates7_valid (z : Fin 6) : rates7 z ∈ Set.Icc 0 1 := by
  fin_cases z <;> norm_num [rates7]
noncomputable def kernel7 := birthKernel rates7 rates7_valid
def modes7 : Fin 5 → Fin 6 → ℝ := ![![(1750250715/1698056581), 0, 0, 0, 0, 0],
  ![(-80869670/677180881), (11552810/1130519), 0, 0, 0, 0],
  ![(24381602/62261727), (-6966172/124773), (241402/6567), 0, 0, 0],
  ![(40703505/1130519), (-366331545/59501), (1209015/199), -1203, 0, 0],
  ![(-71290345/1963533), (40737340/6567), (-201670/33), 1204, 1, 0]]
def eigen7 : Fin 5 → ℝ := ![(249/250), (572/875), (149/350), (39/125), (547/1750)]
theorem capacity7_rates (z : Fin 6) (hz : z ≠ 5) :
    (5/2:ℝ)*rates7 z = (1/100+(z.val:ℝ))*(7-(z.val:ℝ))/7 := by
  fin_cases z <;> norm_num [rates7,Fin.ext_iff] at *
theorem capacity7_sum (z : Fin 6) : uncalled z = ∑ i, modes7 i z := by
  fin_cases z <;> norm_num [uncalled,modes7,Fin.sum_univ_succ]
theorem capacity7_eigen (i : Fin 5) (z : Fin 6) :
    kernel7.step (modes7 i) z = eigen7 i*modes7 i z := by
  fin_cases i <;> fin_cases z <;>
    norm_num [kernel7,birthKernel,FiniteKernel.step,rates7,modes7,eigen7,Fin.sum_univ_succ]
theorem capacity7_survival (t : NNReal) (z : Fin 6) :
    kernel7.poissonized t uncalled z =
      ∑ i, Real.exp ((t:ℝ)*(eigen7 i-1))*modes7 i z :=
  spectral_survival kernel7 uncalled modes7 eigen7 capacity7_sum capacity7_eigen t z

def rates8 : Fin 6 → ℝ := ![(1/250), (707/2000), (603/1000), (301/400), (401/500), 0]
theorem rates8_valid (z : Fin 6) : rates8 z ∈ Set.Icc 0 1 := by
  fin_cases z <;> norm_num [rates8]
noncomputable def kernel8 := birthKernel rates8 rates8_valid
def modes8 : Fin 5 → Fin 6 → ℝ := ![![(4083918335/3969704181), 0, 0, 0, 0, 0],
  ![(-184844960/1981538481), (23105620/2834819), 0, 0, 0, 0],
  ![(3413424280/17784908401), (-853356070/29690999), (1207010/59501), 0, 0, 0],
  ![(-86834144/280647081), (10854268/187473), (-214936/3289), (1604/99), 0, 0],
  ![(20368670/111921381), (-71290345/1963533), (100835/2189), (-1505/99), 1, 0]]
def eigen8 : Fin 5 → ℝ := ![(249/250), (1293/2000), (397/1000), (99/400), (99/500)]
theorem capacity8_rates (z : Fin 6) (hz : z ≠ 5) :
    (5/2:ℝ)*rates8 z = (1/100+(z.val:ℝ))*(8-(z.val:ℝ))/8 := by
  fin_cases z <;> norm_num [rates8,Fin.ext_iff] at *
theorem capacity8_sum (z : Fin 6) : uncalled z = ∑ i, modes8 i z := by
  fin_cases z <;> norm_num [uncalled,modes8,Fin.sum_univ_succ]
theorem capacity8_eigen (i : Fin 5) (z : Fin 6) :
    kernel8.step (modes8 i) z = eigen8 i*modes8 i z := by
  fin_cases i <;> fin_cases z <;>
    norm_num [kernel8,birthKernel,FiniteKernel.step,rates8,modes8,eigen8,Fin.sum_univ_succ]
theorem capacity8_survival (t : NNReal) (z : Fin 6) :
    kernel8.poissonized t uncalled z =
      ∑ i, Real.exp ((t:ℝ)*(eigen8 i-1))*modes8 i z :=
  spectral_survival kernel8 uncalled modes8 eigen8 capacity8_sum capacity8_eigen t z

def rates9 : Fin 6 → ℝ := ![(1/250), (404/1125), (469/750), (301/375), (401/450), 0]
theorem rates9_valid (z : Fin 6) : rates9 z ∈ Set.Icc 0 1 := by
  fin_cases z <;> norm_num [rates9]
noncomputable def kernel9 := birthKernel rates9 rates9_valid
def modes9 : Fin 5 → Fin 6 → ℝ := ![![(57174856690/55645502467), 0, 0, 0, 0, 0],
  ![(-363913515/4537616081), (40434835/5679119), 0, 0, 0, 0],
  ![(104492580/792880127), (-69661720/3402919), (86215/5681), 0, 0, 0],
  ![(-162814020/1130144681), (54271340/1886719), (-134335/3781), (2005/199), 0, 0],
  ![(36663606/564128981), (-16294936/1130519), (1270521/59501), (-1806/199), 1, 0]]
def eigen9 : Fin 5 → ℝ := ![(249/250), (721/1125), (281/750), (74/375), (49/450)]
theorem capacity9_rates (z : Fin 6) (hz : z ≠ 5) :
    (5/2:ℝ)*rates9 z = (1/100+(z.val:ℝ))*(9-(z.val:ℝ))/9 := by
  fin_cases z <;> norm_num [rates9,Fin.ext_iff] at *
theorem capacity9_sum (z : Fin 6) : uncalled z = ∑ i, modes9 i z := by
  fin_cases z <;> norm_num [uncalled,modes9,Fin.sum_univ_succ]
theorem capacity9_eigen (i : Fin 5) (z : Fin 6) :
    kernel9.step (modes9 i) z = eigen9 i*modes9 i z := by
  fin_cases i <;> fin_cases z <;>
    norm_num [kernel9,birthKernel,FiniteKernel.step,rates9,modes9,eigen9,Fin.sum_univ_succ]
theorem capacity9_survival (t : NNReal) (z : Fin 6) :
    kernel9.poissonized t uncalled z =
      ∑ i, Real.exp ((t:ℝ)*(eigen9 i-1))*modes9 i z :=
  spectral_survival kernel9 uncalled modes9 eigen9 capacity9_sum capacity9_eigen t z

end DiagnosticWindows
