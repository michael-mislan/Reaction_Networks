import proofs.CompositionalMemory.SemenovLowInitialMetric
import proofs.CompositionalMemory.SemenovLowMetric01
import proofs.CompositionalMemory.SemenovLowMetric02
import proofs.CompositionalMemory.SemenovLowMetric03
import proofs.CompositionalMemory.SemenovLowMetric04
import proofs.CompositionalMemory.SemenovLowMetric05
import proofs.CompositionalMemory.SemenovLowMetric06
import proofs.CompositionalMemory.SemenovLowMetric07
import proofs.CompositionalMemory.SemenovLowMetric08
import proofs.CompositionalMemory.SemenovLowMetric09
import proofs.CompositionalMemory.SemenovLowMetric10
import proofs.CompositionalMemory.SemenovLowMetric11
import proofs.CompositionalMemory.SemenovLowMetric12
import proofs.CompositionalMemory.SemenovLowMetric13
import proofs.CompositionalMemory.SemenovLowMetric14
import proofs.CompositionalMemory.SemenovLowMetric15
import proofs.CompositionalMemory.SemenovHighInitialMetric
import proofs.CompositionalMemory.SemenovHighMetric01
import proofs.CompositionalMemory.SemenovHighMetric02
import proofs.CompositionalMemory.SemenovHighMetric03
import proofs.CompositionalMemory.SemenovHighMetric04
import proofs.CompositionalMemory.SemenovHighMetric05
import proofs.CompositionalMemory.SemenovHighMetric06
import proofs.CompositionalMemory.SemenovHighMetric07
import proofs.CompositionalMemory.SemenovHighMetric08
import proofs.CompositionalMemory.SemenovHighMetric09
import proofs.CompositionalMemory.SemenovHighMetric10
import proofs.CompositionalMemory.SemenovHighMetric11
import proofs.CompositionalMemory.SemenovHighMetric12
import proofs.CompositionalMemory.SemenovHighMetric13
import proofs.CompositionalMemory.SemenovHighMetric14
import proofs.CompositionalMemory.SemenovHighMetric15
import proofs.CompositionalMemory.SemenovHighMetric16
import proofs.CompositionalMemory.SemenovHighMetric17
import proofs.CompositionalMemory.SemenovHighMetric18
import proofs.CompositionalMemory.SemenovHighMetric19
import proofs.CompositionalMemory.SemenovHighMetric20
import proofs.CompositionalMemory.SemenovHighMetric21

namespace CompositionalMemory.Semenov.SemenovCoverChecks

def low_leftTime : Fin 16 → ℚ := ![SemenovLowInitialMetric.leftTime,SemenovLowMetric01.leftTime,SemenovLowMetric02.leftTime,SemenovLowMetric03.leftTime,SemenovLowMetric04.leftTime,SemenovLowMetric05.leftTime,SemenovLowMetric06.leftTime,SemenovLowMetric07.leftTime,SemenovLowMetric08.leftTime,SemenovLowMetric09.leftTime,SemenovLowMetric10.leftTime,SemenovLowMetric11.leftTime,SemenovLowMetric12.leftTime,SemenovLowMetric13.leftTime,SemenovLowMetric14.leftTime,SemenovLowMetric15.leftTime]
def low_rightTime : Fin 16 → ℚ := ![SemenovLowInitialMetric.rightTime,SemenovLowMetric01.rightTime,SemenovLowMetric02.rightTime,SemenovLowMetric03.rightTime,SemenovLowMetric04.rightTime,SemenovLowMetric05.rightTime,SemenovLowMetric06.rightTime,SemenovLowMetric07.rightTime,SemenovLowMetric08.rightTime,SemenovLowMetric09.rightTime,SemenovLowMetric10.rightTime,SemenovLowMetric11.rightTime,SemenovLowMetric12.rightTime,SemenovLowMetric13.rightTime,SemenovLowMetric14.rightTime,SemenovLowMetric15.rightTime]
def low_zl : Fin 16 → Fin 8 → ℚ := ![SemenovLowInitialMetric.zl,SemenovLowMetric01.zl,SemenovLowMetric02.zl,SemenovLowMetric03.zl,SemenovLowMetric04.zl,SemenovLowMetric05.zl,SemenovLowMetric06.zl,SemenovLowMetric07.zl,SemenovLowMetric08.zl,SemenovLowMetric09.zl,SemenovLowMetric10.zl,SemenovLowMetric11.zl,SemenovLowMetric12.zl,SemenovLowMetric13.zl,SemenovLowMetric14.zl,SemenovLowMetric15.zl]
def low_zr : Fin 16 → Fin 8 → ℚ := ![SemenovLowInitialMetric.zr,SemenovLowMetric01.zr,SemenovLowMetric02.zr,SemenovLowMetric03.zr,SemenovLowMetric04.zr,SemenovLowMetric05.zr,SemenovLowMetric06.zr,SemenovLowMetric07.zr,SemenovLowMetric08.zr,SemenovLowMetric09.zr,SemenovLowMetric10.zr,SemenovLowMetric11.zr,SemenovLowMetric12.zr,SemenovLowMetric13.zr,SemenovLowMetric14.zr,SemenovLowMetric15.zr]
def low_pl : Fin 16 → Fin 8 → Fin 8 → ℚ := ![SemenovLowInitialMetric.pl,SemenovLowMetric01.pl,SemenovLowMetric02.pl,SemenovLowMetric03.pl,SemenovLowMetric04.pl,SemenovLowMetric05.pl,SemenovLowMetric06.pl,SemenovLowMetric07.pl,SemenovLowMetric08.pl,SemenovLowMetric09.pl,SemenovLowMetric10.pl,SemenovLowMetric11.pl,SemenovLowMetric12.pl,SemenovLowMetric13.pl,SemenovLowMetric14.pl,SemenovLowMetric15.pl]
def low_pr : Fin 16 → Fin 8 → Fin 8 → ℚ := ![SemenovLowInitialMetric.pr,SemenovLowMetric01.pr,SemenovLowMetric02.pr,SemenovLowMetric03.pr,SemenovLowMetric04.pr,SemenovLowMetric05.pr,SemenovLowMetric06.pr,SemenovLowMetric07.pr,SemenovLowMetric08.pr,SemenovLowMetric09.pr,SemenovLowMetric10.pr,SemenovLowMetric11.pr,SemenovLowMetric12.pr,SemenovLowMetric13.pr,SemenovLowMetric14.pr,SemenovLowMetric15.pr]
def low_zc : Fin 16 → Fin 8 → Fin 17 → ℚ := ![SemenovLowInitialMetric.zc,SemenovLowMetric01.zc,SemenovLowMetric02.zc,SemenovLowMetric03.zc,SemenovLowMetric04.zc,SemenovLowMetric05.zc,SemenovLowMetric06.zc,SemenovLowMetric07.zc,SemenovLowMetric08.zc,SemenovLowMetric09.zc,SemenovLowMetric10.zc,SemenovLowMetric11.zc,SemenovLowMetric12.zc,SemenovLowMetric13.zc,SemenovLowMetric14.zc,SemenovLowMetric15.zc]
def low_radius : Fin 16 → ℚ := ![SemenovLowInitialMetric.radius,SemenovLowMetric01.radius,SemenovLowMetric02.radius,SemenovLowMetric03.radius,SemenovLowMetric04.radius,SemenovLowMetric05.radius,SemenovLowMetric06.radius,SemenovLowMetric07.radius,SemenovLowMetric08.radius,SemenovLowMetric09.radius,SemenovLowMetric10.radius,SemenovLowMetric11.radius,SemenovLowMetric12.radius,SemenovLowMetric13.radius,SemenovLowMetric14.radius,SemenovLowMetric15.radius]

theorem low_checks :
    (low_leftTime 0=0 ∧ low_rightTime 15=500) ∧
    (∀ i : Fin 15,low_rightTime i.castSucc=low_leftTime i.succ) ∧
    (∀ i : Fin 15,∀ j,low_zr i.castSucc j=low_zl i.succ j) ∧
    (∀ i : Fin 15,∀ j k,low_pr i.castSucc j k=low_pl i.succ j k) ∧
    (∀ i j,(24000000000000000000 : ℚ)*coordinateUpper (low_zc i) (low_radius i) j+1 ≤
      (20000000000000000000 : ℚ)) := by native_decide

def high_leftTime : Fin 22 → ℚ := ![SemenovHighInitialMetric.leftTime,SemenovHighMetric01.leftTime,SemenovHighMetric02.leftTime,SemenovHighMetric03.leftTime,SemenovHighMetric04.leftTime,SemenovHighMetric05.leftTime,SemenovHighMetric06.leftTime,SemenovHighMetric07.leftTime,SemenovHighMetric08.leftTime,SemenovHighMetric09.leftTime,SemenovHighMetric10.leftTime,SemenovHighMetric11.leftTime,SemenovHighMetric12.leftTime,SemenovHighMetric13.leftTime,SemenovHighMetric14.leftTime,SemenovHighMetric15.leftTime,SemenovHighMetric16.leftTime,SemenovHighMetric17.leftTime,SemenovHighMetric18.leftTime,SemenovHighMetric19.leftTime,SemenovHighMetric20.leftTime,SemenovHighMetric21.leftTime]
def high_rightTime : Fin 22 → ℚ := ![SemenovHighInitialMetric.rightTime,SemenovHighMetric01.rightTime,SemenovHighMetric02.rightTime,SemenovHighMetric03.rightTime,SemenovHighMetric04.rightTime,SemenovHighMetric05.rightTime,SemenovHighMetric06.rightTime,SemenovHighMetric07.rightTime,SemenovHighMetric08.rightTime,SemenovHighMetric09.rightTime,SemenovHighMetric10.rightTime,SemenovHighMetric11.rightTime,SemenovHighMetric12.rightTime,SemenovHighMetric13.rightTime,SemenovHighMetric14.rightTime,SemenovHighMetric15.rightTime,SemenovHighMetric16.rightTime,SemenovHighMetric17.rightTime,SemenovHighMetric18.rightTime,SemenovHighMetric19.rightTime,SemenovHighMetric20.rightTime,SemenovHighMetric21.rightTime]
def high_zl : Fin 22 → Fin 8 → ℚ := ![SemenovHighInitialMetric.zl,SemenovHighMetric01.zl,SemenovHighMetric02.zl,SemenovHighMetric03.zl,SemenovHighMetric04.zl,SemenovHighMetric05.zl,SemenovHighMetric06.zl,SemenovHighMetric07.zl,SemenovHighMetric08.zl,SemenovHighMetric09.zl,SemenovHighMetric10.zl,SemenovHighMetric11.zl,SemenovHighMetric12.zl,SemenovHighMetric13.zl,SemenovHighMetric14.zl,SemenovHighMetric15.zl,SemenovHighMetric16.zl,SemenovHighMetric17.zl,SemenovHighMetric18.zl,SemenovHighMetric19.zl,SemenovHighMetric20.zl,SemenovHighMetric21.zl]
def high_zr : Fin 22 → Fin 8 → ℚ := ![SemenovHighInitialMetric.zr,SemenovHighMetric01.zr,SemenovHighMetric02.zr,SemenovHighMetric03.zr,SemenovHighMetric04.zr,SemenovHighMetric05.zr,SemenovHighMetric06.zr,SemenovHighMetric07.zr,SemenovHighMetric08.zr,SemenovHighMetric09.zr,SemenovHighMetric10.zr,SemenovHighMetric11.zr,SemenovHighMetric12.zr,SemenovHighMetric13.zr,SemenovHighMetric14.zr,SemenovHighMetric15.zr,SemenovHighMetric16.zr,SemenovHighMetric17.zr,SemenovHighMetric18.zr,SemenovHighMetric19.zr,SemenovHighMetric20.zr,SemenovHighMetric21.zr]
def high_pl : Fin 22 → Fin 8 → Fin 8 → ℚ := ![SemenovHighInitialMetric.pl,SemenovHighMetric01.pl,SemenovHighMetric02.pl,SemenovHighMetric03.pl,SemenovHighMetric04.pl,SemenovHighMetric05.pl,SemenovHighMetric06.pl,SemenovHighMetric07.pl,SemenovHighMetric08.pl,SemenovHighMetric09.pl,SemenovHighMetric10.pl,SemenovHighMetric11.pl,SemenovHighMetric12.pl,SemenovHighMetric13.pl,SemenovHighMetric14.pl,SemenovHighMetric15.pl,SemenovHighMetric16.pl,SemenovHighMetric17.pl,SemenovHighMetric18.pl,SemenovHighMetric19.pl,SemenovHighMetric20.pl,SemenovHighMetric21.pl]
def high_pr : Fin 22 → Fin 8 → Fin 8 → ℚ := ![SemenovHighInitialMetric.pr,SemenovHighMetric01.pr,SemenovHighMetric02.pr,SemenovHighMetric03.pr,SemenovHighMetric04.pr,SemenovHighMetric05.pr,SemenovHighMetric06.pr,SemenovHighMetric07.pr,SemenovHighMetric08.pr,SemenovHighMetric09.pr,SemenovHighMetric10.pr,SemenovHighMetric11.pr,SemenovHighMetric12.pr,SemenovHighMetric13.pr,SemenovHighMetric14.pr,SemenovHighMetric15.pr,SemenovHighMetric16.pr,SemenovHighMetric17.pr,SemenovHighMetric18.pr,SemenovHighMetric19.pr,SemenovHighMetric20.pr,SemenovHighMetric21.pr]
def high_zc : Fin 22 → Fin 8 → Fin 17 → ℚ := ![SemenovHighInitialMetric.zc,SemenovHighMetric01.zc,SemenovHighMetric02.zc,SemenovHighMetric03.zc,SemenovHighMetric04.zc,SemenovHighMetric05.zc,SemenovHighMetric06.zc,SemenovHighMetric07.zc,SemenovHighMetric08.zc,SemenovHighMetric09.zc,SemenovHighMetric10.zc,SemenovHighMetric11.zc,SemenovHighMetric12.zc,SemenovHighMetric13.zc,SemenovHighMetric14.zc,SemenovHighMetric15.zc,SemenovHighMetric16.zc,SemenovHighMetric17.zc,SemenovHighMetric18.zc,SemenovHighMetric19.zc,SemenovHighMetric20.zc,SemenovHighMetric21.zc]
def high_radius : Fin 22 → ℚ := ![SemenovHighInitialMetric.radius,SemenovHighMetric01.radius,SemenovHighMetric02.radius,SemenovHighMetric03.radius,SemenovHighMetric04.radius,SemenovHighMetric05.radius,SemenovHighMetric06.radius,SemenovHighMetric07.radius,SemenovHighMetric08.radius,SemenovHighMetric09.radius,SemenovHighMetric10.radius,SemenovHighMetric11.radius,SemenovHighMetric12.radius,SemenovHighMetric13.radius,SemenovHighMetric14.radius,SemenovHighMetric15.radius,SemenovHighMetric16.radius,SemenovHighMetric17.radius,SemenovHighMetric18.radius,SemenovHighMetric19.radius,SemenovHighMetric20.radius,SemenovHighMetric21.radius]

theorem high_checks :
    (high_leftTime 0=0 ∧ high_rightTime 21=500) ∧
    (∀ i : Fin 21,high_rightTime i.castSucc=high_leftTime i.succ) ∧
    (∀ i : Fin 21,∀ j,high_zr i.castSucc j=high_zl i.succ j) ∧
    (∀ i : Fin 21,∀ j k,high_pr i.castSucc j k=high_pl i.succ j k) ∧
    (∀ i j,(24000000000000000000 : ℚ)*coordinateUpper (high_zc i) (high_radius i) j+1 ≤
      (20000000000000000000 : ℚ)) := by native_decide

end CompositionalMemory.Semenov.SemenovCoverChecks
