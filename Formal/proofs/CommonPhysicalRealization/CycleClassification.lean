import proofs.CommonPhysicalRealization.ExporterThermochemistry

namespace CommonPhysicalRealization
noncomputable section
open scoped BigOperators

def fullNet (c : Fin 6 → ℝ) (i : Fin 8) : ℝ :=
  ∑ j, ((pairRight j i:ℝ)-pairLeft j i)*c j

def internalNet (c : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![-c 0-c 1+c 5,-c 0-c 2+c 5,c 0-c 1+2*c 4-c 5,
    c 1-c 2,c 2-c 3,c 3-c 4]

theorem net_expansion (c : Fin 6 → ℝ) :
    fullNet c = ![-c 0-c 1+c 5,-c 0-c 2+c 5,c 0-c 1+2*c 4-c 5,
      c 1-c 2,c 2-c 3,c 3-c 4,-c 5,c 5] := by
  funext i
  fin_cases i <;>
    simp [fullNet,pairRight,pairLeft,Fin.sum_univ_succ] <;> ring

def cycleCombination (a b : ℝ) : Fin 6 → ℝ := ![-a+b,a,a,a,a,b]

theorem internal_kernel_classification (c : Fin 6 → ℝ) :
    internalNet c = 0 ↔ c = cycleCombination (c 1) (c 5) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h5 := congrFun h 5
    change -c 0-c 1+c 5=0 at h0
    change c 1-c 2=0 at h3
    change c 2-c 3=0 at h4
    change c 3-c 4=0 at h5
    funext i
    fin_cases i
    · change c 0= -c 1+c 5; linarith
    · rfl
    · change c 2=c 1; linarith
    · change c 3=c 1; linarith
    · change c 4=c 1; linarith
    · rfl
  · intro h
    rw [h]
    funext i
    fin_cases i <;> simp [internalNet,cycleCombination]
    ring

theorem full_cycle_action (a b : ℝ) :
    fullNet (cycleCombination a b) = ![0,0,0,0,0,0,-b,b] := by
  rw [net_expansion]
  funext i
  fin_cases i <;> simp [cycleCombination]
  ring

theorem full_kernel_classification (c : Fin 6 → ℝ) :
    fullNet c = 0 ↔ c = cycleCombination (c 1) 0 := by
  constructor
  · intro h
    have hi : internalNet c=0 := by
      funext i
      have hh := congrFun h (i.castLE (by decide))
      rw [net_expansion] at hh
      fin_cases i <;> exact hh
    have hb := congrFun h 7
    rw [net_expansion] at hb
    change c 5=0 at hb
    simpa only [hb] using internal_kernel_classification c |>.mp hi
  · intro h
    rw [h,full_cycle_action]
    funext i
    fin_cases i <;> norm_num

def pairAffinity : Fin 6 → ℝ :=
  ![Real.log 10,0,0,Real.log 10,0,Real.log 8000000000]
def cycleAffinity (c : Fin 6 → ℝ) : ℝ := ∑ j,c j*pairAffinity j

theorem cycle_force (a b : ℝ) :
    cycleAffinity (cycleCombination a b)=b*Real.log 80000000000 := by
  have hh : Real.log 10+Real.log 8000000000=Real.log 80000000000 := by
    rw [← Real.log_mul (by norm_num : (10:ℝ)≠0) (by norm_num : (8000000000:ℝ)≠0)]
    norm_num
  simp [cycleAffinity,cycleCombination,pairAffinity,Fin.sum_univ_succ]
  rw [← hh]
  ring

end
end CommonPhysicalRealization
