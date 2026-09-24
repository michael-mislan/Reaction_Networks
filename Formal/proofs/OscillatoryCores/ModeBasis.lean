import proofs.OscillatoryCores.StableRoots
import proofs.OscillatoryCores.MovingModes

namespace OscillatoryCores

open scoped Matrix BigOperators

theorem stable_real_eigenvector {t l : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t=0) (hl : l^2+a1 t*l+stableConstant t=0) :
    ∃ e : State, e ≠ 0 ∧ normalizedLinear t e = l • e := by
  have hd : (characteristicMatrix t l).det=0 := by
    rw [characteristic_determinant,crossing_factorization ht hz]
    change (l^2+a3 t/a1 t)*(l^2+a1 t*l+stableConstant t)=0
    rw [hl,mul_zero]
  rw [characteristicMatrix_eq] at hd
  obtain ⟨e,he,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨e,he,?_⟩
  rw [normalizedLinear_apply]
  simpa only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero,eq_comm] using hker

theorem two_real_modes_independent (L : State →L[ℝ] State)
    {l m a b : ℝ} {e f : State} (hlm : l ≠ m) (he : e ≠ 0) (hf : f ≠ 0)
    (hLe : L e = l • e) (hLf : L f = m • f)
    (h : a • e+b • f=0) : a=0 ∧ b=0 := by
  have hL := congrArg L h
  simp only [map_add,map_smul,map_zero,hLe,hLf] at hL
  have hae : (a*(l-m)) • e=0 := by
    calc
      (a*(l-m)) • e = (a • (l • e)+b • (m • f))-m • (a • e+b • f) := by module
      _ = 0 := by rw [hL,h,smul_zero,sub_self]
  have ha : a=0 := (mul_eq_zero.mp ((smul_eq_zero.mp hae).resolve_right he)).resolve_right
    (sub_ne_zero.mpr hlm)
  refine ⟨ha,?_⟩
  rw [ha,zero_smul,zero_add] at h
  exact (smul_eq_zero.mp h).resolve_right hf

theorem center_modes_independent (L : State →L[ℝ] State)
    {w a b : ℝ} {u v : State} (hw : w ≠ 0) (hu : u ≠ 0)
    (hLu : L u = -w • v) (hLv : L v = w • u)
    (h : a • u+b • v=0) : a=0 ∧ b=0 := by
  have hL := congrArg L h
  simp only [map_add,map_smul,map_zero,hLu,hLv] at hL
  have hs : (w*(a^2+b^2)) • u=0 := by
    calc
      (w*(a^2+b^2)) • u = (a*w) • (a • u+b • v) + b • (a • (-w • v)+b • (w • u)) := by module
      _ = 0 := by rw [h,hL,smul_zero,smul_zero,add_zero]
  have hz := (mul_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hu)).resolve_left hw
  constructor <;> nlinarith [sq_nonneg a,sq_nonneg b]

theorem four_modes_independent (L : State →L[ℝ] State)
    {w l m a b c d : ℝ} {u v e f : State} (hw : w ≠ 0) (hlm : l ≠ m)
    (hu : u ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hLu : L u = -w • v) (hLv : L v = w • u)
    (hLe : L e = l • e) (hLf : L f = m • f)
    (h : a • u+b • v+c • e+d • f=0) : a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  have hLL := congrArg (fun x => L (L x)+w^2 • x) h
  simp only [map_add,map_smul,map_zero,hLu,hLv,hLe,hLf,smul_zero,add_zero] at hLL
  have hstable : (c*(l^2+w^2)) • e+(d*(m^2+w^2)) • f=0 := by
    calc
      _ = (a • (-w • (w • u)) + b • (w • (-w • v)) +
        c • (l • (l • e)) + d • (m • (m • f))) +
          w^2 • (a • u+b • v+c • e+d • f) := by module
      _ = 0 := hLL
  obtain ⟨hc,hd⟩ := two_real_modes_independent L hlm he hf hLe hLf hstable
  have hlpos : 0 < l^2+w^2 := by nlinarith [sq_pos_of_ne_zero hw,sq_nonneg l]
  have hmpos : 0 < m^2+w^2 := by nlinarith [sq_pos_of_ne_zero hw,sq_nonneg m]
  have hc0 : c=0 := (mul_eq_zero.mp hc).resolve_right (ne_of_gt hlpos)
  have hd0 : d=0 := (mul_eq_zero.mp hd).resolve_right (ne_of_gt hmpos)
  simp only [hc0,hd0,zero_smul,add_zero] at h
  obtain ⟨ha,hb⟩ := center_modes_independent L hw hu hLu hLv h
  exact ⟨ha,hb,hc0,hd0⟩

end OscillatoryCores
