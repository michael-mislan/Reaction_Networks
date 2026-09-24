import Mathlib.Tactic

namespace ACRZeroDivisors

def reactorField (k1 k2 k3 k4 k5 D ci ell a b c : ℝ) : Fin 3 → ℝ :=
  ![-k1*a*b+k2*b-k4*a*c+k5*c+D*(ci-a)-ell*a,
    k1*a*b-(k2+k3+D)*b, k4*a*c-(k5+D)*c+k3*b]

theorem reactor_total (k1 k2 k3 k4 k5 D ci ell a b c : ℝ) :
    reactorField k1 k2 k3 k4 k5 D ci ell a b c 0 +
    reactorField k1 k2 k3 k4 k5 D ci ell a b c 1 +
    reactorField k1 k2 k3 k4 k5 D ci ell a b c 2 =
    D*(ci-a-b-c)-ell*a := by simp [reactorField]; ring

theorem reactor_equilibrium_reconstruction (alpha r N k1 k3 k4 D : ℝ)
    (hr : 1+r ≠ 0) :
    k1*(r*N/(1+r))*(alpha-alpha)=0 ∧
    k4*(N/(1+r))*(alpha-alpha)-(r*k3)*(N/(1+r))+k3*(r*N/(1+r))=0 ∧
    D*(N-r*N/(1+r)-N/(1+r))=0 := by
  constructor
  · ring
  constructor
  · ring
  · field_simp; ring

theorem reactor_positive_branch (b c delta k3 N : ℝ)
    (hb : 0 < b) (hc : 0 < c) (hk : 0 < k3)
    (hflux : delta*c=k3*b) (ht : b+c=N) :
    0 < delta ∧ 0 < N := by
  constructor
  · have : 0 < delta*c := by rw [hflux]; positivity
    exact (mul_pos_iff_of_pos_right hc).1 this
  · linarith

theorem reactor_unique_split (b c delta k3 N : ℝ)
    (hs : delta+k3 ≠ 0)
    (hflux : delta*c=k3*b) (ht : b+c=N) :
    c = k3*N/(delta+k3) ∧ b=delta*N/(delta+k3) := by
  rw [← ht]
  constructor <;> apply (eq_div_iff hs).2 <;> nlinarith

theorem reactor_capacity (D alpha ci ell : ℝ) (hD : 0 < D) (ha : 0 < alpha) :
    0 < ci-alpha*(1+ell/D) ↔ ell < D*(ci/alpha-1) := by
  have hn : ci-alpha*(1+ell/D) = (D*(ci-alpha)-alpha*ell)/D := by field_simp; ring
  have he : D*(ci/alpha-1) = (D*(ci-alpha))/alpha := by field_simp
  rw [hn, he, div_pos_iff_of_pos_right hD, lt_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith

end ACRZeroDivisors
