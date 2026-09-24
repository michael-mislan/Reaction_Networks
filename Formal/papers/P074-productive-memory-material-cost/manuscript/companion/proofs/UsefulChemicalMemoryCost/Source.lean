import Mathlib

namespace UsefulChemicalMemoryCost

structure State where
  n : ℕ
  c : ℕ
  p : ℕ
  f : ℕ
  deriving DecidableEq

def mass (s : State) : ℕ := s.n + 2*s.c + s.p + s.f
def residents (s : State) : ℕ := s.n+s.c
def admissible (K : ℕ) (s : State) : Prop := mass s=K ∧ 1 ≤ residents s
def restart (K : ℕ) (s : State) : Prop :=
  admissible K s ∧ s.p=0 ∧ residents s ≤ K-1

def rates (κ : ℚ) (s : State) : Fin 6 → ℚ :=
  ![(s.n*s.f : ℕ), (s.n*(s.n-1) : ℕ)/100,
    (2*s.n*s.f : ℕ), κ*s.c, κ*s.c, (s.n*s.p : ℕ)/50]

def enabled (s : State) : Fin 6 → Prop :=
  ![1 ≤ s.n ∧ 1 ≤ s.f, 2 ≤ s.n, 1 ≤ s.n ∧ 1 ≤ s.f,
    1 ≤ s.c, 1 ≤ s.c, 1 ≤ s.n ∧ 1 ≤ s.p]

def jump (s : State) : Fin 6 → State :=
  ![⟨s.n+1,s.c,s.p,s.f-1⟩, ⟨s.n-1,s.c,s.p,s.f+1⟩,
    ⟨s.n-1,s.c+1,s.p,s.f-1⟩, ⟨s.n+1,s.c-1,s.p,s.f+1⟩,
    ⟨s.n+1,s.c-1,s.p+1,s.f⟩, ⟨s.n-1,s.c+1,s.p-1,s.f⟩]

theorem jump_conserves (s : State) (r : Fin 6) (h : enabled s r) :
    mass (jump s r) = mass s := by
  fin_cases r <;> simp_all [enabled, jump, mass] <;> omega

theorem final_resident_survives (s : State) (r : Fin 6)
    (h : enabled s r) (hs : 1 ≤ residents s) : 1 ≤ residents (jump s r) := by
  fin_cases r <;> simp_all [enabled, jump, residents] <;> omega

theorem quota_limits_carriers (K q : ℕ) (s : State)
    (hs : admissible K s) (hq : q ≤ s.p) : residents s+q ≤ K := by
  unfold admissible mass residents at *
  omega

theorem bound_seed_rates (K : ℕ) (κ : ℚ) :
    rates κ ⟨0,1,0,K-2⟩ = ![0,0,0,κ,κ,0] := by
  ext r
  fin_cases r <;> simp [rates]

theorem bound_seed_admitted (K : ℕ) (hK : 2 ≤ K) :
    restart K ⟨0,1,0,K-2⟩ := by
  simp [restart, admissible, mass, residents]
  omega

theorem release_affine (s : State) (lo hi t : ℚ) (r : Fin 6) :
    rates ((1-t)*lo+t*hi) s r =
      (1-t)*rates lo s r+t*rates hi s r := by
  fin_cases r <;> simp [rates] <;> ring

end UsefulChemicalMemoryCost
