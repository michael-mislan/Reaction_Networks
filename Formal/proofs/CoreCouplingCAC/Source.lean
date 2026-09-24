import Mathlib

/-! Literal driven source: A ↔ B+z, z ↔ H, 2z ↔ H,
0 ↔ A, 0 ↔ B, B ↔ 2A, H → 0.
Rates respectively (1,1), (u,1), (v,1), (a,1), (b,1), (e,e), d.
Every reversible pair contributes its net current exactly once.
-/
namespace CoreCouplingCAC

structure Rates where
  a : ℝ
  b : ℝ
  u : ℝ
  v : ℝ
  e : ℝ
  d : ℝ

def Rates.Positive (p : Rates) : Prop :=
  0 < p.a ∧ 0 < p.b ∧ 0 < p.u ∧ 0 < p.v ∧ 0 < p.e ∧ 0 < p.d

structure State where
  A : ℝ
  B : ℝ
  z : ℝ
  H : ℝ

def State.Positive (x : State) : Prop := 0 < x.A ∧ 0 < x.B ∧ 0 < x.z ∧ 0 < x.H

noncomputable def fA (p : Rates) (A B z : ℝ) : ℝ :=
  p.a - 2*A + z*B + 2*p.e*(B-A^2)
noncomputable def fB (p : Rates) (A B z : ℝ) : ℝ :=
  p.b + A - (1+z)*B - p.e*(B-A^2)
noncomputable def fZ (p : Rates) (A B z H : ℝ) : ℝ :=
  A-B*z-p.u*z-2*p.v*z^2+3*H
noncomputable def fH (p : Rates) (z H : ℝ) : ℝ :=
  p.u*z+p.v*z^2-(2+p.d)*H

def Stationary (p : Rates) (x : State) : Prop :=
  fA p x.A x.B x.z = 0 ∧ fB p x.A x.B x.z = 0 ∧
  fZ p x.A x.B x.z x.H = 0 ∧ fH p x.z x.H = 0

/-- Rows of the gain-two core, used both for (A,B) and (z,H).
The oriented reactions are first species → second, second → 2 first.
-/
def CoreProductive (j k : ℝ) : Prop := 0 < -j+2*k ∧ 0 < j-k

theorem gain_two_core_productive : CoreProductive 3 2 := by
  norm_num [CoreProductive]

/-- Removing either reaction prevents productivity, even with signed net currents. -/
theorem gain_two_core_reaction_minimal (j k : ℝ) (h : j = 0 ∨ k = 0) :
    ¬ CoreProductive j k := by
  rcases h with rfl | rfl <;> intro hp <;> unfold CoreProductive at hp <;> linarith [hp.1, hp.2]

noncomputable def coreZH (p : Rates) (x : State) : ℝ × ℝ :=
  (-(p.u*x.z-x.H)+2*(x.H-p.v*x.z^2),
    (p.u*x.z-x.H)-(x.H-p.v*x.z^2))

theorem stationary_H_margin (p : Rates) (x : State) (h : Stationary p x) :
    (coreZH p x).2 = p.d*x.H := by
  dsimp [coreZH]
  have hh := h.2.2.2
  dsimp [fH] at hh
  linarith

theorem stationary_H_margin_pos (p : Rates) (x : State)
    (hp : p.Positive) (hx : x.Positive) (h : Stationary p x) :
    0 < (coreZH p x).2 := by
  rw [stationary_H_margin p x h]
  exact mul_pos hp.2.2.2.2.2 hx.2.2.2

end CoreCouplingCAC
