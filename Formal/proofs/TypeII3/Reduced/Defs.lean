import Mathlib

namespace TypeII3

structure SectorParams where
  A : ℝ
  B : ℝ
  lam : ℝ
  a : ℝ
  b : ℝ
  e : ℝ
  f : ℝ
  m : ℕ
  A_pos : 0 < A
  B_pos : 0 < B
  lam_pos : 0 < lam
  a_pos : 0 < a
  b_pos : 0 < b
  e_pos : 0 < e
  f_pos : 0 < f
  m_pos : 0 < m

structure ReducedParams where
  q0 : SectorParams
  q1 : SectorParams
  q2 : SectorParams

def reducedF (q : SectorParams) (xPrev x xNext : ℝ) : ℝ :=
  q.A * xPrev - q.B * x -
    q.lam * (q.a * xPrev + q.b * x) * (q.e * x + q.f * xNext) ^ q.m

def IsReducedRoot (p : ReducedParams) (x0 x1 x2 : ℝ) : Prop :=
  reducedF p.q0 x2 x0 x1 = 0 ∧
  reducedF p.q1 x0 x1 x2 = 0 ∧
  reducedF p.q2 x1 x2 x0 = 0

def PositiveTriple (x0 x1 x2 : ℝ) : Prop :=
  0 < x0 ∧ 0 < x1 ∧ 0 < x2

end TypeII3
