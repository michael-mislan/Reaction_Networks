import proofs.RobustPermanence.RateSource

namespace RobustPermanence
open Set

structure RateBox (r : AssemblyRates) : Prop where
  a : r.a ∈ Icc (5999999/1000000:ℝ) (6000001/1000000)
  b : r.b ∈ Icc (26999999/1000000:ℝ) (27000001/1000000)
  p : r.p ∈ Icc (999999/1000000:ℝ) (1000001/1000000)
  q : r.q ∈ Icc (999999/1000000:ℝ) (1000001/1000000)
  alpha : r.alpha ∈ Icc (999999/1000000:ℝ) (1000001/1000000)
  beta : r.beta ∈ Icc (999999/1000000:ℝ) (1000001/1000000)
  ef : r.ef ∈ Icc (1/1000000:ℝ) (21/1000000)
  er : r.er ∈ Icc (1/1000000:ℝ) (21/1000000)
  u : r.u ∈ Icc (15999999/1000000:ℝ) (16000001/1000000)
  v : r.v ∈ Icc (1999999/1000000:ℝ) (2000001/1000000)
  h1 : r.h1 ∈ Icc (999999/1000000:ℝ) (1000001/1000000)
  h2 : r.h2 ∈ Icc (999999/1000000:ℝ) (1000001/1000000)
  d : r.d ∈ Icc (99/1000000:ℝ) (101/1000000)
  k : r.k ∈ Icc (999999/1000000:ℝ) (1000001/1000000)
  mu : r.mu ∈ Icc (499999/1000000:ℝ) (500001/1000000)
  rho : r.rho ∈ Icc (999999/1000000:ℝ) (1000001/1000000)

theorem RateNeighborhood.box (e : ℝ) (r : AssemblyRates)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000) (hr : RateNeighborhood e r) : RateBox r := by
  constructor
  · have h := abs_le.1 hr.a
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.b
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.p
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.q
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.alpha
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.beta
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.ef
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.er
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.u
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.v
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.h1
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.h2
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.d
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.k
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.mu
    dsimp [rateRadius] at h
    constructor <;> linarith
  · have h := abs_le.1 hr.rho
    dsimp [rateRadius] at h
    constructor <;> linarith

end RobustPermanence
