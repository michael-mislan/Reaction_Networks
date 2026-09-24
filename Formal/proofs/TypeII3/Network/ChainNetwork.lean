import proofs.TypeII3.Network.ChainCompression
import proofs.TypeII3.Network.FullReduction

namespace TypeII3

structure ArcChainRates where
  rp : UnitChain
  pq : UnitChain
  dR : ℝ
  dP : ℝ
  dQ : ℝ
  dR_pos : 0 < dR
  dP_pos : 0 < dP
  dQ_pos : 0 < dQ

noncomputable def ArcChainRates.effective (a : ArcChainRates) : ArcRates :=
  { c := a.rp.summary.c
    beta := a.rp.summary.beta
    gamma := a.pq.summary.c
    eta := a.pq.summary.beta
    dR := a.dR + a.rp.summary.leakL
    dP := a.dP + a.rp.summary.leakR + a.pq.summary.leakL
    dQ := a.dQ + a.pq.summary.leakR
    c_pos := a.rp.summary.c_pos
    beta_pos := a.rp.summary.beta_pos
    gamma_pos := a.pq.summary.c_pos
    eta_pos := a.pq.summary.beta_pos
    dR_pos := add_pos_of_pos_of_nonneg a.dR_pos a.rp.summary.leakL_nonneg
    dP_pos := add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg a.dP_pos a.rp.summary.leakR_nonneg)
      a.pq.summary.leakL_nonneg
    dQ_pos := add_pos_of_pos_of_nonneg a.dQ_pos a.pq.summary.leakR_nonneg }

def ArcChainSteady (a : ArcChainRates)
    (zRP : a.rp.State) (zPQ : a.pq.State) (m : ℕ)
    (delta deltaNext R P Q : ℝ) : Prop :=
  ∃ jRPL jRPR jPQL jPQR,
    ChainFlux a.rp zRP R P jRPL jRPR ∧
    ChainFlux a.pq zPQ P Q jPQL jPQR ∧
    m * delta - jRPL - a.dR * R = 0 ∧
    jRPR - jPQL - a.dP * P + deltaNext = 0 ∧
    jPQR - a.dQ * Q - deltaNext = 0

theorem arc_chain_compress
    (a : ArcChainRates) (zRP : a.rp.State) (zPQ : a.pq.State)
    {m : ℕ} {delta deltaNext R P Q : ℝ}
    (h : ArcChainSteady a zRP zPQ m delta deltaNext R P Q) :
    ArcSteady a.effective m delta deltaNext R P Q := by
  rcases h with ⟨jRPL, jRPR, jPQL, jPQR, hRP, hPQ, hR, hP, hQ⟩
  rcases chain_flux_compress a.rp zRP hRP with ⟨hRPL, hRPR⟩
  rcases chain_flux_compress a.pq zPQ hPQ with ⟨hPQL, hPQR⟩
  simp only [ArcSteady, ArcChainRates.effective]
  constructor
  · rw [hRPL] at hR
    linear_combination hR
  constructor
  · rw [hRPR] at hP
    rw [hPQL] at hP
    linear_combination hP
  · rw [hPQR] at hQ
    linear_combination hQ

theorem arc_chain_states_unique
    (a : ArcChainRates)
    (zRP wRP : a.rp.State) (zPQ wPQ : a.pq.State)
    {m : ℕ} {delta deltaNext R P Q : ℝ}
    (hz : ArcChainSteady a zRP zPQ m delta deltaNext R P Q)
    (hw : ArcChainSteady a wRP wPQ m delta deltaNext R P Q) :
    zRP = wRP ∧ zPQ = wPQ := by
  rcases hz with ⟨_, _, _, _, hzRP, hzPQ, _⟩
  rcases hw with ⟨_, _, _, _, hwRP, hwPQ, _⟩
  exact ⟨chain_state_unique a.rp zRP wRP hzRP hwRP,
    chain_state_unique a.pq zPQ wPQ hzPQ hwPQ⟩

structure ChainCanonicalParams where
  arc0 : ArcChainRates
  arc1 : ArcChainRates
  arc2 : ArcChainRates
  fork0 : ForkRates
  fork1 : ForkRates
  fork2 : ForkRates

noncomputable def ChainCanonicalParams.effective
    (p : ChainCanonicalParams) : CanonicalParams :=
  { arc0 := p.arc0.effective
    arc1 := p.arc1.effective
    arc2 := p.arc2.effective
    fork0 := p.fork0
    fork1 := p.fork1
    fork2 := p.fork2 }

@[ext] structure ChainCanonicalState (p : ChainCanonicalParams) where
  endpoints : CanonicalState
  rp0 : p.arc0.rp.State
  pq0 : p.arc0.pq.State
  rp1 : p.arc1.rp.State
  pq1 : p.arc1.pq.State
  rp2 : p.arc2.rp.State
  pq2 : p.arc2.pq.State

def PositiveChainCanonicalState {p : ChainCanonicalParams}
    (x : ChainCanonicalState p) : Prop := PositiveCanonicalState x.endpoints

def IsChainCanonicalStationary {p : ChainCanonicalParams}
    (x : ChainCanonicalState p) : Prop :=
  let d0 := forkCurrent p.fork0 x.endpoints.Q0 x.endpoints.P0 x.endpoints.R0
  let d1 := forkCurrent p.fork1 x.endpoints.Q1 x.endpoints.P1 x.endpoints.R1
  let d2 := forkCurrent p.fork2 x.endpoints.Q2 x.endpoints.P2 x.endpoints.R2
  ArcChainSteady p.arc0 x.rp0 x.pq0 p.fork2.m d2 d0
    x.endpoints.R2 x.endpoints.P0 x.endpoints.Q0 ∧
  ArcChainSteady p.arc1 x.rp1 x.pq1 p.fork0.m d0 d1
    x.endpoints.R0 x.endpoints.P1 x.endpoints.Q1 ∧
  ArcChainSteady p.arc2 x.rp2 x.pq2 p.fork1.m d1 d2
    x.endpoints.R1 x.endpoints.P2 x.endpoints.Q2

theorem chain_to_canonical_stationary
    {p : ChainCanonicalParams} (x : ChainCanonicalState p)
    (h : IsChainCanonicalStationary x) :
    IsCanonicalStationary p.effective x.endpoints := by
  simp only [IsChainCanonicalStationary] at h
  rcases h with ⟨h0, h1, h2⟩
  simp only [IsCanonicalStationary, ChainCanonicalParams.effective]
  exact ⟨arc_chain_compress p.arc0 x.rp0 x.pq0 h0,
    arc_chain_compress p.arc1 x.rp1 x.pq1 h1,
    arc_chain_compress p.arc2 x.rp2 x.pq2 h2⟩

/-- `T_chain`: positive stationary states are unique after inserting arbitrary
finite unit-stoichiometric reversible chains between the six fork endpoints. -/
theorem chain_canonical_unistationarity
    (p : ChainCanonicalParams) (x y : ChainCanonicalState p)
    (hx : PositiveChainCanonicalState x)
    (hy : PositiveChainCanonicalState y)
    (hxstat : IsChainCanonicalStationary x)
    (hystat : IsChainCanonicalStationary y) : x = y := by
  have hex : x.endpoints = y.endpoints := canonical_unistationarity p.effective
    x.endpoints y.endpoints hx hy
    (chain_to_canonical_stationary x hxstat)
    (chain_to_canonical_stationary y hystat)
  simp only [IsChainCanonicalStationary] at hxstat hystat
  rcases hxstat with ⟨hxs0, hxs1, hxs2⟩
  rcases hystat with ⟨hys0, hys1, hys2⟩
  have hs0 := arc_chain_states_unique p.arc0 x.rp0 y.rp0 x.pq0 y.pq0
    hxs0 (hex ▸ hys0)
  have hs1 := arc_chain_states_unique p.arc1 x.rp1 y.rp1 x.pq1 y.pq1
    hxs1 (hex ▸ hys1)
  have hs2 := arc_chain_states_unique p.arc2 x.rp2 y.rp2 x.pq2 y.pq2
    hxs2 (hex ▸ hys2)
  apply ChainCanonicalState.ext
  all_goals aesop

end TypeII3
