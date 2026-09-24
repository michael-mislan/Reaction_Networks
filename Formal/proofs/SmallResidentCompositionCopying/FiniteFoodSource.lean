import proofs.CompositionalMemory.FiniteDeadlineCertificate
import proofs.CompositionalMemory.FiniteGeneratorTransport

namespace SmallResidentCompositionCopying.FiniteFood
open FiniteCopy CompositionalMemory
noncomputable section

structure Rates where
  a : ℝ
  b : ℝ
  c : ℝ
  ha : 0 ≤ a
  hb : 0 ≤ b
  hc : 0 ≤ c

def nominal : Rates := ⟨1000,1,1/10,by norm_num,by norm_num,by norm_num⟩
abbrev Counts (K : ℕ) := Fin K × Fin K
def up {K : ℕ} (x : Fin K) : Fin K := ⟨min (x.val+1) (K-1),by have := x.isLt; omega⟩
def down {K : ℕ} (x : Fin K) : Fin K := ⟨x.val-1,by have := x.isLt; omega⟩
def birth (p : Rates) {K : ℕ} (x y : Fin K) : ℝ :=
  p.a*(x.val+1)*(K-1-x.val:ℕ)*(1+p.c*(y.val+1))
def death (p : Rates) {K : ℕ} (x y : Fin K) : ℝ :=
  p.b*(x.val+1)*x.val*(1+p.c*(y.val+1))
def model (p : Rates) (K : ℕ) : FiniteJumpModel (Counts K) (Fin 4) where
  next z r := if r=0 then (up z.1,z.2) else if r=1 then (down z.1,z.2)
    else if r=2 then (z.1,up z.2) else (z.1,down z.2)
  rate z r := if r=0 then birth p z.1 z.2 else if r=1 then death p z.1 z.2
    else if r=2 then birth p z.2 z.1 else death p z.2 z.1
  nonneg z r := by
    have := p.ha; have := p.hb; have := p.hc
    split_ifs <;> dsimp [birth,death] <;> positivity

abbrev Word := Fin 2 → Bool
def count {K : ℕ} (z : Counts K) (i : Fin 2) : Fin K := if i=0 then z.1 else z.2
def resident {K : ℕ} (word : Word) (z : Counts K) (i : Fin 2) (s : Bool) : ℕ :=
  if word i=s then (count z i).val+1 else 0
def food {K : ℕ} (z : Counts K) (i : Fin 2) : ℕ := K-1-(count z i).val
def target (r : Fin 4) : Fin 2 := if r.val<2 then 0 else 1
def neighbor (r : Fin 4) : Fin 2 := if r.val<2 then 1 else 0
def literalBase (p : Rates) (v : Fin 2 → Bool → ℕ) (f : Fin 2 → ℕ)
    (r : Fin 4) (s : Bool) : ℝ :=
  if r=0 ∨ r=2 then p.a*(v (target r) s)*f (target r)
  else p.b*(v (target r) s)*(v (target r) s-1:ℕ)
def literalRate (p : Rates) (v : Fin 2 → Bool → ℕ) (f : Fin 2 → ℕ)
    (r : Fin 4) (s : Bool) (c : Option Bool) : ℝ :=
  literalBase p v f r s * (match c with | none => 1 | some t => p.c*v (neighbor r) t)
def chemistry (p : Rates) (K : ℕ) (word : Word) :
    FiniteJumpModel (Counts K) (Fin 4 × Bool × Option Bool) where
  next z r := (model p K).next z r.1
  rate z r := literalRate p (resident word z) (food z) r.1 r.2.1 r.2.2
  nonneg z r := by
    have := p.ha; have := p.hb; have := p.hc
    dsimp [literalRate,literalBase]
    split_ifs <;> cases r.2.2 <;> simp only <;> positivity

theorem conserved {K : ℕ} (z : Counts K) (i : Fin 2) :
    (count z i).val+1+food z i=K := by
  have := (count z i).isLt
  dsimp [food]; omega

theorem channel_sum (p : Rates) {K : ℕ} (word : Word) (z : Counts K) (r : Fin 4) :
    (∑ s : Bool, ∑ c : Option Bool, literalRate p (resident word z) (food z) r s c)=
      (model p K).rate z r := by
  fin_cases r <;> cases h0 : word 0 <;> cases h1 : word 1 <;>
    simp [literalRate,literalBase,resident,food,count,target,neighbor,model,birth,death,
      Fintype.sum_option,h0,h1,Nat.cast_add] <;> ring

theorem generator_identification (p : Rates) {K : ℕ} (word : Word)
    (f : Counts K → ℝ) (z : Counts K) :
    (chemistry p K word).generator f z=(model p K).generator f z := by
  simp only [FiniteJumpModel.generator,chemistry,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [← Finset.sum_mul]
  rw [channel_sum]

theorem word_law (p : Rates) {K : ℕ} (word : Word) (t : NNReal)
    (f : Counts K → ℝ) (z : Counts K) :
    finiteTimeExpectation (chemistry p K word) t f z=
      finiteTimeExpectation (model p K) t f z := by
  exact finite_time_generator_congr (chemistry p K word) (model p K)
    (generator_identification p word) t f z

end
end SmallResidentCompositionCopying.FiniteFood
