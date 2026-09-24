import proofs.CompositionalMemory.ChebyshevEnclosure

namespace CompositionalMemory
open Polynomial

abbrev QCoefficients := List ℚ

def qadd : QCoefficients → QCoefficients → QCoefficients
  | [],ys => ys
  | xs,[] => xs
  | x::xs,y::ys => (x+y)::qadd xs ys

def qscale (c : ℚ) (xs : QCoefficients) : QCoefficients := xs.map (fun x => c*x)

def qmul : QCoefficients → QCoefficients → QCoefficients
  | [],_ => []
  | a::xs,ys => qadd (qscale a ys) (0::qmul xs ys)

def qderivativeAux (n : ℕ) : QCoefficients → QCoefficients
  | [] => []
  | a::xs => ((n : ℚ)*a)::qderivativeAux (n+1) xs

def qderivative : QCoefficients → QCoefficients
  | [] => []
  | _::xs => qderivativeAux 1 xs

def qsum : List QCoefficients → QCoefficients
  | [] => []
  | xs::xss => qadd xs (qsum xss)

def qsumFin {N : ℕ} (f : Fin N → QCoefficients) : QCoefficients := qsum (List.ofFn f)

def qeval (x : ℚ) : QCoefficients → ℚ
  | [] => 0
  | a::xs => a+x*qeval x xs

noncomputable def qpolynomial : QCoefficients → Polynomial ℚ
  | [] => 0
  | a::xs => C a+X*qpolynomial xs

theorem qeval_real_semantics (x : ℚ) (xs : QCoefficients) :
    Polynomial.aeval (x : ℝ) (qpolynomial xs)=(qeval x xs : ℝ) := by
  induction xs with
  | nil => simp [qpolynomial,qeval]
  | cons a xs ih => simp [qpolynomial,qeval,ih]

@[simp] theorem qpolynomial_qadd (xs ys : QCoefficients) :
    qpolynomial (qadd xs ys)=qpolynomial xs+qpolynomial ys := by
  induction xs generalizing ys with
  | nil => simp [qadd,qpolynomial]
  | cons a xs ih =>
    cases ys with
    | nil => simp [qadd,qpolynomial]
    | cons b ys => simp only [qadd,qpolynomial,ih,map_add]; ring

@[simp] theorem qpolynomial_qscale (c : ℚ) (xs : QCoefficients) :
    qpolynomial (qscale c xs)=C c*qpolynomial xs := by
  induction xs with
  | nil => simp [qscale,qpolynomial]
  | cons a xs ih => simp only [qscale,List.map_cons,qpolynomial,map_mul] at ih ⊢; rw [ih]; ring

@[simp] theorem qpolynomial_qmul (xs ys : QCoefficients) :
    qpolynomial (qmul xs ys)=qpolynomial xs*qpolynomial ys := by
  induction xs with
  | nil => simp [qmul,qpolynomial]
  | cons a xs ih => simp only [qmul,qpolynomial_qadd,qpolynomial_qscale,qpolynomial,map_zero,ih]; ring

theorem qpolynomial_qderivativeAux (n : ℕ) (xs : QCoefficients) :
    qpolynomial (qderivativeAux n xs)=C (n : ℚ)*qpolynomial xs+X*(qpolynomial xs).derivative := by
  induction xs generalizing n with
  | nil => simp [qderivativeAux,qpolynomial]
  | cons a xs ih =>
    simp only [qderivativeAux,qpolynomial,ih,derivative_C,derivative_mul,derivative_X,
      Nat.cast_add,Nat.cast_one,map_add,map_one,map_mul]
    ring

@[simp] theorem qpolynomial_qderivative (xs : QCoefficients) :
    qpolynomial (qderivative xs)=(qpolynomial xs).derivative := by
  cases xs with
  | nil => simp [qderivative,qpolynomial]
  | cons a xs => simp [qderivative,qpolynomial,qpolynomial_qderivativeAux]

@[simp] theorem qpolynomial_qsum (xss : List QCoefficients) :
    qpolynomial (qsum xss)=(xss.map qpolynomial).sum := by
  induction xss with
  | nil => simp [qsum,qpolynomial]
  | cons xs xss ih => simp [qsum,ih]

@[simp] theorem qpolynomial_qsumFin {N : ℕ} (f : Fin N → QCoefficients) :
    qpolynomial (qsumFin f)=∑ i,qpolynomial (f i) := by
  simp [qsumFin,List.map_ofFn,List.sum_ofFn]

def qchebyshevPair : ℕ → QCoefficients × QCoefficients
  | 0 => ([1],[0,1])
  | n+1 => let p := qchebyshevPair n; (p.2,qadd (qmul [0,2] p.2) (qscale (-1) p.1))

def qchebyshev (n : ℕ) : QCoefficients := (qchebyshevPair n).1

theorem qchebyshevPair_semantics (n : ℕ) :
    (qpolynomial (qchebyshevPair n).1,qpolynomial (qchebyshevPair n).2)=rationalChebyshevPair n := by
  induction n with
  | zero => simp [qchebyshevPair,qpolynomial,rationalChebyshevPair]
  | succ n ih =>
    have h1 := congrArg Prod.fst ih
    have h2 := congrArg Prod.snd ih
    change qpolynomial (qchebyshevPair n).1=(rationalChebyshevPair n).1 at h1
    change qpolynomial (qchebyshevPair n).2=(rationalChebyshevPair n).2 at h2
    simp only [qchebyshevPair,rationalChebyshevPair,qpolynomial_qadd,qpolynomial_qmul,qpolynomial_qscale,
      qpolynomial,map_zero,map_one,map_ofNat,map_neg,h1,h2]
    congr 1
    ring

@[simp] theorem qpolynomial_qchebyshev (n : ℕ) :
    qpolynomial (qchebyshev n)=rationalChebyshev n := by
  exact congrArg Prod.fst (qchebyshevPair_semantics n)

def qchebyshevSeries {N : ℕ} (c : Fin N → ℚ) : QCoefficients :=
  qsumFin (fun i => qscale (c i) (qchebyshev i.val))

@[simp] theorem qchebyshevSeries_semantics {N : ℕ} (c : Fin N → ℚ) :
    qpolynomial (qchebyshevSeries c)=rationalChebyshevPolynomial c := by
  simp [qchebyshevSeries,rationalChebyshevPolynomial]

def qzeroCheck (xs : QCoefficients) : Bool := xs.all (fun x => x==0)

theorem qzeroCheck_sound (xs : QCoefficients) (h : qzeroCheck xs=true) : qpolynomial xs=0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [qzeroCheck,List.all_cons,Bool.and_eq_true,beq_iff_eq] at h
    simp [qpolynomial,h.1,ih h.2]

end CompositionalMemory
