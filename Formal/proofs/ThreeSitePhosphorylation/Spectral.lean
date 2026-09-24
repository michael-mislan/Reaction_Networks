import proofs.ThreeSitePhosphorylation.Jacobian
import proofs.ThreeSitePhosphorylation.Polynomial

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 3000000
open scoped Matrix

def sourceMatrix (r : ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  !![(0) , (0) , (0) , (5/26) , (0) , (0) , (-1/93) , (0) , (0);
    (0) , (0) , (0) , (0) , (1950/7) , (0) , (0) , (-52) , (0);
    (0) , (0) , (0) , (0) , (0) , (50/39) , (0) , (0) , (-2/5);
    (-101/30000) , (0) , (0) , (-326331/1430000) , (-101/3300) , (-101/3300) , (0) , (0) , (0);
    (303/500) , (-303/500) , (0) , (-1313/550) , (-10947491/38500) , (-1313/550) , (-303/500) , (0) , (0);
    (0) , (101/19) , (-101/19) , (-101/330) , (-101/330) , (-281891/40755) , (0) , (-101/19) , (0);
    (1/130)+r*(1/130) , (-1/130)+r*(-1/130) , (0) , (0) , (-1/130)+r*(-1/130) , (0) , (-716/6045)+r*(-716/6045) , (-1/10)+r*(-1/10) , (-1/10)+r*(-1/10);
    (0) , (3939/95) , (-3939/95) , (0) , (0) , (-3939/95) , (-3939/500) , (-967681/9500) , (-3939/500);
    (0) , (0) , (101/9) , (0) , (0) , (0) , (-101/100) , (-101/100) , (-56863/4500)]

theorem sourceMatrix_action (r : ℝ) (y : ReducedState) :
    (sourceMatrix r).mulVec y = jacobianOperator r y := by
  ext i
  fin_cases i <;>
    simp [sourceMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      jacobianOperator,jacobianRows,complexLinear,witnessState,
      speciesVariation,coordinate,inputSpecies,enzymeSpecies,boundCoordinate,bindingRates,exitRates] <;> ring

def adjugateVector (z : ℂ) : Fin 9 → ℂ :=
  ![(-1/93)*z^7 + (-694941800587/159189030000)*z^6 + (-68166530701704733/163378215000000)*z^5 + (-5615305096991169299/430499179687500)*z^4 + (-145788025447404844607270023/1164069781875000000000)*z^3 + (-1493349457946276585559938263/5820348909375000000000)*z^2 + (-5327751085886284293137/86099835937500000)*z^1 + (-491673862855421581/59636250000000)*z^0,
    (421473/1750)*z^6 + (35252476329778417/340147500000)*z^5 + (1246805146607466485821/663287625000000)*z^4 + (16391271987942196848985679/1658219062500000000)*z^3 + (27533153333711325095174141/1938178125000000000)*z^2 + (244857208729496774971031011/89543829375000000000)*z^1 + (221106167074886957629/45919912500000000)*z^0,
    (101/250)*z^6 + (9968836083663/47547500000)*z^5 + (23522652716259996360527/776046521250000000)*z^4 + (433223244806895082989139043/349220934562500000000)*z^3 + (32300677220787557782955709301/3492209345625000000000)*z^2 + (2693952116654251518104947/1326575250000000000)*z^1 + (28111500034518198271/7653318750000000)*z^0,
    (1425817/76725000)*z^6 + (1169320763134259/1193917725000000)*z^5 + (-297748678912537076387/895438293750000000)*z^4 + (-629770100628644087311093/29847943125000000000)*z^3 + (-44545939516921818924836687/223859573437500000000)*z^2 + (-26108460168397690256227/344399343750000000)*z^1 + (-52234285111226413/4591991250000000)*z^0,
    (-303/500)*z^7 + (-8467311970081/114855000000)*z^6 + (-49006433455581803/17497441406250)*z^5 + (-1912438808663682197386819/55431894375000000000)*z^4 + (-212962536970631570584214029/1662956831250000000000)*z^3 + (-112843925743981430504874241/1662956831250000000000)*z^2 + (-10406235526758079085933/1162906875000000000)*z^1 + (-117852815356958791/3279993750000000)*z^0,
    (43956109/1045000)*z^6 + (10907469190243194511/795945150000000)*z^5 + (100261152249867877181609/137759737500000000)*z^4 + (225545314389062333204467213/33164381250000000000)*z^3 + (34761017329533033297973181/8568787500000000000)*z^2 + (9269571884808082775111/15944414062500000)*z^1 + (238330223521127803/231918750000000)*z^0,
    (1)*z^8 + (694941800587/1711710000)*z^7 + (68167114573766233/1756755000000)*z^6 + (4338286922830631273731/3576251250000000)*z^5 + (20816226896810958619739039/1788125625000000000)*z^4 + (2939466158345404864571544551/125168793750000000000)*z^3 + (27485255164260744718375553/12516879375000000000)*z^2 + (-597026003518388430463/1013512500000000)*z^1 + (-4018021931632801/19750500000000)*z^0,
    (-3939/500)*z^7 + (-52404477301607/21945000000)*z^6 + (-4377948099003499567/85585500000000)*z^5 + (-84776910996869445351073/226120781250000000)*z^4 + (-286312162729290819112836907/298479431250000000000)*z^3 + (-10645692829061638640352443/25583951250000000000)*z^2 + (-28672424240353439225723/596958862500000000)*z^1 + (-117852815356958791/612265500000000)*z^0,
    (-101/100)*z^7 + (-22214189175989/57057000000)*z^6 + (-35441993650379939863/1112611500000000)*z^5 + (-128284946230375725386989/166891725000000000)*z^4 + (-926029889132071400176317773/698441869125000000000)*z^3 + (2214160521517738555355942819/279376747650000000000)*z^2 + (4919408371867728374891/2653150500000000)*z^1 + (18333094117009831/5566050000000)*z^0]

theorem adjugate_residual (r : ℝ) (z : ℂ) :
    ∀ i : Fin 9, ((sourceMatrix r).map (algebraMap ℝ ℂ)).mulVec (adjugateVector z) i =
      z*adjugateVector z i - (if i=6 then candidatePolynomial r z else 0) := by
  intro i
  fin_cases i <;>
    simp [sourceMatrix,adjugateVector,candidatePolynomial,Matrix.mulVec,
      dotProduct,Fin.sum_univ_succ] <;> ring

def adjugateReal0 (t : ℝ) : ℝ := (694941800587/159189030000)*t^3 + (-5615305096991169299/430499179687500)*t^2 + (1493349457946276585559938263/5820348909375000000000)*t^1 + (-491673862855421581/59636250000000)*t^0

theorem adjugate_real0 (w : ℝ) :
    (adjugateVector (Complex.I*(w:ℂ)) 0).re = adjugateReal0 (w^2) := by
  simp [adjugateVector,adjugateReal0,pow_succ,Complex.mul_re,Complex.mul_im]
  ring

theorem adjugate_real0_positive (t : ℝ)
    (ht : frequencyLower ≤ t ∧ t ≤ frequencyUpper) : 0 < adjugateReal0 t := by
  have hl : (0:ℝ) ≤ frequencyLower := by norm_num [frequencyLower]
  have ht0 : 0 ≤ t := hl.trans ht.1
  have h2 : frequencyLower^2 ≤ t^2 ∧ t^2 ≤ frequencyUpper^2 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  have h3 : frequencyLower^3 ≤ t^3 ∧ t^3 ≤ frequencyUpper^3 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  norm_num [frequencyLower,frequencyUpper] at ht h2 h3
  unfold adjugateReal0
  linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2]

theorem source_imaginary_eigenpair : ∃ r w : ℝ, ∃ v : Fin 9 → ℂ,
    0 < r ∧ 0 < w ∧ v ≠ 0 ∧
    ((sourceMatrix r).map (algebraMap ℝ ℂ)).mulVec v = (Complex.I*(w:ℂ)) • v := by
  obtain ⟨t,r,ht,hr,hl,hu,he,ho⟩ := admissible_frequency_exists
  let w := Real.sqrt t
  have hw : 0 < w := Real.sqrt_pos.2 ht
  have hw2 : w^2=t := Real.sq_sqrt ht.le
  have hp : candidatePolynomial r (Complex.I*(w:ℂ)) = 0 := by
    rw [candidate_at_imaginary,hw2,he,ho]
    simp
  refine ⟨r,w,adjugateVector (Complex.I*(w:ℂ)),hr,hw,?_,?_⟩
  · intro hz
    have hzero := congrArg (fun v : Fin 9 → ℂ => (v 0).re) hz
    change (adjugateVector (Complex.I*(w:ℂ)) 0).re = 0 at hzero
    have hpos := adjugate_real0_positive t ⟨hl,hu⟩
    rw [adjugate_real0,hw2] at hzero
    linarith
  · ext i
    rw [adjugate_residual,hp]
    simp

end
end ThreeSitePhosphorylation
