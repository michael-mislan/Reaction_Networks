import proofs.ThreeSitePhosphorylation.Crossing

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 200000

def even0Slope (t : ℝ) : ℝ :=
    (21549480866197/13265752500:ℝ)*t^3 +
    (-3070471513831161895424219/840717064687500000:ℝ)*t^2 +
    (3747333761964530151289376279869/75664535821875000000000:ℝ)*t^1 +
    (-676438287388827146536247537/1269894307500000000000:ℝ)

theorem even0_hasDerivAt (t : ℝ) : HasDerivAt even0 (even0Slope t) t := by
  convert ((((((hasDerivAt_pow 4 t).const_mul (21549480866197/53063010000:ℝ)).add ((hasDerivAt_pow 3 t).const_mul (-3070471513831161895424219/2522151194062500000:ℝ))).add ((hasDerivAt_pow 2 t).const_mul (3747333761964530151289376279869/151329071643750000000000:ℝ))).add ((hasDerivAt_pow 1 t).const_mul (-676438287388827146536247537/1269894307500000000000:ℝ))).add (hasDerivAt_const (x := t) (1182316803067886887/3061327500000000:ℝ))) using 1
  norm_num [even0,even0Slope]
  ring

def odd0Slope (t : ℝ) : ℝ :=
    (4/1:ℝ)*t^3 +
    (-1914250662484005497/16424265000000:ℝ)*t^2 +
    (178228249672628679513269034107/7566453582187500000000:ℝ)*t^1 +
    (-1095227502621761760478226249101/226993607465625000000000:ℝ)

theorem odd0_hasDerivAt (t : ℝ) : HasDerivAt odd0 (odd0Slope t) t := by
  convert ((((((hasDerivAt_pow 4 t).const_mul (1/1:ℝ)).add ((hasDerivAt_pow 3 t).const_mul (-1914250662484005497/49272795000000:ℝ))).add ((hasDerivAt_pow 2 t).const_mul (178228249672628679513269034107/15132907164375000000000:ℝ))).add ((hasDerivAt_pow 1 t).const_mul (-1095227502621761760478226249101/226993607465625000000000:ℝ))).add (hasDerivAt_const (x := t) (2365405597729059858828139/17908765875000000000:ℝ))) using 1
  norm_num [odd0,odd0Slope]
  ring

def even1Slope (t : ℝ) : ℝ :=
    (2864/6045:ℝ)*t^3 +
    (-1743145840777470340069/134514730350000000:ℝ)*t^2 +
    (19351917652493567002237891771/7566453582187500000000:ℝ)*t^1 +
    (-15669391757369638993598066707/13968837382500000000000:ℝ)

theorem even1_hasDerivAt (t : ℝ) : HasDerivAt even1 (even1Slope t) t := by
  convert ((((((hasDerivAt_pow 4 t).const_mul (716/6045:ℝ)).add ((hasDerivAt_pow 3 t).const_mul (-1743145840777470340069/403544191050000000:ℝ))).add ((hasDerivAt_pow 2 t).const_mul (19351917652493567002237891771/15132907164375000000000:ℝ))).add ((hasDerivAt_pow 1 t).const_mul (-15669391757369638993598066707/13968837382500000000000:ℝ))).add (hasDerivAt_const (x := t) (1182316803067886887/3061327500000000:ℝ))) using 1
  norm_num [even1,even1Slope]
  ring

def odd1Slope (t : ℝ) : ℝ :=
    (-244167141079021/1724547825000:ℝ)*t^2 +
    (41210428898350734288350941/151329071643750000000:ℝ)*t^1 +
    (-298391200108946577505242797723/113496803732812500000000:ℝ)

theorem odd1_hasDerivAt (t : ℝ) : HasDerivAt odd1 (odd1Slope t) t := by
  convert (((((hasDerivAt_pow 3 t).const_mul (-244167141079021/5173643475000:ℝ)).add ((hasDerivAt_pow 2 t).const_mul (41210428898350734288350941/302658143287500000000:ℝ))).add ((hasDerivAt_pow 1 t).const_mul (-298391200108946577505242797723/113496803732812500000000:ℝ))).add (hasDerivAt_const (x := t) (2369048939115567901134889/17908765875000000000:ℝ))) using 1
  norm_num [odd1,odd1Slope]
  ring

theorem frequencyPolynomial_hasDerivAt (t : ℝ) : HasDerivAt frequencyPolynomial (frequencySlope t) t := by
  convert ((((((((((hasDerivAt_pow 8 t).const_mul (716/6045:ℝ)).add ((hasDerivAt_pow 7 t).const_mul (45363713206799695617936821/4427888636296125000000:ℝ))).add ((hasDerivAt_pow 6 t).const_mul (8362584637034098682974692474934473341/144834808942073250000000000000:ℝ))).add ((hasDerivAt_pow 5 t).const_mul (1021981665335961675887509605635181201202152317573/15153341885564413781250000000000000000:ℝ))).add ((hasDerivAt_pow 4 t).const_mul (11198760752754982346148437812223082888450889500269551/1309332536195081835937500000000000000000:ℝ))).add ((hasDerivAt_pow 3 t).const_mul (12034017163583946742646863911283573660046765892191640401/261866507239016367187500000000000000000000:ℝ))).add ((hasDerivAt_pow 2 t).const_mul (17670011491528419899226529827217130725881483843447001/19427361391749248437500000000000000000000:ℝ))).add ((hasDerivAt_pow 1 t).const_mul (-108348236585674064820049548916655479756645358993/1379457613615331250000000000000000000:ℝ))).add (hasDerivAt_const (x := t) (-4750574844864748849091480686980487/60462748788750000000000000000:ℝ))) using 1
  · funext u; dsimp [frequencyPolynomial]; ring
  · norm_num [frequencySlope]; ring

theorem frequency_orientation (t r : ℝ)
    (he : even0 t+r*even1 t=0) (ho : odd0 t+r*odd1 t=0) :
    frequencySlope t = even1 t*(odd0Slope t+r*odd1Slope t)-
      odd1 t*(even0Slope t+r*even1Slope t) := by
  have hd := eliminant_slope_at_root (even0 t) (odd0 t) (even1 t) (odd1 t)
    (even0Slope t) (odd0Slope t) (even1Slope t) (odd1Slope t) r he ho
  rw [← hd]
  unfold frequencySlope even0 odd0 even1 odd1 even0Slope odd0Slope even1Slope odd1Slope
  ring

theorem frequency_transverse (t r : ℝ) (ht : 0 < t)
    (he : even0 t+r*even1 t=0) (ho : odd0 t+r*odd1 t=0) :
    0 < t*(odd0Slope t+r*odd1Slope t)^2+(even0Slope t+r*even1Slope t)^2 ∧
    -frequencySlope t/(2*(t*(odd0Slope t+r*odd1Slope t)^2+
      (even0Slope t+r*even1Slope t)^2)) < 0 := by
  have hp : frequencyPolynomial t=0 := by
    rw [frequency_elimination_identity]
    linear_combination even1 t*ho-odd1 t*he
  exact crossing_quotient_negative t (even1 t) (odd1 t)
    (even0Slope t+r*even1Slope t) (odd0Slope t+r*odd1Slope t)
    (frequencySlope t) ht (frequency_slope_positive t ht hp) (frequency_orientation t r he ho)

end
end ThreeSitePhosphorylation
