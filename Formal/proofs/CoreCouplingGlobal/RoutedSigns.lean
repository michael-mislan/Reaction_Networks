import proofs.CoreCouplingGlobal.RoutedResponse

namespace CoreCouplingGlobal

theorem routed_sign_lowLeft (e g : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : (999/1000:ℝ) ≤ g) (hgu : g ≤ 1) :
    0 < (-1:ℝ)*routedPoly e g (9/10) := by
  let t : ℝ := 1000*g-999
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htu : t ≤ 1 := by dsimp [t]; linarith
  have h0 : 0 < (-1:ℝ)*routedPoly (0) g (9/10) := by
    have hid : (-1:ℝ)*routedPoly (0) g (9/10) = (482410614579021891/666700000000000000)*(1-t)^4+4*(799646468016933/1130000000000000)*t*(1-t)^3+6*(23058211749843/33335000000000)*t^2*(1-t)^2+4*(45052907001/66670000000)*t^3*(1-t)+(2749287/4166875)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (-1:ℝ)*routedPoly (1/50000) g (9/10) := by
    have hid : (-1:ℝ)*routedPoly (1/50000) g (9/10) = (390019238339647329603189/555611112500000000000000)*(1-t)^4+4*(381159660888615577876407/555611112500000000000000)*t*(1-t)^3+6*(186146712819600707356797/277805556250000000000000)*t^2*(1-t)^2+4*(181710265808323684839/277805556250000000000)*t^3*(1-t)+(88635244461594831/138902778125000000)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hm := routed_positive_affine_mix (50000*e) _ _ (by positivity) (by linarith) h0 h1
  rw [routed_poly_affine]
  convert hm using 1
  ring

theorem routed_sign_lowRight (e g : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : (999/1000:ℝ) ≤ g) (hgu : g ≤ 1) :
    0 < (1:ℝ)*routedPoly e g (11/10) := by
  let t : ℝ := 1000*g-999
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htu : t ≤ 1 := by dsimp [t]; linarith
  have h0 : 0 < (1:ℝ)*routedPoly (0) g (11/10) := by
    have hid : (1:ℝ)*routedPoly (0) g (11/10) = (322103892275896509/666700000000000000)*(1-t)^4+4*(33232846269533913/66670000000000000)*t*(1-t)^3+6*(17127944253877/33335000000000)*t^2*(1-t)^2+4*(35279515799/66670000000)*t^3*(1-t)+(2268983/4166875)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (1:ℝ)*routedPoly (1/50000) g (11/10) := by
    have hid : (1:ℝ)*routedPoly (1/50000) g (11/10) = (286357578576796605637251/555611112500000000000000)*(1-t)^4+4*(294892804172028626277063/555611112500000000000000)*t*(1-t)^3+6*(455149371244618466872969/833416668750000000000000)*t^2*(1-t)^2+4*(155988953678061019461/277805556250000000000)*t^3*(1-t)+(80131945639287209/138902778125000000)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hm := routed_positive_affine_mix (50000*e) _ _ (by positivity) (by linarith) h0 h1
  rw [routed_poly_affine]
  convert hm using 1
  ring

theorem routed_sign_midLeft (e g : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : (999/1000:ℝ) ≤ g) (hgu : g ≤ 1) :
    0 < (1:ℝ)*routedPoly e g (19/10) := by
  let t : ℝ := 1000*g-999
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htu : t ≤ 1 := by dsimp [t]; linarith
  have h0 : 0 < (1:ℝ)*routedPoly (0) g (19/10) := by
    have hid : (1:ℝ)*routedPoly (0) g (19/10) = (272163661381092429/666700000000000000)*(1-t)^4+4*(27564357210403833/66670000000000000)*t*(1-t)^3+6*(13955671371477/33335000000000)*t^2*(1-t)^2+4*(28257320439/66670000000)*t^3*(1-t)+(1787643/4166875)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (1:ℝ)*routedPoly (1/50000) g (19/10) := by
    have hid : (1:ℝ)*routedPoly (1/50000) g (19/10) = (276675992904464577314451/555611112500000000000000)*(1-t)^4+4*(279614152716340666413663/555611112500000000000000)*t*(1-t)^3+6*(141271975922597210275923/277805556250000000000000)*t^2*(1-t)^2+4*(142732685575127154501/277805556250000000000)*t^3*(1-t)+(72094597868974329/138902778125000000)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hm := routed_positive_affine_mix (50000*e) _ _ (by positivity) (by linarith) h0 h1
  rw [routed_poly_affine]
  convert hm using 1
  ring

theorem routed_sign_midRight (e g : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : (999/1000:ℝ) ≤ g) (hgu : g ≤ 1) :
    0 < (-1:ℝ)*routedPoly e g (21/10) := by
  let t : ℝ := 1000*g-999
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htu : t ≤ 1 := by dsimp [t]; linarith
  have h0 : 0 < (-1:ℝ)*routedPoly (0) g (21/10) := by
    have hid : (-1:ℝ)*routedPoly (0) g (21/10) = (236875071321484011/666700000000000000)*(1-t)^4+4*(23637209537700567/66670000000000000)*t*(1-t)^3+6*(104373963411/295000000000)*t^2*(1-t)^2+4*(23541428841/66670000000)*t^3*(1-t)+(1468497/4166875)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (-1:ℝ)*routedPoly (1/50000) g (21/10) := by
    have hid : (-1:ℝ)*routedPoly (1/50000) g (21/10) = (137457342521190359575389/555611112500000000000000)*(1-t)^4+4*(136992832129717014615507/555611112500000000000000)*t*(1-t)^3+6*(68270832307779921803397/277805556250000000000000)*t^2*(1-t)^2+4*(68051933028833451879/277805556250000000000)*t^3*(1-t)+(33919865639292951/138902778125000000)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hm := routed_positive_affine_mix (50000*e) _ _ (by positivity) (by linarith) h0 h1
  rw [routed_poly_affine]
  convert hm using 1
  ring

theorem routed_sign_highLeft (e g : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : (999/1000:ℝ) ≤ g) (hgu : g ≤ 1) :
    0 < (-1:ℝ)*routedPoly e g (29/10) := by
  let t : ℝ := 1000*g-999
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htu : t ≤ 1 := by dsimp [t]; linarith
  have h0 : 0 < (-1:ℝ)*routedPoly (0) g (29/10) := by
    have hid : (-1:ℝ)*routedPoly (0) g (29/10) = (421940757217211451/666700000000000000)*(1-t)^4+4*(43706658869853687/66670000000000000)*t*(1-t)^3+6*(22612020420803/33335000000000)*t^2*(1-t)^2+4*(46746229321/66670000000)*t^3*(1-t)+(3017077/4166875)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (-1:ℝ)*routedPoly (1/50000) g (29/10) := by
    have hid : (-1:ℝ)*routedPoly (1/50000) g (29/10) = (240624399865977273564909/555611112500000000000000)*(1-t)^4+4*(253149628781076836982267/555611112500000000000000)*t*(1-t)^3+6*(398572217145538401867071/833416668750000000000000)*t^2*(1-t)^2+4*(139160005925428953159/277805556250000000000)*t^3*(1-t)+(72741323536449511/138902778125000000)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hm := routed_positive_affine_mix (50000*e) _ _ (by positivity) (by linarith) h0 h1
  rw [routed_poly_affine]
  convert hm using 1
  ring

theorem routed_sign_highRight (e g : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : (999/1000:ℝ) ≤ g) (hgu : g ≤ 1) :
    0 < (1:ℝ)*routedPoly e g (31/10) := by
  let t : ℝ := 1000*g-999
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htu : t ≤ 1 := by dsimp [t]; linarith
  have h0 : 0 < (1:ℝ)*routedPoly (0) g (31/10) := by
    have hid : (1:ℝ)*routedPoly (0) g (31/10) = (953220557881117269/666700000000000000)*(1-t)^4+4*(93373716079364553/66670000000000000)*t*(1-t)^3+6*(45709797149637/33335000000000)*t^2*(1-t)^2+4*(89459681319/66670000000)*t^3*(1-t)+(5468373/4166875)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (1:ℝ)*routedPoly (1/50000) g (31/10) := by
    have hid : (1:ℝ)*routedPoly (1/50000) g (31/10) = (921580605932761834534971/555611112500000000000000)*(1-t)^4+4*(905434404383378285365923/555611112500000000000000)*t*(1-t)^3+6*(444620029725464851997883/277805556250000000000000)*t^2*(1-t)^2+4*(436498747528797569781/277805556250000000000)*t^3*(1-t)+(214176658761173889/138902778125000000)*t^4 := by
      dsimp [t,routedPoly,routedNumerA,routedK,routedDen]
      ring
    rw [hid]
    exact positive_quartic_bernstein t _ _ _ _ _ ht htu
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hm := routed_positive_affine_mix (50000*e) _ _ (by positivity) (by linarith) h0 h1
  rw [routed_poly_affine]
  convert hm using 1
  ring

end CoreCouplingGlobal
