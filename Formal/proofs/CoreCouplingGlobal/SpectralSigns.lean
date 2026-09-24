import proofs.CoreCouplingGlobal.SpectralPolynomial

namespace CoreCouplingGlobal
open Set

theorem spectral_sign_neg80 (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (9/10:ℝ) (31/10)) :
    0 < (1:ℝ)*scaledCharacteristic e p z (-80) := by
  let t : ℝ := (z-(9/10))/((31/10)-(9/10))
  have ht : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hz.1) (by norm_num)
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by norm_num)).2
    linarith [hz.2]
  have h0 : 0 < (1:ℝ)*scaledCharacteristic (0) (0) z (-80) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (0) z (-80) = (60012868240869/1250000)*(1-t)^3+3*(219614871551233/3750000)*t*(1-t)^2+3*(234546729205727/3750000)*t^2*(1-t)+(75613472694171/1250000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (1:ℝ)*scaledCharacteristic (0) (17/25000) z (-80) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (17/25000) z (-80) = (750134243429272213/15625000000)*(1-t)^3+3*(915029365839452947/15625000000)*t*(1-t)^2+3*(2931728886300959279/46875000000)*t^2*(1-t)+(945134223289433667/15625000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (0) z (-80) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (0) z (-80) = (30006426064305047/625000000)*(1-t)^3+3*(109807406047395533/1875000000)*t*(1-t)^2+3*(117273332393046053/1875000000)*t^2*(1-t)+(37806725809359567/625000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (-80) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (-80) = (46883377626627243/976562500)*(1-t)^3+3*(457514559052139111/7812500000)*t*(1-t)^2+3*(30538834177661699/488281250)*t^2*(1-t)+(472566979923142671/7812500000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he0 : 0 ≤ 50000*e := by positivity
  have he1 : 50000*e ≤ 1 := by linarith
  have hp0 : 0 ≤ (25000/17:ℝ)*p := by positivity
  have hp1 : (25000/17:ℝ)*p ≤ 1 := by linarith
  have hm := positive_affine_mix (50000*e) _ _ he0 he1
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h0 h1)
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h2 h3)
  rw [scaledCharacteristic_box_mix]
  convert hm using 1
  ring

theorem spectral_sign_neg10 (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (9/10:ℝ) (31/10)) :
    0 < (-1:ℝ)*scaledCharacteristic e p z (-10) := by
  let t : ℝ := (z-(9/10))/((31/10)-(9/10))
  have ht : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hz.1) (by norm_num)
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by norm_num)).2
    linarith [hz.2]
  have h0 : 0 < (-1:ℝ)*scaledCharacteristic (0) (0) z (-10) := by
    have hid : (-1:ℝ)*scaledCharacteristic (0) (0) z (-10) = (173360583477/2500000)*(1-t)^3+3*(210573000213/2500000)*t*(1-t)^2+3*(253404582897/2500000)*t^2*(1-t)+(283647443193/2500000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (-1:ℝ)*scaledCharacteristic (0) (17/25000) z (-10) := by
    have hid : (-1:ℝ)*scaledCharacteristic (0) (17/25000) z (-10) = (2166293615504499/31250000000)*(1-t)^3+3*(2631258606385131/31250000000)*t*(1-t)^2+3*(9499201342552517/93750000000)*t^2*(1-t)+(3544154927379591/31250000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 0 < (-1:ℝ)*scaledCharacteristic (1/50000) (0) z (-10) := by
    have hid : (-1:ℝ)*scaledCharacteristic (1/50000) (0) z (-10) = (86680064550807/1250000000)*(1-t)^3+3*(315858607118423/3750000000)*t*(1-t)^2+3*(380105677547393/3750000000)*t^2*(1-t)+(141823190811777/1250000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : 0 < (-1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (-10) := by
    have hid : (-1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (-10) = (1083143967906087/15625000000)*(1-t)^3+3*(1973438372282117/23437500000)*t*(1-t)^2+3*(4749585711299921/46875000000)*t^2*(1-t)+(886035414440379/7812500000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he0 : 0 ≤ 50000*e := by positivity
  have he1 : 50000*e ≤ 1 := by linarith
  have hp0 : 0 ≤ (25000/17:ℝ)*p := by positivity
  have hp1 : (25000/17:ℝ)*p ≤ 1 := by linarith
  have hm := positive_affine_mix (50000*e) _ _ he0 he1
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h0 h1)
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h2 h3)
  rw [scaledCharacteristic_box_mix]
  convert hm using 1
  ring

theorem spectral_sign_neg2 (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (9/10:ℝ) (31/10)) :
    0 < (1:ℝ)*scaledCharacteristic e p z (-2) := by
  let t : ℝ := (z-(9/10))/((31/10)-(9/10))
  have ht : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hz.1) (by norm_num)
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by norm_num)).2
    linarith [hz.2]
  have h0 : 0 < (1:ℝ)*scaledCharacteristic (0) (0) z (-2) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (0) z (-2) = (383671167/2500000)*(1-t)^3+3*(2552137709/7500000)*t*(1-t)^2+3*(5216439481/7500000)*t^2*(1-t)+(3367391643/2500000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (1:ℝ)*scaledCharacteristic (0) (17/25000) z (-2) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (17/25000) z (-2) = (4803860600081/31250000000)*(1-t)^3+3*(10639772552809/31250000000)*t*(1-t)^2+3*(65200235518903/93750000000)*t^2*(1-t)+(42072082142589/31250000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (0) z (-2) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (0) z (-2) = (959220545213/6250000000)*(1-t)^3+3*(6380523633197/18750000000)*t*(1-t)^2+3*(13041344059787/18750000000)*t^2*(1-t)+(8418587731803/6250000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (-2) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (-2) = (2402036869323/15625000000)*(1-t)^3+3*(1330008935913/3906250000)*t*(1-t)^2+3*(10866910384223/15625000000)*t^2*(1-t)+(5259078158013/3906250000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he0 : 0 ≤ 50000*e := by positivity
  have he1 : 50000*e ≤ 1 := by linarith
  have hp0 : 0 ≤ (25000/17:ℝ)*p := by positivity
  have hp1 : (25000/17:ℝ)*p ≤ 1 := by linarith
  have hm := positive_affine_mix (50000*e) _ _ he0 he1
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h0 h1)
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h2 h3)
  rw [scaledCharacteristic_box_mix]
  convert hm using 1
  ring

theorem spectral_sign_negHalf (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (9/10:ℝ) (31/10)) :
    0 < (-1:ℝ)*scaledCharacteristic e p z (-1/2) := by
  let t : ℝ := (z-(9/10))/((31/10)-(9/10))
  have ht : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hz.1) (by norm_num)
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by norm_num)).2
    linarith [hz.2]
  have h0 : 0 < (-1:ℝ)*scaledCharacteristic (0) (0) z (-1/2) := by
    have hid : (-1:ℝ)*scaledCharacteristic (0) (0) z (-1/2) = (159051501/2500000)*(1-t)^3+3*(3351349423/30000000)*t*(1-t)^2+3*(1348218323/7500000)*t^2*(1-t)+(2677687281/10000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (-1:ℝ)*scaledCharacteristic (0) (17/25000) z (-1/2) := by
    have hid : (-1:ℝ)*scaledCharacteristic (0) (17/25000) z (-1/2) = (7960455228691/125000000000)*(1-t)^3+3*(13986644599959/125000000000)*t*(1-t)^2+3*(67543766911373/375000000000)*t^2*(1-t)+(33543754492059/125000000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 0 < (-1:ℝ)*scaledCharacteristic (1/50000) (0) z (-1/2) := by
    have hid : (-1:ℝ)*scaledCharacteristic (1/50000) (0) z (-1/2) = (6361898265583/100000000000)*(1-t)^3+3*(33512954466847/300000000000)*t*(1-t)^2+3*(53928138720817/300000000000)*t^2*(1-t)+(26776656599553/100000000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : 0 < (-1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (-1/2) := by
    have hid : (-1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (-1/2) = (31841012042679/500000000000)*(1-t)^3+3*(55945678794581/500000000000)*t*(1-t)^2+3*(90057365549859/500000000000)*t^2*(1-t)+(134173936916001/500000000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he0 : 0 ≤ 50000*e := by positivity
  have he1 : 50000*e ≤ 1 := by linarith
  have hp0 : 0 ≤ (25000/17:ℝ)*p := by positivity
  have hp1 : (25000/17:ℝ)*p ≤ 1 := by linarith
  have hm := positive_affine_mix (50000*e) _ _ he0 he1
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h0 h1)
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h2 h3)
  rw [scaledCharacteristic_box_mix]
  convert hm using 1
  ring

theorem spectral_sign_posTenth (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (9/10:ℝ) (31/10)) :
    0 < (1:ℝ)*scaledCharacteristic e p z (1/10) := by
  let t : ℝ := (z-(9/10))/((31/10)-(9/10))
  have ht : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hz.1) (by norm_num)
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by norm_num)).2
    linarith [hz.2]
  have h0 : 0 < (1:ℝ)*scaledCharacteristic (0) (0) z (1/10) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (0) z (1/10) = (580336581/10000000)*(1-t)^3+3*(3357160631/75000000)*t*(1-t)^2+3*(9636860519/150000000)*t^2*(1-t)+(4317881337/25000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (1:ℝ)*scaledCharacteristic (0) (17/25000) z (1/10) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (17/25000) z (1/10) = (7286252746439/125000000000)*(1-t)^3+3*(1125062539543/25000000000)*t*(1-t)^2+3*(24191866192537/375000000000)*t^2*(1-t)+(21639722341959/125000000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (0) z (1/10) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (0) z (1/10) = (29018186499757/500000000000)*(1-t)^3+3*(67147293889501/1500000000000)*t*(1-t)^2+3*(96372718615603/1500000000000)*t^2*(1-t)+(86359016345859/500000000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (1/10) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (1/10) = (29146368435513/500000000000)*(1-t)^3+3*(22502611214027/500000000000)*t*(1-t)^2+3*(32257192731917/500000000000)*t^2*(1-t)+(17312055794739/100000000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he0 : 0 ≤ 50000*e := by positivity
  have he1 : 50000*e ≤ 1 := by linarith
  have hp0 : 0 ≤ (25000/17:ℝ)*p := by positivity
  have hp1 : (25000/17:ℝ)*p ≤ 1 := by linarith
  have hm := positive_affine_mix (50000*e) _ _ he0 he1
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h0 h1)
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h2 h3)
  rw [scaledCharacteristic_box_mix]
  convert hm using 1
  ring

theorem spectral_sign_lowZero (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (9/10:ℝ) (11/10)) :
    0 < (1:ℝ)*scaledCharacteristic e p z (0) := by
  let t : ℝ := (z-(9/10))/((11/10)-(9/10))
  have ht : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hz.1) (by norm_num)
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by norm_num)).2
    linarith [hz.2]
  have h0 : 0 < (1:ℝ)*scaledCharacteristic (0) (0) z (0) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (0) z (0) = (19676889/1250000)*(1-t)^3+3*(16488571/1250000)*t*(1-t)^2+3*(13480369/1250000)*t^2*(1-t)+(10692291/1250000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (1:ℝ)*scaledCharacteristic (0) (17/25000) z (0) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (17/25000) z (0) = (248845747113/15625000000)*(1-t)^3+3*(208937570707/15625000000)*t*(1-t)^2+3*(171283906273/15625000000)*t^2*(1-t)+(136385533947/15625000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (0) z (0) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (0) z (0) = (393597783/25000000)*(1-t)^3+3*(329831423/25000000)*t*(1-t)^2+3*(269667383/25000000)*t^2*(1-t)+(213905823/25000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (0) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (0) = (62220812247/3906250000)*(1-t)^3+3*(104487536291/7812500000)*t*(1-t)^2+3*(42830352037/3906250000)*t^2*(1-t)+(68211517911/7812500000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he0 : 0 ≤ 50000*e := by positivity
  have he1 : 50000*e ≤ 1 := by linarith
  have hp0 : 0 ≤ (25000/17:ℝ)*p := by positivity
  have hp1 : (25000/17:ℝ)*p ≤ 1 := by linarith
  have hm := positive_affine_mix (50000*e) _ _ he0 he1
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h0 h1)
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h2 h3)
  rw [scaledCharacteristic_box_mix]
  convert hm using 1
  ring

theorem spectral_sign_middleZero (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    0 < (-1:ℝ)*scaledCharacteristic e p z (0) := by
  let t : ℝ := (z-(19/10))/((21/10)-(19/10))
  have ht : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hz.1) (by norm_num)
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by norm_num)).2
    linarith [hz.2]
  have h0 : 0 < (-1:ℝ)*scaledCharacteristic (0) (0) z (0) := by
    have hid : (-1:ℝ)*scaledCharacteristic (0) (0) z (0) = (9638181/1250000)*(1-t)^3+3*(10025139/1250000)*t*(1-t)^2+3*(10031941/1250000)*t^2*(1-t)+(9618579/1250000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (-1:ℝ)*scaledCharacteristic (0) (17/25000) z (0) := by
    have hid : (-1:ℝ)*scaledCharacteristic (0) (17/25000) z (0) = (118090984077/15625000000)*(1-t)^3+3*(122934537363/15625000000)*t*(1-t)^2+3*(123019677997/15625000000)*t^2*(1-t)+(117845625843/15625000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 0 < (-1:ℝ)*scaledCharacteristic (1/50000) (0) z (0) := by
    have hid : (-1:ℝ)*scaledCharacteristic (1/50000) (0) z (0) = (192703617/25000000)*(1-t)^3+3*(200442777/25000000)*t*(1-t)^2+3*(200578817/25000000)*t^2*(1-t)+(192311577/25000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : 0 < (-1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (0) := by
    have hid : (-1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (0) = (59026741101/7812500000)*(1-t)^3+3*(3840532359/488281250)*t*(1-t)^2+3*(61491088061/7812500000)*t^2*(1-t)+(1840751937/244140625)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he0 : 0 ≤ 50000*e := by positivity
  have he1 : 50000*e ≤ 1 := by linarith
  have hp0 : 0 ≤ (25000/17:ℝ)*p := by positivity
  have hp1 : (25000/17:ℝ)*p ≤ 1 := by linarith
  have hm := positive_affine_mix (50000*e) _ _ he0 he1
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h0 h1)
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h2 h3)
  rw [scaledCharacteristic_box_mix]
  convert hm using 1
  ring

theorem spectral_sign_highZero (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (29/10:ℝ) (31/10)) :
    0 < (1:ℝ)*scaledCharacteristic e p z (0) := by
  let t : ℝ := (z-(29/10))/((31/10)-(29/10))
  have ht : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hz.1) (by norm_num)
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by norm_num)).2
    linarith [hz.2]
  have h0 : 0 < (1:ℝ)*scaledCharacteristic (0) (0) z (0) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (0) z (0) = (18070149/1250000)*(1-t)^3+3*(22484951/1250000)*t*(1-t)^2+3*(27479949/1250000)*t^2*(1-t)+(33095151/1250000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : 0 < (1:ℝ)*scaledCharacteristic (0) (17/25000) z (0) := by
    have hid : (1:ℝ)*scaledCharacteristic (0) (17/25000) z (0) = (228734182533/15625000000)*(1-t)^3+3*(283994259167/15625000000)*t*(1-t)^2+3*(346516649133/15625000000)*t^2*(1-t)+(416802132567/15625000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (0) z (0) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (0) z (0) = (361462983/25000000)*(1-t)^3+3*(449759023/25000000)*t*(1-t)^2+3*(549658983/25000000)*t^2*(1-t)+(661963023/25000000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : 0 < (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (0) := by
    have hid : (1:ℝ)*scaledCharacteristic (1/50000) (17/25000) z (0) = (28596460551/1953125000)*(1-t)^3+3*(142015880521/7812500000)*t*(1-t)^2+3*(10829817219/488281250)*t^2*(1-t)+(208419817221/7812500000)*t^3 := by
      dsimp [t,scaledCharacteristic]
      ring
    rw [hid]
    exact positive_cubic_bernstein t _ _ _ _ ht ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he0 : 0 ≤ 50000*e := by positivity
  have he1 : 50000*e ≤ 1 := by linarith
  have hp0 : 0 ≤ (25000/17:ℝ)*p := by positivity
  have hp1 : (25000/17:ℝ)*p ≤ 1 := by linarith
  have hm := positive_affine_mix (50000*e) _ _ he0 he1
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h0 h1)
    (positive_affine_mix ((25000/17)*p) _ _ hp0 hp1 h2 h3)
  rw [scaledCharacteristic_box_mix]
  convert hm using 1
  ring

end CoreCouplingGlobal
