import proofs.SandwichImmunoassay.MarginCertificate

namespace SandwichImmunoassay

theorem stronger_margin_lo {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u 9 (19/20) (1/25) :=  by
  let t : ℝ :=  (u-20)/80
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 9 (19/20) (1/25)  = 
      (549739/25)*(1-t)^3+3*(6249899/25)*t*(1-t)^2+3*(23318059/25)*t^2*(1-t)+(554219/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem stronger_margin_hi {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u 11 (19/20) (1/25) :=  by
  let t : ℝ :=  (u-20)/80
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 11 (19/20) (1/25)  = 
      (601099/25)*(1-t)^3+3*(25425377/75)*t*(1-t)^2+3*(34047819/25)*t^2*(1-t)+(26119179/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem stronger_margin_polynomial {u d : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100)
    (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    0 ≤ marginPolynomial u d (19/20) (1/25) :=  by
  exact dilution_endpoints (by linarith) (by norm_num) (by norm_num) hd0 hd1
    (stronger_margin_lo hl hu) (stronger_margin_hi hl hu)

theorem stronger_margin_source {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hu : u ≤ 100) (hd0 : 9 ≤ d) (hd1 : d ≤ 11)
    (hr : (19/20) ≤ r) : (1/25) ≤ r*signal (u/d) pd qd-signal u p q :=  by
  exact source_certificate h j hc hd hk hj (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (stronger_margin_polynomial hl hu hd0 hd1)

theorem smaller_guard_lo {u : ℝ} (hl : 12 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u 9 (19/20) (1/100) :=  by
  let t : ℝ :=  (u-12)/88
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 9 (19/20) (1/100)  = 
      (142047/25)*(1-t)^3+3*(7251831/25)*t*(1-t)^2+3*(9789651/5)*t^2*(1-t)+(108194519/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem smaller_guard_hi {u : ℝ} (hl : 12 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u 11 (19/20) (1/100) :=  by
  let t : ℝ :=  (u-12)/88
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 11 (19/20) (1/100)  = 
      (447/25)*(1-t)^3+3*(26997893/75)*t*(1-t)^2+3*2477943*t^2*(1-t)+(141811479/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem smaller_guard_polynomial {u d : ℝ} (hl : 12 ≤ u) (hu : u ≤ 100)
    (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    0 ≤ marginPolynomial u d (19/20) (1/100) :=  by
  exact dilution_endpoints (by linarith) (by norm_num) (by norm_num) hd0 hd1
    (smaller_guard_lo hl hu) (smaller_guard_hi hl hu)

theorem smaller_guard_source {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 12 ≤ u) (hu : u ≤ 100) (hd0 : 9 ≤ d) (hd1 : d ≤ 11)
    (hr : (19/20) ≤ r) : (1/100) ≤ r*signal (u/d) pd qd-signal u p q :=  by
  exact source_certificate h j hc hd hk hj (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (smaller_guard_polynomial hl hu hd0 hd1)

theorem range_1000_lo {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 1000) :
    0 ≤ marginPolynomial u 9 (19/20) (1/200) :=  by
  let t : ℝ :=  (u-20)/980
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 9 (19/20) (1/200)  = 
      (3321809/25)*(1-t)^3+3*(163930579/25)*t*(1-t)^2+3*(4820411849/25)*t^2*(1-t)+(2207865619/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem range_1000_hi {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 1000) :
    0 ≤ marginPolynomial u 11 (19/20) (1/200) :=  by
  let t : ℝ :=  (u-20)/980
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 11 (19/20) (1/200)  = 
      (4019969/25)*(1-t)^3+3*(620561017/75)*t*(1-t)^2+3*(6102058209/25)*t^2*(1-t)+(5924733579/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem range_1000_polynomial {u d : ℝ} (hl : 20 ≤ u) (hu : u ≤ 1000)
    (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    0 ≤ marginPolynomial u d (19/20) (1/200) :=  by
  exact dilution_endpoints (by linarith) (by norm_num) (by norm_num) hd0 hd1
    (range_1000_lo hl hu) (range_1000_hi hl hu)

theorem range_1000_source {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hu : u ≤ 1000) (hd0 : 9 ≤ d) (hd1 : d ≤ 11)
    (hr : (19/20) ≤ r) : (1/200) ≤ r*signal (u/d) pd qd-signal u p q :=  by
  exact source_certificate h j hc hd hk hj (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (range_1000_polynomial hl hu hd0 hd1)

theorem range_10000_lo {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 10000) :
    0 ≤ marginPolynomial u 9 (19/20) (1/2000) :=  by
  let t : ℝ :=  (u-20)/9980
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 9 (19/20) (1/2000)  = 
      (3678218/25)*(1-t)^3+3*(351625757/5)*t*(1-t)^2+3*(506967701252/25)*t^2*(1-t)+(273117405619/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem range_10000_hi {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 10000) :
    0 ≤ marginPolynomial u 11 (19/20) (1/2000) :=  by
  let t : ℝ :=  (u-20)/9980
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 11 (19/20) (1/2000)  = 
      (4459538/25)*(1-t)^3+3*(1325600471/15)*t*(1-t)^2+3*(635241642132/25)*t^2*(1-t)+(656586393579/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem range_10000_polynomial {u d : ℝ} (hl : 20 ≤ u) (hu : u ≤ 10000)
    (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    0 ≤ marginPolynomial u d (19/20) (1/2000) :=  by
  exact dilution_endpoints (by linarith) (by norm_num) (by norm_num) hd0 hd1
    (range_10000_lo hl hu) (range_10000_hi hl hu)

theorem range_10000_source {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hu : u ≤ 10000) (hd0 : 9 ≤ d) (hd1 : d ≤ 11)
    (hr : (19/20) ≤ r) : (1/2000) ≤ r*signal (u/d) pd qd-signal u p q :=  by
  exact source_certificate h j hc hd hk hj (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (range_10000_polynomial hl hu hd0 hd1)

theorem attenuation_90pct_lo {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u 9 (171/200) (3/100) :=  by
  let t : ℝ :=  (u-20)/80
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 9 (171/200) (3/100)  = 
      (649209/25)*(1-t)^3+3*(6619929/25)*t*(1-t)^2+3*(25577049/25)*t^2*(1-t)+(19120569/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem attenuation_90pct_hi {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u 11 (171/200) (3/100) :=  by
  let t : ℝ :=  (u-20)/80
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 11 (171/200) (3/100)  = 
      (731469/25)*(1-t)^3+3*(8829389/25)*t*(1-t)^2+3*(35892909/25)*t^2*(1-t)+(43522029/25)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem attenuation_90pct_polynomial {u d : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100)
    (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    0 ≤ marginPolynomial u d (171/200) (3/100) :=  by
  exact dilution_endpoints (by linarith) (by norm_num) (by norm_num) hd0 hd1
    (attenuation_90pct_lo hl hu) (attenuation_90pct_hi hl hu)

theorem attenuation_90pct_source {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hu : u ≤ 100) (hd0 : 9 ≤ d) (hd1 : d ≤ 11)
    (hr : (171/200) ≤ r) : (3/100) ≤ r*signal (u/d) pd qd-signal u p q :=  by
  exact source_certificate h j hc hd hk hj (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (attenuation_90pct_polynomial hl hu hd0 hd1)

theorem availability_drift_lo {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u (60/7) (19/20) (3/100) :=  by
  let t : ℝ :=  (u-20)/80
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u (60/7) (19/20) (3/100)  = 
      (2495856/49)*(1-t)^3+3*(16732656/49)*t*(1-t)^2+3*1240944*t^2*(1-t)+(59452656/49)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem availability_drift_hi {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u (220/19) (19/20) (3/100) :=  by
  let t : ℝ :=  (u-20)/80
  have h0 : 0 ≤ t :=  by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 :=  by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u (220/19) (19/20) (3/100)  = 
      (23404464/361)*(1-t)^3+3*(183330864/361)*t*(1-t)^2+3*(710732464/361)*t^2*(1-t)+(1051113264/361)*t^3 :=  by dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem availability_drift_polynomial {u d : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100)
    (hd0 : (60/7) ≤ d) (hd1 : d ≤ (220/19)) :
    0 ≤ marginPolynomial u d (19/20) (3/100) :=  by
  exact dilution_endpoints (by linarith) (by norm_num) (by norm_num) hd0 hd1
    (availability_drift_lo hl hu) (availability_drift_hi hl hu)

theorem availability_drift_source {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hu : u ≤ 100) (hd0 : (60/7) ≤ d) (hd1 : d ≤ (220/19))
    (hr : (19/20) ≤ r) : (3/100) ≤ r*signal (u/d) pd qd-signal u p q :=  by
  exact source_certificate h j hc hd hk hj (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (availability_drift_polynomial hl hu hd0 hd1)

end SandwichImmunoassay
