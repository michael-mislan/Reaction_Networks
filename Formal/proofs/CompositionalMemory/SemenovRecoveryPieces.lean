import proofs.CompositionalMemory.SemenovRecoveryPiece
import proofs.CompositionalMemory.SemenovCoverChecks

namespace CompositionalMemory.Semenov.SemenovRecoveryPieces

def lowPiece00 : RecoveryPiece false where
  zc := SemenovLowInitialMetric.zc
  pc := SemenovLowInitialMetric.pc
  wc := SemenovLowInitialMetric.wc
  A := SemenovLowInitialMetric.A
  nr := SemenovLowInitialMetric.nr
  radius := SemenovLowInitialMetric.radius
  margin := SemenovLowInitialMetric.margin
  z := SemenovLowInitialMetric.z
  P := SemenovLowInitialMetric.P
  scale := SemenovLowInitialMetric.timeScale
  left := SemenovLowInitialMetric.leftTime
  right := SemenovLowInitialMetric.rightTime
  zLeft := SemenovLowInitialMetric.zl
  zRight := SemenovLowInitialMetric.zr
  pLeft := SemenovLowInitialMetric.pl
  pRight := SemenovLowInitialMetric.pr
  rb := SemenovLowInitialMetric.rbound
  fb := SemenovLowInitialMetric.fbound
  geometry := by
    convert SemenovLowInitialMetric.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowInitialMetric.eta]
  cache_z := by intro j; simp only [SemenovLowInitialMetric.z,SemenovLowInitialMetric.zCache,cached_ofFn_value]
  cache_P := SemenovLowInitialMetric.cache_P
  symmetry := SemenovLowInitialMetric.symmetry_and_endpoints.1
  z_endpoints := SemenovLowInitialMetric.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowInitialMetric.symmetry_and_endpoints.2.2.1
  timing := SemenovLowInitialMetric.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowInitialMetric.replay.2.2.2.1
  force_squares := SemenovLowInitialMetric.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowInitialMetric.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowInitialMetric.force_bound i t hl hu
  whitened := SemenovLowInitialMetric.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (0 : Fin 16) j

def lowPiece01 : RecoveryPiece false where
  zc := SemenovLowMetric01.zc
  pc := SemenovLowMetric01.pc
  wc := SemenovLowMetric01.wc
  A := SemenovLowMetric01.A
  nr := SemenovLowMetric01.nr
  radius := SemenovLowMetric01.radius
  margin := SemenovLowMetric01.margin
  z := SemenovLowMetric01.z
  P := SemenovLowMetric01.P
  scale := SemenovLowMetric01.timeScale
  left := SemenovLowMetric01.leftTime
  right := SemenovLowMetric01.rightTime
  zLeft := SemenovLowMetric01.zl
  zRight := SemenovLowMetric01.zr
  pLeft := SemenovLowMetric01.pl
  pRight := SemenovLowMetric01.pr
  rb := SemenovLowMetric01.rbound
  fb := SemenovLowMetric01.fbound
  geometry := by
    convert SemenovLowMetric01.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric01.eta]
  cache_z := by intro j; simp only [SemenovLowMetric01.z,SemenovLowMetric01.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric01.cache_P
  symmetry := SemenovLowMetric01.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric01.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric01.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric01.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric01.replay.2.2.2.1
  force_squares := SemenovLowMetric01.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric01.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric01.force_bound i t hl hu
  whitened := SemenovLowMetric01.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (1 : Fin 16) j

def lowPiece02 : RecoveryPiece false where
  zc := SemenovLowMetric02.zc
  pc := SemenovLowMetric02.pc
  wc := SemenovLowMetric02.wc
  A := SemenovLowMetric02.A
  nr := SemenovLowMetric02.nr
  radius := SemenovLowMetric02.radius
  margin := SemenovLowMetric02.margin
  z := SemenovLowMetric02.z
  P := SemenovLowMetric02.P
  scale := SemenovLowMetric02.timeScale
  left := SemenovLowMetric02.leftTime
  right := SemenovLowMetric02.rightTime
  zLeft := SemenovLowMetric02.zl
  zRight := SemenovLowMetric02.zr
  pLeft := SemenovLowMetric02.pl
  pRight := SemenovLowMetric02.pr
  rb := SemenovLowMetric02.rbound
  fb := SemenovLowMetric02.fbound
  geometry := by
    convert SemenovLowMetric02.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric02.eta]
  cache_z := by intro j; simp only [SemenovLowMetric02.z,SemenovLowMetric02.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric02.cache_P
  symmetry := SemenovLowMetric02.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric02.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric02.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric02.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric02.replay.2.2.2.1
  force_squares := SemenovLowMetric02.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric02.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric02.force_bound i t hl hu
  whitened := SemenovLowMetric02.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (2 : Fin 16) j

def lowPiece03 : RecoveryPiece false where
  zc := SemenovLowMetric03.zc
  pc := SemenovLowMetric03.pc
  wc := SemenovLowMetric03.wc
  A := SemenovLowMetric03.A
  nr := SemenovLowMetric03.nr
  radius := SemenovLowMetric03.radius
  margin := SemenovLowMetric03.margin
  z := SemenovLowMetric03.z
  P := SemenovLowMetric03.P
  scale := SemenovLowMetric03.timeScale
  left := SemenovLowMetric03.leftTime
  right := SemenovLowMetric03.rightTime
  zLeft := SemenovLowMetric03.zl
  zRight := SemenovLowMetric03.zr
  pLeft := SemenovLowMetric03.pl
  pRight := SemenovLowMetric03.pr
  rb := SemenovLowMetric03.rbound
  fb := SemenovLowMetric03.fbound
  geometry := by
    convert SemenovLowMetric03.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric03.eta]
  cache_z := by intro j; simp only [SemenovLowMetric03.z,SemenovLowMetric03.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric03.cache_P
  symmetry := SemenovLowMetric03.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric03.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric03.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric03.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric03.replay.2.2.2.1
  force_squares := SemenovLowMetric03.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric03.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric03.force_bound i t hl hu
  whitened := SemenovLowMetric03.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (3 : Fin 16) j

def lowPiece04 : RecoveryPiece false where
  zc := SemenovLowMetric04.zc
  pc := SemenovLowMetric04.pc
  wc := SemenovLowMetric04.wc
  A := SemenovLowMetric04.A
  nr := SemenovLowMetric04.nr
  radius := SemenovLowMetric04.radius
  margin := SemenovLowMetric04.margin
  z := SemenovLowMetric04.z
  P := SemenovLowMetric04.P
  scale := SemenovLowMetric04.timeScale
  left := SemenovLowMetric04.leftTime
  right := SemenovLowMetric04.rightTime
  zLeft := SemenovLowMetric04.zl
  zRight := SemenovLowMetric04.zr
  pLeft := SemenovLowMetric04.pl
  pRight := SemenovLowMetric04.pr
  rb := SemenovLowMetric04.rbound
  fb := SemenovLowMetric04.fbound
  geometry := by
    convert SemenovLowMetric04.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric04.eta]
  cache_z := by intro j; simp only [SemenovLowMetric04.z,SemenovLowMetric04.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric04.cache_P
  symmetry := SemenovLowMetric04.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric04.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric04.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric04.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric04.replay.2.2.2.1
  force_squares := SemenovLowMetric04.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric04.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric04.force_bound i t hl hu
  whitened := SemenovLowMetric04.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (4 : Fin 16) j

def lowPiece05 : RecoveryPiece false where
  zc := SemenovLowMetric05.zc
  pc := SemenovLowMetric05.pc
  wc := SemenovLowMetric05.wc
  A := SemenovLowMetric05.A
  nr := SemenovLowMetric05.nr
  radius := SemenovLowMetric05.radius
  margin := SemenovLowMetric05.margin
  z := SemenovLowMetric05.z
  P := SemenovLowMetric05.P
  scale := SemenovLowMetric05.timeScale
  left := SemenovLowMetric05.leftTime
  right := SemenovLowMetric05.rightTime
  zLeft := SemenovLowMetric05.zl
  zRight := SemenovLowMetric05.zr
  pLeft := SemenovLowMetric05.pl
  pRight := SemenovLowMetric05.pr
  rb := SemenovLowMetric05.rbound
  fb := SemenovLowMetric05.fbound
  geometry := by
    convert SemenovLowMetric05.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric05.eta]
  cache_z := by intro j; simp only [SemenovLowMetric05.z,SemenovLowMetric05.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric05.cache_P
  symmetry := SemenovLowMetric05.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric05.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric05.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric05.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric05.replay.2.2.2.1
  force_squares := SemenovLowMetric05.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric05.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric05.force_bound i t hl hu
  whitened := SemenovLowMetric05.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (5 : Fin 16) j

def lowPiece06 : RecoveryPiece false where
  zc := SemenovLowMetric06.zc
  pc := SemenovLowMetric06.pc
  wc := SemenovLowMetric06.wc
  A := SemenovLowMetric06.A
  nr := SemenovLowMetric06.nr
  radius := SemenovLowMetric06.radius
  margin := SemenovLowMetric06.margin
  z := SemenovLowMetric06.z
  P := SemenovLowMetric06.P
  scale := SemenovLowMetric06.timeScale
  left := SemenovLowMetric06.leftTime
  right := SemenovLowMetric06.rightTime
  zLeft := SemenovLowMetric06.zl
  zRight := SemenovLowMetric06.zr
  pLeft := SemenovLowMetric06.pl
  pRight := SemenovLowMetric06.pr
  rb := SemenovLowMetric06.rbound
  fb := SemenovLowMetric06.fbound
  geometry := by
    convert SemenovLowMetric06.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric06.eta]
  cache_z := by intro j; simp only [SemenovLowMetric06.z,SemenovLowMetric06.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric06.cache_P
  symmetry := SemenovLowMetric06.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric06.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric06.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric06.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric06.replay.2.2.2.1
  force_squares := SemenovLowMetric06.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric06.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric06.force_bound i t hl hu
  whitened := SemenovLowMetric06.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (6 : Fin 16) j

def lowPiece07 : RecoveryPiece false where
  zc := SemenovLowMetric07.zc
  pc := SemenovLowMetric07.pc
  wc := SemenovLowMetric07.wc
  A := SemenovLowMetric07.A
  nr := SemenovLowMetric07.nr
  radius := SemenovLowMetric07.radius
  margin := SemenovLowMetric07.margin
  z := SemenovLowMetric07.z
  P := SemenovLowMetric07.P
  scale := SemenovLowMetric07.timeScale
  left := SemenovLowMetric07.leftTime
  right := SemenovLowMetric07.rightTime
  zLeft := SemenovLowMetric07.zl
  zRight := SemenovLowMetric07.zr
  pLeft := SemenovLowMetric07.pl
  pRight := SemenovLowMetric07.pr
  rb := SemenovLowMetric07.rbound
  fb := SemenovLowMetric07.fbound
  geometry := by
    convert SemenovLowMetric07.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric07.eta]
  cache_z := by intro j; simp only [SemenovLowMetric07.z,SemenovLowMetric07.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric07.cache_P
  symmetry := SemenovLowMetric07.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric07.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric07.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric07.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric07.replay.2.2.2.1
  force_squares := SemenovLowMetric07.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric07.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric07.force_bound i t hl hu
  whitened := SemenovLowMetric07.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (7 : Fin 16) j

def lowPiece08 : RecoveryPiece false where
  zc := SemenovLowMetric08.zc
  pc := SemenovLowMetric08.pc
  wc := SemenovLowMetric08.wc
  A := SemenovLowMetric08.A
  nr := SemenovLowMetric08.nr
  radius := SemenovLowMetric08.radius
  margin := SemenovLowMetric08.margin
  z := SemenovLowMetric08.z
  P := SemenovLowMetric08.P
  scale := SemenovLowMetric08.timeScale
  left := SemenovLowMetric08.leftTime
  right := SemenovLowMetric08.rightTime
  zLeft := SemenovLowMetric08.zl
  zRight := SemenovLowMetric08.zr
  pLeft := SemenovLowMetric08.pl
  pRight := SemenovLowMetric08.pr
  rb := SemenovLowMetric08.rbound
  fb := SemenovLowMetric08.fbound
  geometry := by
    convert SemenovLowMetric08.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric08.eta]
  cache_z := by intro j; simp only [SemenovLowMetric08.z,SemenovLowMetric08.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric08.cache_P
  symmetry := SemenovLowMetric08.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric08.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric08.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric08.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric08.replay.2.2.2.1
  force_squares := SemenovLowMetric08.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric08.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric08.force_bound i t hl hu
  whitened := SemenovLowMetric08.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (8 : Fin 16) j

def lowPiece09 : RecoveryPiece false where
  zc := SemenovLowMetric09.zc
  pc := SemenovLowMetric09.pc
  wc := SemenovLowMetric09.wc
  A := SemenovLowMetric09.A
  nr := SemenovLowMetric09.nr
  radius := SemenovLowMetric09.radius
  margin := SemenovLowMetric09.margin
  z := SemenovLowMetric09.z
  P := SemenovLowMetric09.P
  scale := SemenovLowMetric09.timeScale
  left := SemenovLowMetric09.leftTime
  right := SemenovLowMetric09.rightTime
  zLeft := SemenovLowMetric09.zl
  zRight := SemenovLowMetric09.zr
  pLeft := SemenovLowMetric09.pl
  pRight := SemenovLowMetric09.pr
  rb := SemenovLowMetric09.rbound
  fb := SemenovLowMetric09.fbound
  geometry := by
    convert SemenovLowMetric09.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric09.eta]
  cache_z := by intro j; simp only [SemenovLowMetric09.z,SemenovLowMetric09.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric09.cache_P
  symmetry := SemenovLowMetric09.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric09.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric09.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric09.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric09.replay.2.2.2.1
  force_squares := SemenovLowMetric09.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric09.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric09.force_bound i t hl hu
  whitened := SemenovLowMetric09.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (9 : Fin 16) j

def lowPiece10 : RecoveryPiece false where
  zc := SemenovLowMetric10.zc
  pc := SemenovLowMetric10.pc
  wc := SemenovLowMetric10.wc
  A := SemenovLowMetric10.A
  nr := SemenovLowMetric10.nr
  radius := SemenovLowMetric10.radius
  margin := SemenovLowMetric10.margin
  z := SemenovLowMetric10.z
  P := SemenovLowMetric10.P
  scale := SemenovLowMetric10.timeScale
  left := SemenovLowMetric10.leftTime
  right := SemenovLowMetric10.rightTime
  zLeft := SemenovLowMetric10.zl
  zRight := SemenovLowMetric10.zr
  pLeft := SemenovLowMetric10.pl
  pRight := SemenovLowMetric10.pr
  rb := SemenovLowMetric10.rbound
  fb := SemenovLowMetric10.fbound
  geometry := by
    convert SemenovLowMetric10.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric10.eta]
  cache_z := by intro j; simp only [SemenovLowMetric10.z,SemenovLowMetric10.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric10.cache_P
  symmetry := SemenovLowMetric10.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric10.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric10.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric10.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric10.replay.2.2.2.1
  force_squares := SemenovLowMetric10.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric10.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric10.force_bound i t hl hu
  whitened := SemenovLowMetric10.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (10 : Fin 16) j

def lowPiece11 : RecoveryPiece false where
  zc := SemenovLowMetric11.zc
  pc := SemenovLowMetric11.pc
  wc := SemenovLowMetric11.wc
  A := SemenovLowMetric11.A
  nr := SemenovLowMetric11.nr
  radius := SemenovLowMetric11.radius
  margin := SemenovLowMetric11.margin
  z := SemenovLowMetric11.z
  P := SemenovLowMetric11.P
  scale := SemenovLowMetric11.timeScale
  left := SemenovLowMetric11.leftTime
  right := SemenovLowMetric11.rightTime
  zLeft := SemenovLowMetric11.zl
  zRight := SemenovLowMetric11.zr
  pLeft := SemenovLowMetric11.pl
  pRight := SemenovLowMetric11.pr
  rb := SemenovLowMetric11.rbound
  fb := SemenovLowMetric11.fbound
  geometry := by
    convert SemenovLowMetric11.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric11.eta]
  cache_z := by intro j; simp only [SemenovLowMetric11.z,SemenovLowMetric11.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric11.cache_P
  symmetry := SemenovLowMetric11.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric11.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric11.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric11.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric11.replay.2.2.2.1
  force_squares := SemenovLowMetric11.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric11.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric11.force_bound i t hl hu
  whitened := SemenovLowMetric11.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (11 : Fin 16) j

def lowPiece12 : RecoveryPiece false where
  zc := SemenovLowMetric12.zc
  pc := SemenovLowMetric12.pc
  wc := SemenovLowMetric12.wc
  A := SemenovLowMetric12.A
  nr := SemenovLowMetric12.nr
  radius := SemenovLowMetric12.radius
  margin := SemenovLowMetric12.margin
  z := SemenovLowMetric12.z
  P := SemenovLowMetric12.P
  scale := SemenovLowMetric12.timeScale
  left := SemenovLowMetric12.leftTime
  right := SemenovLowMetric12.rightTime
  zLeft := SemenovLowMetric12.zl
  zRight := SemenovLowMetric12.zr
  pLeft := SemenovLowMetric12.pl
  pRight := SemenovLowMetric12.pr
  rb := SemenovLowMetric12.rbound
  fb := SemenovLowMetric12.fbound
  geometry := by
    convert SemenovLowMetric12.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric12.eta]
  cache_z := by intro j; simp only [SemenovLowMetric12.z,SemenovLowMetric12.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric12.cache_P
  symmetry := SemenovLowMetric12.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric12.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric12.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric12.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric12.replay.2.2.2.1
  force_squares := SemenovLowMetric12.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric12.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric12.force_bound i t hl hu
  whitened := SemenovLowMetric12.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (12 : Fin 16) j

def lowPiece13 : RecoveryPiece false where
  zc := SemenovLowMetric13.zc
  pc := SemenovLowMetric13.pc
  wc := SemenovLowMetric13.wc
  A := SemenovLowMetric13.A
  nr := SemenovLowMetric13.nr
  radius := SemenovLowMetric13.radius
  margin := SemenovLowMetric13.margin
  z := SemenovLowMetric13.z
  P := SemenovLowMetric13.P
  scale := SemenovLowMetric13.timeScale
  left := SemenovLowMetric13.leftTime
  right := SemenovLowMetric13.rightTime
  zLeft := SemenovLowMetric13.zl
  zRight := SemenovLowMetric13.zr
  pLeft := SemenovLowMetric13.pl
  pRight := SemenovLowMetric13.pr
  rb := SemenovLowMetric13.rbound
  fb := SemenovLowMetric13.fbound
  geometry := by
    convert SemenovLowMetric13.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric13.eta]
  cache_z := by intro j; simp only [SemenovLowMetric13.z,SemenovLowMetric13.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric13.cache_P
  symmetry := SemenovLowMetric13.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric13.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric13.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric13.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric13.replay.2.2.2.1
  force_squares := SemenovLowMetric13.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric13.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric13.force_bound i t hl hu
  whitened := SemenovLowMetric13.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (13 : Fin 16) j

def lowPiece14 : RecoveryPiece false where
  zc := SemenovLowMetric14.zc
  pc := SemenovLowMetric14.pc
  wc := SemenovLowMetric14.wc
  A := SemenovLowMetric14.A
  nr := SemenovLowMetric14.nr
  radius := SemenovLowMetric14.radius
  margin := SemenovLowMetric14.margin
  z := SemenovLowMetric14.z
  P := SemenovLowMetric14.P
  scale := SemenovLowMetric14.timeScale
  left := SemenovLowMetric14.leftTime
  right := SemenovLowMetric14.rightTime
  zLeft := SemenovLowMetric14.zl
  zRight := SemenovLowMetric14.zr
  pLeft := SemenovLowMetric14.pl
  pRight := SemenovLowMetric14.pr
  rb := SemenovLowMetric14.rbound
  fb := SemenovLowMetric14.fbound
  geometry := by
    convert SemenovLowMetric14.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric14.eta]
  cache_z := by intro j; simp only [SemenovLowMetric14.z,SemenovLowMetric14.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric14.cache_P
  symmetry := SemenovLowMetric14.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric14.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric14.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric14.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric14.replay.2.2.2.1
  force_squares := SemenovLowMetric14.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric14.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric14.force_bound i t hl hu
  whitened := SemenovLowMetric14.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (14 : Fin 16) j

def lowPiece15 : RecoveryPiece false where
  zc := SemenovLowMetric15.zc
  pc := SemenovLowMetric15.pc
  wc := SemenovLowMetric15.wc
  A := SemenovLowMetric15.A
  nr := SemenovLowMetric15.nr
  radius := SemenovLowMetric15.radius
  margin := SemenovLowMetric15.margin
  z := SemenovLowMetric15.z
  P := SemenovLowMetric15.P
  scale := SemenovLowMetric15.timeScale
  left := SemenovLowMetric15.leftTime
  right := SemenovLowMetric15.rightTime
  zLeft := SemenovLowMetric15.zl
  zRight := SemenovLowMetric15.zr
  pLeft := SemenovLowMetric15.pl
  pRight := SemenovLowMetric15.pr
  rb := SemenovLowMetric15.rbound
  fb := SemenovLowMetric15.fbound
  geometry := by
    convert SemenovLowMetric15.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovLowMetric15.eta]
  cache_z := by intro j; simp only [SemenovLowMetric15.z,SemenovLowMetric15.zCache,cached_ofFn_value]
  cache_P := SemenovLowMetric15.cache_P
  symmetry := SemenovLowMetric15.symmetry_and_endpoints.1
  z_endpoints := SemenovLowMetric15.symmetry_and_endpoints.2.1
  p_endpoints := SemenovLowMetric15.symmetry_and_endpoints.2.2.1
  timing := SemenovLowMetric15.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovLowMetric15.replay.2.2.2.1
  force_squares := SemenovLowMetric15.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovLowMetric15.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovLowMetric15.force_bound i t hl hu
  whitened := SemenovLowMetric15.whitened_eq
  capacity := fun j => SemenovCoverChecks.low_checks.2.2.2.2 (15 : Fin 16) j

def lowPieces : Fin 16 → RecoveryPiece false := ![lowPiece00,lowPiece01,lowPiece02,lowPiece03,lowPiece04,lowPiece05,lowPiece06,lowPiece07,lowPiece08,lowPiece09,lowPiece10,lowPiece11,lowPiece12,lowPiece13,lowPiece14,lowPiece15]

def highPiece00 : RecoveryPiece true where
  zc := SemenovHighInitialMetric.zc
  pc := SemenovHighInitialMetric.pc
  wc := SemenovHighInitialMetric.wc
  A := SemenovHighInitialMetric.A
  nr := SemenovHighInitialMetric.nr
  radius := SemenovHighInitialMetric.radius
  margin := SemenovHighInitialMetric.margin
  z := SemenovHighInitialMetric.z
  P := SemenovHighInitialMetric.P
  scale := SemenovHighInitialMetric.timeScale
  left := SemenovHighInitialMetric.leftTime
  right := SemenovHighInitialMetric.rightTime
  zLeft := SemenovHighInitialMetric.zl
  zRight := SemenovHighInitialMetric.zr
  pLeft := SemenovHighInitialMetric.pl
  pRight := SemenovHighInitialMetric.pr
  rb := SemenovHighInitialMetric.rbound
  fb := SemenovHighInitialMetric.fbound
  geometry := by
    convert SemenovHighInitialMetric.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighInitialMetric.eta]
  cache_z := by intro j; simp only [SemenovHighInitialMetric.z,SemenovHighInitialMetric.zCache,cached_ofFn_value]
  cache_P := SemenovHighInitialMetric.cache_P
  symmetry := SemenovHighInitialMetric.symmetry_and_endpoints.1
  z_endpoints := SemenovHighInitialMetric.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighInitialMetric.symmetry_and_endpoints.2.2.1
  timing := SemenovHighInitialMetric.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighInitialMetric.replay.2.2.2.1
  force_squares := SemenovHighInitialMetric.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighInitialMetric.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighInitialMetric.force_bound i t hl hu
  whitened := SemenovHighInitialMetric.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (0 : Fin 22) j

def highPiece01 : RecoveryPiece true where
  zc := SemenovHighMetric01.zc
  pc := SemenovHighMetric01.pc
  wc := SemenovHighMetric01.wc
  A := SemenovHighMetric01.A
  nr := SemenovHighMetric01.nr
  radius := SemenovHighMetric01.radius
  margin := SemenovHighMetric01.margin
  z := SemenovHighMetric01.z
  P := SemenovHighMetric01.P
  scale := SemenovHighMetric01.timeScale
  left := SemenovHighMetric01.leftTime
  right := SemenovHighMetric01.rightTime
  zLeft := SemenovHighMetric01.zl
  zRight := SemenovHighMetric01.zr
  pLeft := SemenovHighMetric01.pl
  pRight := SemenovHighMetric01.pr
  rb := SemenovHighMetric01.rbound
  fb := SemenovHighMetric01.fbound
  geometry := by
    convert SemenovHighMetric01.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric01.eta]
  cache_z := by intro j; simp only [SemenovHighMetric01.z,SemenovHighMetric01.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric01.cache_P
  symmetry := SemenovHighMetric01.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric01.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric01.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric01.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric01.replay.2.2.2.1
  force_squares := SemenovHighMetric01.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric01.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric01.force_bound i t hl hu
  whitened := SemenovHighMetric01.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (1 : Fin 22) j

def highPiece02 : RecoveryPiece true where
  zc := SemenovHighMetric02.zc
  pc := SemenovHighMetric02.pc
  wc := SemenovHighMetric02.wc
  A := SemenovHighMetric02.A
  nr := SemenovHighMetric02.nr
  radius := SemenovHighMetric02.radius
  margin := SemenovHighMetric02.margin
  z := SemenovHighMetric02.z
  P := SemenovHighMetric02.P
  scale := SemenovHighMetric02.timeScale
  left := SemenovHighMetric02.leftTime
  right := SemenovHighMetric02.rightTime
  zLeft := SemenovHighMetric02.zl
  zRight := SemenovHighMetric02.zr
  pLeft := SemenovHighMetric02.pl
  pRight := SemenovHighMetric02.pr
  rb := SemenovHighMetric02.rbound
  fb := SemenovHighMetric02.fbound
  geometry := by
    convert SemenovHighMetric02.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric02.eta]
  cache_z := by intro j; simp only [SemenovHighMetric02.z,SemenovHighMetric02.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric02.cache_P
  symmetry := SemenovHighMetric02.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric02.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric02.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric02.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric02.replay.2.2.2.1
  force_squares := SemenovHighMetric02.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric02.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric02.force_bound i t hl hu
  whitened := SemenovHighMetric02.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (2 : Fin 22) j

def highPiece03 : RecoveryPiece true where
  zc := SemenovHighMetric03.zc
  pc := SemenovHighMetric03.pc
  wc := SemenovHighMetric03.wc
  A := SemenovHighMetric03.A
  nr := SemenovHighMetric03.nr
  radius := SemenovHighMetric03.radius
  margin := SemenovHighMetric03.margin
  z := SemenovHighMetric03.z
  P := SemenovHighMetric03.P
  scale := SemenovHighMetric03.timeScale
  left := SemenovHighMetric03.leftTime
  right := SemenovHighMetric03.rightTime
  zLeft := SemenovHighMetric03.zl
  zRight := SemenovHighMetric03.zr
  pLeft := SemenovHighMetric03.pl
  pRight := SemenovHighMetric03.pr
  rb := SemenovHighMetric03.rbound
  fb := SemenovHighMetric03.fbound
  geometry := by
    convert SemenovHighMetric03.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric03.eta]
  cache_z := by intro j; simp only [SemenovHighMetric03.z,SemenovHighMetric03.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric03.cache_P
  symmetry := SemenovHighMetric03.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric03.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric03.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric03.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric03.replay.2.2.2.1
  force_squares := SemenovHighMetric03.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric03.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric03.force_bound i t hl hu
  whitened := SemenovHighMetric03.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (3 : Fin 22) j

def highPiece04 : RecoveryPiece true where
  zc := SemenovHighMetric04.zc
  pc := SemenovHighMetric04.pc
  wc := SemenovHighMetric04.wc
  A := SemenovHighMetric04.A
  nr := SemenovHighMetric04.nr
  radius := SemenovHighMetric04.radius
  margin := SemenovHighMetric04.margin
  z := SemenovHighMetric04.z
  P := SemenovHighMetric04.P
  scale := SemenovHighMetric04.timeScale
  left := SemenovHighMetric04.leftTime
  right := SemenovHighMetric04.rightTime
  zLeft := SemenovHighMetric04.zl
  zRight := SemenovHighMetric04.zr
  pLeft := SemenovHighMetric04.pl
  pRight := SemenovHighMetric04.pr
  rb := SemenovHighMetric04.rbound
  fb := SemenovHighMetric04.fbound
  geometry := by
    convert SemenovHighMetric04.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric04.eta]
  cache_z := by intro j; simp only [SemenovHighMetric04.z,SemenovHighMetric04.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric04.cache_P
  symmetry := SemenovHighMetric04.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric04.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric04.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric04.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric04.replay.2.2.2.1
  force_squares := SemenovHighMetric04.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric04.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric04.force_bound i t hl hu
  whitened := SemenovHighMetric04.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (4 : Fin 22) j

def highPiece05 : RecoveryPiece true where
  zc := SemenovHighMetric05.zc
  pc := SemenovHighMetric05.pc
  wc := SemenovHighMetric05.wc
  A := SemenovHighMetric05.A
  nr := SemenovHighMetric05.nr
  radius := SemenovHighMetric05.radius
  margin := SemenovHighMetric05.margin
  z := SemenovHighMetric05.z
  P := SemenovHighMetric05.P
  scale := SemenovHighMetric05.timeScale
  left := SemenovHighMetric05.leftTime
  right := SemenovHighMetric05.rightTime
  zLeft := SemenovHighMetric05.zl
  zRight := SemenovHighMetric05.zr
  pLeft := SemenovHighMetric05.pl
  pRight := SemenovHighMetric05.pr
  rb := SemenovHighMetric05.rbound
  fb := SemenovHighMetric05.fbound
  geometry := by
    convert SemenovHighMetric05.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric05.eta]
  cache_z := by intro j; simp only [SemenovHighMetric05.z,SemenovHighMetric05.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric05.cache_P
  symmetry := SemenovHighMetric05.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric05.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric05.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric05.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric05.replay.2.2.2.1
  force_squares := SemenovHighMetric05.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric05.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric05.force_bound i t hl hu
  whitened := SemenovHighMetric05.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (5 : Fin 22) j

def highPiece06 : RecoveryPiece true where
  zc := SemenovHighMetric06.zc
  pc := SemenovHighMetric06.pc
  wc := SemenovHighMetric06.wc
  A := SemenovHighMetric06.A
  nr := SemenovHighMetric06.nr
  radius := SemenovHighMetric06.radius
  margin := SemenovHighMetric06.margin
  z := SemenovHighMetric06.z
  P := SemenovHighMetric06.P
  scale := SemenovHighMetric06.timeScale
  left := SemenovHighMetric06.leftTime
  right := SemenovHighMetric06.rightTime
  zLeft := SemenovHighMetric06.zl
  zRight := SemenovHighMetric06.zr
  pLeft := SemenovHighMetric06.pl
  pRight := SemenovHighMetric06.pr
  rb := SemenovHighMetric06.rbound
  fb := SemenovHighMetric06.fbound
  geometry := by
    convert SemenovHighMetric06.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric06.eta]
  cache_z := by intro j; simp only [SemenovHighMetric06.z,SemenovHighMetric06.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric06.cache_P
  symmetry := SemenovHighMetric06.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric06.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric06.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric06.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric06.replay.2.2.2.1
  force_squares := SemenovHighMetric06.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric06.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric06.force_bound i t hl hu
  whitened := SemenovHighMetric06.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (6 : Fin 22) j

def highPiece07 : RecoveryPiece true where
  zc := SemenovHighMetric07.zc
  pc := SemenovHighMetric07.pc
  wc := SemenovHighMetric07.wc
  A := SemenovHighMetric07.A
  nr := SemenovHighMetric07.nr
  radius := SemenovHighMetric07.radius
  margin := SemenovHighMetric07.margin
  z := SemenovHighMetric07.z
  P := SemenovHighMetric07.P
  scale := SemenovHighMetric07.timeScale
  left := SemenovHighMetric07.leftTime
  right := SemenovHighMetric07.rightTime
  zLeft := SemenovHighMetric07.zl
  zRight := SemenovHighMetric07.zr
  pLeft := SemenovHighMetric07.pl
  pRight := SemenovHighMetric07.pr
  rb := SemenovHighMetric07.rbound
  fb := SemenovHighMetric07.fbound
  geometry := by
    convert SemenovHighMetric07.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric07.eta]
  cache_z := by intro j; simp only [SemenovHighMetric07.z,SemenovHighMetric07.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric07.cache_P
  symmetry := SemenovHighMetric07.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric07.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric07.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric07.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric07.replay.2.2.2.1
  force_squares := SemenovHighMetric07.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric07.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric07.force_bound i t hl hu
  whitened := SemenovHighMetric07.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (7 : Fin 22) j

def highPiece08 : RecoveryPiece true where
  zc := SemenovHighMetric08.zc
  pc := SemenovHighMetric08.pc
  wc := SemenovHighMetric08.wc
  A := SemenovHighMetric08.A
  nr := SemenovHighMetric08.nr
  radius := SemenovHighMetric08.radius
  margin := SemenovHighMetric08.margin
  z := SemenovHighMetric08.z
  P := SemenovHighMetric08.P
  scale := SemenovHighMetric08.timeScale
  left := SemenovHighMetric08.leftTime
  right := SemenovHighMetric08.rightTime
  zLeft := SemenovHighMetric08.zl
  zRight := SemenovHighMetric08.zr
  pLeft := SemenovHighMetric08.pl
  pRight := SemenovHighMetric08.pr
  rb := SemenovHighMetric08.rbound
  fb := SemenovHighMetric08.fbound
  geometry := by
    convert SemenovHighMetric08.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric08.eta]
  cache_z := by intro j; simp only [SemenovHighMetric08.z,SemenovHighMetric08.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric08.cache_P
  symmetry := SemenovHighMetric08.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric08.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric08.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric08.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric08.replay.2.2.2.1
  force_squares := SemenovHighMetric08.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric08.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric08.force_bound i t hl hu
  whitened := SemenovHighMetric08.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (8 : Fin 22) j

def highPiece09 : RecoveryPiece true where
  zc := SemenovHighMetric09.zc
  pc := SemenovHighMetric09.pc
  wc := SemenovHighMetric09.wc
  A := SemenovHighMetric09.A
  nr := SemenovHighMetric09.nr
  radius := SemenovHighMetric09.radius
  margin := SemenovHighMetric09.margin
  z := SemenovHighMetric09.z
  P := SemenovHighMetric09.P
  scale := SemenovHighMetric09.timeScale
  left := SemenovHighMetric09.leftTime
  right := SemenovHighMetric09.rightTime
  zLeft := SemenovHighMetric09.zl
  zRight := SemenovHighMetric09.zr
  pLeft := SemenovHighMetric09.pl
  pRight := SemenovHighMetric09.pr
  rb := SemenovHighMetric09.rbound
  fb := SemenovHighMetric09.fbound
  geometry := by
    convert SemenovHighMetric09.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric09.eta]
  cache_z := by intro j; simp only [SemenovHighMetric09.z,SemenovHighMetric09.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric09.cache_P
  symmetry := SemenovHighMetric09.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric09.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric09.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric09.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric09.replay.2.2.2.1
  force_squares := SemenovHighMetric09.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric09.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric09.force_bound i t hl hu
  whitened := SemenovHighMetric09.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (9 : Fin 22) j

def highPiece10 : RecoveryPiece true where
  zc := SemenovHighMetric10.zc
  pc := SemenovHighMetric10.pc
  wc := SemenovHighMetric10.wc
  A := SemenovHighMetric10.A
  nr := SemenovHighMetric10.nr
  radius := SemenovHighMetric10.radius
  margin := SemenovHighMetric10.margin
  z := SemenovHighMetric10.z
  P := SemenovHighMetric10.P
  scale := SemenovHighMetric10.timeScale
  left := SemenovHighMetric10.leftTime
  right := SemenovHighMetric10.rightTime
  zLeft := SemenovHighMetric10.zl
  zRight := SemenovHighMetric10.zr
  pLeft := SemenovHighMetric10.pl
  pRight := SemenovHighMetric10.pr
  rb := SemenovHighMetric10.rbound
  fb := SemenovHighMetric10.fbound
  geometry := by
    convert SemenovHighMetric10.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric10.eta]
  cache_z := by intro j; simp only [SemenovHighMetric10.z,SemenovHighMetric10.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric10.cache_P
  symmetry := SemenovHighMetric10.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric10.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric10.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric10.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric10.replay.2.2.2.1
  force_squares := SemenovHighMetric10.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric10.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric10.force_bound i t hl hu
  whitened := SemenovHighMetric10.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (10 : Fin 22) j

def highPiece11 : RecoveryPiece true where
  zc := SemenovHighMetric11.zc
  pc := SemenovHighMetric11.pc
  wc := SemenovHighMetric11.wc
  A := SemenovHighMetric11.A
  nr := SemenovHighMetric11.nr
  radius := SemenovHighMetric11.radius
  margin := SemenovHighMetric11.margin
  z := SemenovHighMetric11.z
  P := SemenovHighMetric11.P
  scale := SemenovHighMetric11.timeScale
  left := SemenovHighMetric11.leftTime
  right := SemenovHighMetric11.rightTime
  zLeft := SemenovHighMetric11.zl
  zRight := SemenovHighMetric11.zr
  pLeft := SemenovHighMetric11.pl
  pRight := SemenovHighMetric11.pr
  rb := SemenovHighMetric11.rbound
  fb := SemenovHighMetric11.fbound
  geometry := by
    convert SemenovHighMetric11.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric11.eta]
  cache_z := by intro j; simp only [SemenovHighMetric11.z,SemenovHighMetric11.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric11.cache_P
  symmetry := SemenovHighMetric11.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric11.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric11.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric11.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric11.replay.2.2.2.1
  force_squares := SemenovHighMetric11.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric11.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric11.force_bound i t hl hu
  whitened := SemenovHighMetric11.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (11 : Fin 22) j

def highPiece12 : RecoveryPiece true where
  zc := SemenovHighMetric12.zc
  pc := SemenovHighMetric12.pc
  wc := SemenovHighMetric12.wc
  A := SemenovHighMetric12.A
  nr := SemenovHighMetric12.nr
  radius := SemenovHighMetric12.radius
  margin := SemenovHighMetric12.margin
  z := SemenovHighMetric12.z
  P := SemenovHighMetric12.P
  scale := SemenovHighMetric12.timeScale
  left := SemenovHighMetric12.leftTime
  right := SemenovHighMetric12.rightTime
  zLeft := SemenovHighMetric12.zl
  zRight := SemenovHighMetric12.zr
  pLeft := SemenovHighMetric12.pl
  pRight := SemenovHighMetric12.pr
  rb := SemenovHighMetric12.rbound
  fb := SemenovHighMetric12.fbound
  geometry := by
    convert SemenovHighMetric12.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric12.eta]
  cache_z := by intro j; simp only [SemenovHighMetric12.z,SemenovHighMetric12.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric12.cache_P
  symmetry := SemenovHighMetric12.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric12.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric12.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric12.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric12.replay.2.2.2.1
  force_squares := SemenovHighMetric12.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric12.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric12.force_bound i t hl hu
  whitened := SemenovHighMetric12.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (12 : Fin 22) j

def highPiece13 : RecoveryPiece true where
  zc := SemenovHighMetric13.zc
  pc := SemenovHighMetric13.pc
  wc := SemenovHighMetric13.wc
  A := SemenovHighMetric13.A
  nr := SemenovHighMetric13.nr
  radius := SemenovHighMetric13.radius
  margin := SemenovHighMetric13.margin
  z := SemenovHighMetric13.z
  P := SemenovHighMetric13.P
  scale := SemenovHighMetric13.timeScale
  left := SemenovHighMetric13.leftTime
  right := SemenovHighMetric13.rightTime
  zLeft := SemenovHighMetric13.zl
  zRight := SemenovHighMetric13.zr
  pLeft := SemenovHighMetric13.pl
  pRight := SemenovHighMetric13.pr
  rb := SemenovHighMetric13.rbound
  fb := SemenovHighMetric13.fbound
  geometry := by
    convert SemenovHighMetric13.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric13.eta]
  cache_z := by intro j; simp only [SemenovHighMetric13.z,SemenovHighMetric13.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric13.cache_P
  symmetry := SemenovHighMetric13.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric13.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric13.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric13.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric13.replay.2.2.2.1
  force_squares := SemenovHighMetric13.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric13.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric13.force_bound i t hl hu
  whitened := SemenovHighMetric13.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (13 : Fin 22) j

def highPiece14 : RecoveryPiece true where
  zc := SemenovHighMetric14.zc
  pc := SemenovHighMetric14.pc
  wc := SemenovHighMetric14.wc
  A := SemenovHighMetric14.A
  nr := SemenovHighMetric14.nr
  radius := SemenovHighMetric14.radius
  margin := SemenovHighMetric14.margin
  z := SemenovHighMetric14.z
  P := SemenovHighMetric14.P
  scale := SemenovHighMetric14.timeScale
  left := SemenovHighMetric14.leftTime
  right := SemenovHighMetric14.rightTime
  zLeft := SemenovHighMetric14.zl
  zRight := SemenovHighMetric14.zr
  pLeft := SemenovHighMetric14.pl
  pRight := SemenovHighMetric14.pr
  rb := SemenovHighMetric14.rbound
  fb := SemenovHighMetric14.fbound
  geometry := by
    convert SemenovHighMetric14.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric14.eta]
  cache_z := by intro j; simp only [SemenovHighMetric14.z,SemenovHighMetric14.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric14.cache_P
  symmetry := SemenovHighMetric14.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric14.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric14.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric14.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric14.replay.2.2.2.1
  force_squares := SemenovHighMetric14.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric14.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric14.force_bound i t hl hu
  whitened := SemenovHighMetric14.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (14 : Fin 22) j

def highPiece15 : RecoveryPiece true where
  zc := SemenovHighMetric15.zc
  pc := SemenovHighMetric15.pc
  wc := SemenovHighMetric15.wc
  A := SemenovHighMetric15.A
  nr := SemenovHighMetric15.nr
  radius := SemenovHighMetric15.radius
  margin := SemenovHighMetric15.margin
  z := SemenovHighMetric15.z
  P := SemenovHighMetric15.P
  scale := SemenovHighMetric15.timeScale
  left := SemenovHighMetric15.leftTime
  right := SemenovHighMetric15.rightTime
  zLeft := SemenovHighMetric15.zl
  zRight := SemenovHighMetric15.zr
  pLeft := SemenovHighMetric15.pl
  pRight := SemenovHighMetric15.pr
  rb := SemenovHighMetric15.rbound
  fb := SemenovHighMetric15.fbound
  geometry := by
    convert SemenovHighMetric15.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric15.eta]
  cache_z := by intro j; simp only [SemenovHighMetric15.z,SemenovHighMetric15.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric15.cache_P
  symmetry := SemenovHighMetric15.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric15.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric15.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric15.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric15.replay.2.2.2.1
  force_squares := SemenovHighMetric15.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric15.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric15.force_bound i t hl hu
  whitened := SemenovHighMetric15.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (15 : Fin 22) j

def highPiece16 : RecoveryPiece true where
  zc := SemenovHighMetric16.zc
  pc := SemenovHighMetric16.pc
  wc := SemenovHighMetric16.wc
  A := SemenovHighMetric16.A
  nr := SemenovHighMetric16.nr
  radius := SemenovHighMetric16.radius
  margin := SemenovHighMetric16.margin
  z := SemenovHighMetric16.z
  P := SemenovHighMetric16.P
  scale := SemenovHighMetric16.timeScale
  left := SemenovHighMetric16.leftTime
  right := SemenovHighMetric16.rightTime
  zLeft := SemenovHighMetric16.zl
  zRight := SemenovHighMetric16.zr
  pLeft := SemenovHighMetric16.pl
  pRight := SemenovHighMetric16.pr
  rb := SemenovHighMetric16.rbound
  fb := SemenovHighMetric16.fbound
  geometry := by
    convert SemenovHighMetric16.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric16.eta]
  cache_z := by intro j; simp only [SemenovHighMetric16.z,SemenovHighMetric16.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric16.cache_P
  symmetry := SemenovHighMetric16.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric16.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric16.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric16.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric16.replay.2.2.2.1
  force_squares := SemenovHighMetric16.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric16.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric16.force_bound i t hl hu
  whitened := SemenovHighMetric16.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (16 : Fin 22) j

def highPiece17 : RecoveryPiece true where
  zc := SemenovHighMetric17.zc
  pc := SemenovHighMetric17.pc
  wc := SemenovHighMetric17.wc
  A := SemenovHighMetric17.A
  nr := SemenovHighMetric17.nr
  radius := SemenovHighMetric17.radius
  margin := SemenovHighMetric17.margin
  z := SemenovHighMetric17.z
  P := SemenovHighMetric17.P
  scale := SemenovHighMetric17.timeScale
  left := SemenovHighMetric17.leftTime
  right := SemenovHighMetric17.rightTime
  zLeft := SemenovHighMetric17.zl
  zRight := SemenovHighMetric17.zr
  pLeft := SemenovHighMetric17.pl
  pRight := SemenovHighMetric17.pr
  rb := SemenovHighMetric17.rbound
  fb := SemenovHighMetric17.fbound
  geometry := by
    convert SemenovHighMetric17.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric17.eta]
  cache_z := by intro j; simp only [SemenovHighMetric17.z,SemenovHighMetric17.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric17.cache_P
  symmetry := SemenovHighMetric17.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric17.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric17.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric17.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric17.replay.2.2.2.1
  force_squares := SemenovHighMetric17.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric17.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric17.force_bound i t hl hu
  whitened := SemenovHighMetric17.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (17 : Fin 22) j

def highPiece18 : RecoveryPiece true where
  zc := SemenovHighMetric18.zc
  pc := SemenovHighMetric18.pc
  wc := SemenovHighMetric18.wc
  A := SemenovHighMetric18.A
  nr := SemenovHighMetric18.nr
  radius := SemenovHighMetric18.radius
  margin := SemenovHighMetric18.margin
  z := SemenovHighMetric18.z
  P := SemenovHighMetric18.P
  scale := SemenovHighMetric18.timeScale
  left := SemenovHighMetric18.leftTime
  right := SemenovHighMetric18.rightTime
  zLeft := SemenovHighMetric18.zl
  zRight := SemenovHighMetric18.zr
  pLeft := SemenovHighMetric18.pl
  pRight := SemenovHighMetric18.pr
  rb := SemenovHighMetric18.rbound
  fb := SemenovHighMetric18.fbound
  geometry := by
    convert SemenovHighMetric18.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric18.eta]
  cache_z := by intro j; simp only [SemenovHighMetric18.z,SemenovHighMetric18.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric18.cache_P
  symmetry := SemenovHighMetric18.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric18.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric18.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric18.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric18.replay.2.2.2.1
  force_squares := SemenovHighMetric18.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric18.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric18.force_bound i t hl hu
  whitened := SemenovHighMetric18.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (18 : Fin 22) j

def highPiece19 : RecoveryPiece true where
  zc := SemenovHighMetric19.zc
  pc := SemenovHighMetric19.pc
  wc := SemenovHighMetric19.wc
  A := SemenovHighMetric19.A
  nr := SemenovHighMetric19.nr
  radius := SemenovHighMetric19.radius
  margin := SemenovHighMetric19.margin
  z := SemenovHighMetric19.z
  P := SemenovHighMetric19.P
  scale := SemenovHighMetric19.timeScale
  left := SemenovHighMetric19.leftTime
  right := SemenovHighMetric19.rightTime
  zLeft := SemenovHighMetric19.zl
  zRight := SemenovHighMetric19.zr
  pLeft := SemenovHighMetric19.pl
  pRight := SemenovHighMetric19.pr
  rb := SemenovHighMetric19.rbound
  fb := SemenovHighMetric19.fbound
  geometry := by
    convert SemenovHighMetric19.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric19.eta]
  cache_z := by intro j; simp only [SemenovHighMetric19.z,SemenovHighMetric19.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric19.cache_P
  symmetry := SemenovHighMetric19.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric19.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric19.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric19.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric19.replay.2.2.2.1
  force_squares := SemenovHighMetric19.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric19.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric19.force_bound i t hl hu
  whitened := SemenovHighMetric19.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (19 : Fin 22) j

def highPiece20 : RecoveryPiece true where
  zc := SemenovHighMetric20.zc
  pc := SemenovHighMetric20.pc
  wc := SemenovHighMetric20.wc
  A := SemenovHighMetric20.A
  nr := SemenovHighMetric20.nr
  radius := SemenovHighMetric20.radius
  margin := SemenovHighMetric20.margin
  z := SemenovHighMetric20.z
  P := SemenovHighMetric20.P
  scale := SemenovHighMetric20.timeScale
  left := SemenovHighMetric20.leftTime
  right := SemenovHighMetric20.rightTime
  zLeft := SemenovHighMetric20.zl
  zRight := SemenovHighMetric20.zr
  pLeft := SemenovHighMetric20.pl
  pRight := SemenovHighMetric20.pr
  rb := SemenovHighMetric20.rbound
  fb := SemenovHighMetric20.fbound
  geometry := by
    convert SemenovHighMetric20.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric20.eta]
  cache_z := by intro j; simp only [SemenovHighMetric20.z,SemenovHighMetric20.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric20.cache_P
  symmetry := SemenovHighMetric20.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric20.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric20.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric20.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric20.replay.2.2.2.1
  force_squares := SemenovHighMetric20.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric20.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric20.force_bound i t hl hu
  whitened := SemenovHighMetric20.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (20 : Fin 22) j

def highPiece21 : RecoveryPiece true where
  zc := SemenovHighMetric21.zc
  pc := SemenovHighMetric21.pc
  wc := SemenovHighMetric21.wc
  A := SemenovHighMetric21.A
  nr := SemenovHighMetric21.nr
  radius := SemenovHighMetric21.radius
  margin := SemenovHighMetric21.margin
  z := SemenovHighMetric21.z
  P := SemenovHighMetric21.P
  scale := SemenovHighMetric21.timeScale
  left := SemenovHighMetric21.leftTime
  right := SemenovHighMetric21.rightTime
  zLeft := SemenovHighMetric21.zl
  zRight := SemenovHighMetric21.zr
  pLeft := SemenovHighMetric21.pl
  pRight := SemenovHighMetric21.pr
  rb := SemenovHighMetric21.rbound
  fb := SemenovHighMetric21.fbound
  geometry := by
    convert SemenovHighMetric21.geometry using 1
    all_goals norm_num [recoveryEta,recoveryL,recoveryQ,recoveryH,SemenovHighMetric21.eta]
  cache_z := by intro j; simp only [SemenovHighMetric21.z,SemenovHighMetric21.zCache,cached_ofFn_value]
  cache_P := SemenovHighMetric21.cache_P
  symmetry := SemenovHighMetric21.symmetry_and_endpoints.1
  z_endpoints := SemenovHighMetric21.symmetry_and_endpoints.2.1
  p_endpoints := SemenovHighMetric21.symmetry_and_endpoints.2.2.1
  timing := SemenovHighMetric21.symmetry_and_endpoints.2.2.2
  residual_rows := SemenovHighMetric21.replay.2.2.2.1
  force_squares := SemenovHighMetric21.replay.2.2.2.2.1
  residual := fun t hl hu i j => SemenovHighMetric21.residual_bound i j t hl hu
  force := fun t hl hu i => SemenovHighMetric21.force_bound i t hl hu
  whitened := SemenovHighMetric21.whitened_eq
  capacity := fun j => SemenovCoverChecks.high_checks.2.2.2.2 (21 : Fin 22) j

def highPieces : Fin 22 → RecoveryPiece true := ![highPiece00,highPiece01,highPiece02,highPiece03,highPiece04,highPiece05,highPiece06,highPiece07,highPiece08,highPiece09,highPiece10,highPiece11,highPiece12,highPiece13,highPiece14,highPiece15,highPiece16,highPiece17,highPiece18,highPiece19,highPiece20,highPiece21]

end CompositionalMemory.Semenov.SemenovRecoveryPieces
