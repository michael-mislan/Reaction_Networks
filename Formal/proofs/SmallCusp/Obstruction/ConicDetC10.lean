import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC10 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 32 : ℚ), (-33 / 32 : ℚ), 0, (-33 / 32 : ℚ), (1 / 8 : ℚ)], ![(3 / 16 : ℚ), (-1 / 32 : ℚ), 0, (-33 / 16 : ℚ), (-3 / 32 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-13 / 12 : ℚ), 0, (-7 / 6 : ℚ), 0], ![(1 / 6 : ℚ), 0, 0, (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-2 / 7 : ℚ), (-10 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-16 / 7 : ℚ), (-4 / 7 : ℚ), (-9 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 6 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), (-1 / 3 : ℚ), (-31 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), (-2 / 3 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-9 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), 0, (-13 / 9 : ℚ), (-8 / 9 : ℚ), (-50 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-26 / 9 : ℚ), (-16 / 9 : ℚ), (-16 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (1 / 3 : ℚ), (-1 / 24 : ℚ), 0, (-29 / 24 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 24 : ℚ), (-17 / 8 : ℚ), (-1 / 24 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0, (-9 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, (-13 / 5 : ℚ), (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 7 : ℚ), 0, (-3 / 7 : ℚ), 0, -7], ![(-9 / 7 : ℚ), (-3 / 7 : ℚ), (-23 / 7 : ℚ), (-3 / 7 : ℚ), (-23 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), 0, (-8 / 17 : ℚ), 0, (-124 / 17 : ℚ)], ![(-24 / 17 : ℚ), 0, (-58 / 17 : ℚ), (-8 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0, -6], ![(-6 / 5 : ℚ), (-2 / 5 : ℚ), (-16 / 5 : ℚ), (-2 / 5 : ℚ), (-26 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-6 / 7 : ℚ), 0], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 22 : ℚ), (-15 / 11 : ℚ), (7 / 11 : ℚ), (-14 / 11 : ℚ), (-2 / 11 : ℚ)], ![(-9 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-30 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -3, -1, -1, (-1 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), -6, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 3 : ℚ), (-8 / 9 : ℚ)], ![0, 0, 0, (-20 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 2 : ℚ), (-1 / 2 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), -5, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-7 / 10 : ℚ), (3 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), -1, (-1 / 2 : ℚ), 0, 0], ![(1 / 5 : ℚ), 0, (-21 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 6 : ℚ), 0, (-11 / 6 : ℚ), (11 / 6 : ℚ)], ![(-11 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (11 / 6 : ℚ), (11 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 17 : ℚ), (-37 / 17 : ℚ), (-28 / 17 : ℚ), (23 / 17 : ℚ), (-1 / 17 : ℚ)], ![(25 / 17 : ℚ), (-1 / 17 : ℚ), (-74 / 17 : ℚ), (-22 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (1 / 4 : ℚ), (1 / 20 : ℚ), (-11 / 20 : ℚ), (-4 / 5 : ℚ)], ![(-7 / 20 : ℚ), 0, 0, (13 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 17 : ℚ), (-71 / 34 : ℚ), (-53 / 34 : ℚ), (43 / 34 : ℚ), (-1 / 34 : ℚ)], ![(47 / 34 : ℚ), (-1 / 17 : ℚ), (-71 / 17 : ℚ), (-41 / 34 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 20 : ℚ)], ![(-1 / 20 : ℚ), 0, (-43 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), 0], ![(1 / 2 : ℚ), 0, (-7 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (17 / 16 : ℚ), (3 / 16 : ℚ), (-31 / 16 : ℚ), (31 / 16 : ℚ)], ![(-31 / 16 : ℚ), 0, 0, 0, (31 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 10 : ℚ)], ![(3 / 10 : ℚ), 0, (-43 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ), (-16 / 5 : ℚ)], ![(-7 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-21 / 10 : ℚ), (-11 / 10 : ℚ), (3 / 10 : ℚ), (-1 / 10 : ℚ)], ![(1 / 2 : ℚ), 0, (-22 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), -2, (-14 / 9 : ℚ), (-1 / 9 : ℚ), (-35 / 9 : ℚ)], ![0, (-8 / 9 : ℚ), (-29 / 9 : ℚ), 0, (-17 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-81 / 20 : ℚ)], ![0, 0, (-43 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 22 : ℚ), (-51 / 22 : ℚ), (-49 / 22 : ℚ), (17 / 22 : ℚ), 0], ![0, (-2 / 11 : ℚ), (-51 / 11 : ℚ), (21 / 22 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, 0, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 12 : ℚ), (-9 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 1, (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 2 : ℚ), (-7 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![0, (-1 / 3 : ℚ), -5, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-7 / 3 : ℚ), -1, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, -5, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 19 : ℚ), (-62 / 19 : ℚ), (-44 / 19 : ℚ), (-8 / 19 : ℚ), (20 / 19 : ℚ)], ![(-8 / 19 : ℚ), (-8 / 19 : ℚ), (-124 / 19 : ℚ), 0, (24 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-12 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, 0, (-28 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-11 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, (-24 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 11 : ℚ), (-49 / 22 : ℚ), (-15 / 22 : ℚ), 0, (-1 / 22 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 11 : ℚ), (-49 / 11 : ℚ), (1 / 22 : ℚ), (1 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .xy), (.xx, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 5 : ℚ)], ![0, 0, 0, (-3 / 5 : ℚ), (-7 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-7 / 12 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, (-3 / 5 : ℚ), (-7 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-5 / 2 : ℚ), (-4 / 3 : ℚ), (-13 / 6 : ℚ), (-1 / 6 : ℚ)], ![(5 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-29 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-3 / 4 : ℚ), (-7 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 2 : ℚ)], ![0, 0, 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xx), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 3 : ℚ), -2, -2, 0], ![(-2 / 3 : ℚ), 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xy), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0, -2], ![(1 / 4 : ℚ), 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .yy), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, 0, (-3 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (2 / 5 : ℚ), (-8 / 5 : ℚ), (2 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, -1, -1, 0], ![0, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), 0], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, (-3 / 4 : ℚ), (-1 / 4 : ℚ)], ![(1 / 4 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, 0, (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), -2, 0, -2, 0], ![(1 / 3 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-4 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, 0, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-1 / 3 : ℚ), (-19 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 3 : ℚ), (-1 / 3 : ℚ), -3]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-3 / 2 : ℚ), 0, -2, (-1 / 2 : ℚ)], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (8 / 9 : ℚ), (-7 / 3 : ℚ), (1 / 12 : ℚ), (-41 / 36 : ℚ)], ![(-35 / 36 : ℚ), (-1 / 12 : ℚ), (-55 / 12 : ℚ), 0, (31 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (1 / 10 : ℚ), (-12 / 5 : ℚ), (1 / 10 : ℚ), (-7 / 5 : ℚ)], ![(-3 / 10 : ℚ), 0, (-47 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), (-13 / 10 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-12 / 5 : ℚ), (-3 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-20 / 7 : ℚ), 0, -6], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-38 / 7 : ℚ), (-2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (8 / 17 : ℚ), (-66 / 17 : ℚ), (8 / 17 : ℚ), (-128 / 17 : ℚ)], ![(-24 / 17 : ℚ), 0, (-124 / 17 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (7 / 24 : ℚ), (-1 / 24 : ℚ), 0, (-7 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 24 : ℚ), (-25 / 12 : ℚ), (-1 / 24 : ℚ), (29 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-12 / 5 : ℚ), (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-2 / 7 : ℚ), 0, -6], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-18 / 7 : ℚ), (-2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, (-13 / 2 : ℚ)], ![-1, 0, -3, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-5 / 2 : ℚ), (-1 / 2 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, 0, 0, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-4 / 5 : ℚ), -1, (1 / 5 : ℚ), (2 / 5 : ℚ)], ![(3 / 5 : ℚ), 0, (-6 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, (-7 / 6 : ℚ), 0, 0], ![(1 / 3 : ℚ), 0, (-7 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0], ![0, (-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-35 / 16 : ℚ), (-13 / 8 : ℚ), (11 / 8 : ℚ), (-1 / 16 : ℚ)], ![(3 / 2 : ℚ), (-1 / 16 : ℚ), (-35 / 16 : ℚ), (-21 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-3 / 10 : ℚ), (3 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (-59 / 28 : ℚ), (-59 / 28 : ℚ), (37 / 28 : ℚ), 0], ![(41 / 28 : ℚ), (-1 / 14 : ℚ), (-59 / 28 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-5 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), 0], ![0, 0, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0], ![0, 0, (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-11 / 5 : ℚ), (-6 / 5 : ℚ), (3 / 5 : ℚ), (-1 / 5 : ℚ)], ![(4 / 5 : ℚ), 0, (-12 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), (-8 / 5 : ℚ), (-14 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 8 : ℚ), (-33 / 16 : ℚ), (-35 / 16 : ℚ), (5 / 16 : ℚ), 0], ![(7 / 16 : ℚ), 0, (-35 / 16 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, -1], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-7 / 2 : ℚ)], ![0, (-1 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-4 / 3 : ℚ), (-5 / 3 : ℚ), 0, (-13 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -5], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (2 / 3 : ℚ), -5]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-9 / 4 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-7 / 12 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-3 / 4 : ℚ), (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-3 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-11 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-16 / 5 : ℚ), (-16 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (-16 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-8 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, 0, (-12 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 5 : ℚ), (-12 / 5 : ℚ), (-16 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![0, 0, (-16 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-4 / 5 : ℚ), (-3 / 10 : ℚ), (-3 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, 0, 0, (-1 / 4 : ℚ), (3 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), 0], ![0, 0, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-9 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-1 / 4 : ℚ)], ![0, 0, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-21 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (1 / 4 : ℚ)], ![(9 / 20 : ℚ), 0, 0, 0, (-3 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-15 / 14 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), 0], ![0, 0, 0, 0, (-3 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-13 / 12 : ℚ), 0, 0, -1], ![(1 / 6 : ℚ), 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ)], ![(1 / 2 : ℚ), 0, 0, 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, 0, -1], ![(1 / 6 : ℚ), 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 1, 0], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .yy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, 0, (3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, -1, 0, 0], ![(1 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0], ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, (9 / 8 : ℚ), (-1 / 8 : ℚ)], ![(11 / 8 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ)], ![0, 0, 0, (3 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, (9 / 8 : ℚ), (-1 / 16 : ℚ)], ![(11 / 8 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, (1 / 4 : ℚ), 0], ![(1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, -1, 0, 0], ![(1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -1, -1, 0, 0], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 4 : ℚ), 0, (1 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-1 / 4 : ℚ)], ![(1 / 4 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-1 / 4 : ℚ)], ![(1 / 2 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, (-3 / 8 : ℚ), (-1 / 8 : ℚ)], ![(1 / 8 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, 0, (-3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, 0, -1, 0], ![(1 / 3 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-7 / 6 : ℚ), (-1 / 12 : ℚ), 0, (5 / 12 : ℚ)], ![(7 / 12 : ℚ), (-1 / 12 : ℚ), 0, (1 / 12 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-8 / 5 : ℚ), (-13 / 10 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ), (-12 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (-7 / 6 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), (-11 / 10 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), -1, 1, 0], ![-1, (-1 / 3 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ), (3 / 10 : ℚ)], ![(1 / 2 : ℚ), 0, 0, (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-4 / 3 : ℚ), -1, -1], ![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), (-1 / 6 : ℚ), 0], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-7 / 6 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 9 : ℚ), (-5 / 9 : ℚ), (5 / 9 : ℚ)], ![(-5 / 9 : ℚ), (-2 / 9 : ℚ), (-13 / 9 : ℚ), (5 / 9 : ℚ), (5 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), 0, (-8 / 3 : ℚ), (-7 / 8 : ℚ), (-103 / 24 : ℚ)], ![(-1 / 24 : ℚ), (-1 / 24 : ℚ), (-13 / 12 : ℚ), (11 / 12 : ℚ), (-17 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (-1 / 20 : ℚ), (3 / 20 : ℚ), (-1 / 20 : ℚ)], ![(1 / 4 : ℚ), 0, 0, (-1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 8 : ℚ), (-7 / 8 : ℚ), (1 / 8 : ℚ), 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, 0, (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, -1], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 8 : ℚ), 0, (1 / 4 : ℚ)], ![(-5 / 16 : ℚ), (-1 / 16 : ℚ), (-9 / 8 : ℚ), (3 / 16 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 5 : ℚ), 0, (-47 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), (9 / 10 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, (-19 / 8 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 8 : ℚ), (3 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 5 : ℚ), 0, (-87 / 20 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), (9 / 10 : ℚ), (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-6 / 5 : ℚ), (1 / 2 : ℚ), (-47 / 10 : ℚ)], ![(-7 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), (1 / 2 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-5 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, 0, 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-9 / 8 : ℚ), (-1 / 12 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), (-13 / 12 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, 0], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 4 : ℚ), (-9 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), (3 / 2 : ℚ), 0], ![(-3 / 2 : ℚ), (-1 / 2 : ℚ), -3, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-9 / 10 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)], ![(3 / 10 : ℚ), 0, (-3 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)], ![(5 / 12 : ℚ), 0, 0, (-1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-12 / 5 : ℚ), (3 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-8 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-37 / 12 : ℚ), (-3 / 4 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), (5 / 6 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-4 / 5 : ℚ), (-1 / 4 : ℚ), (-1 / 10 : ℚ), (-19 / 40 : ℚ)], ![0, 0, (-9 / 20 : ℚ), (3 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-17 / 8 : ℚ), (25 / 72 : ℚ), (11 / 8 : ℚ), (-1 / 24 : ℚ)], ![(37 / 24 : ℚ), (-1 / 12 : ℚ), (7 / 9 : ℚ), (-31 / 24 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 8 : ℚ), (-1 / 4 : ℚ), 0], ![(-1 / 8 : ℚ), 0, (-17 / 8 : ℚ), 0, (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 1, -1], ![1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, -1], ![(-1 / 4 : ℚ), 0, (-9 / 4 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, (1 / 4 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 4 : ℚ), (-5 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 5 : ℚ), 0, (-47 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 5 : ℚ), (9 / 10 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-5 / 2 : ℚ)], ![(-1 / 3 : ℚ), 0, (-7 / 3 : ℚ), (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-10 / 7 : ℚ), 0, -5], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-18 / 7 : ℚ), (5 / 7 : ℚ), (-34 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-10 / 3 : ℚ), (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-3 / 4 : ℚ), (-1 / 12 : ℚ), (-61 / 12 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-10 / 9 : ℚ), (-1 / 9 : ℚ), (-14 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, 0, 0, (-16 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, -1, (3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), -1, -1], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 5 : ℚ), 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (3 / 10 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, 0], ![0, (-1 / 3 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-7 / 12 : ℚ), (-3 / 4 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-13 / 12 : ℚ), (5 / 6 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-3 / 5 : ℚ), (-13 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-6 / 5 : ℚ), (4 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 12 : ℚ), (-1 / 4 : ℚ), (-103 / 24 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-13 / 12 : ℚ), (1 / 3 : ℚ), (-17 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![(1 / 8 : ℚ), 0, (-7 / 8 : ℚ), 0, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-17 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 12 : ℚ), (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-3 / 4 : ℚ), (-1 / 12 : ℚ), (-7 / 4 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-11 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), (-3 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![(2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), 0, (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 7 : ℚ), (-3 / 7 : ℚ), 0, (-2 / 7 : ℚ)], ![0, (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-12 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (13 / 10 : ℚ), (13 / 10 : ℚ), (-1 / 10 : ℚ)], ![(3 / 2 : ℚ), 0, (-6 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0], ![(3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-41 / 20 : ℚ), (5 / 4 : ℚ), (5 / 4 : ℚ), (-1 / 20 : ℚ)], ![(29 / 20 : ℚ), 0, (-23 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -3, 2, 2, 0], ![(7 / 3 : ℚ), 0, -2, 2, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, -4], ![(1 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-25 / 12 : ℚ), (13 / 12 : ℚ), (13 / 12 : ℚ), (-1 / 6 : ℚ)], ![(17 / 12 : ℚ), 0, (-13 / 12 : ℚ), (13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 13 : ℚ), 0, (-66 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (9 / 13 : ℚ), (8 / 13 : ℚ), (-32 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, (-47 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ), (3 / 5 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 7 : ℚ), (12 / 7 : ℚ), (-12 / 7 : ℚ), (-1 / 7 : ℚ)], ![(12 / 7 : ℚ), (-1 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-12 / 5 : ℚ), (29 / 15 : ℚ), (-29 / 15 : ℚ), 0], ![(29 / 15 : ℚ), (-4 / 15 : ℚ), (-29 / 15 : ℚ), (-29 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (13 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![(3 / 2 : ℚ), 0, (-6 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (3 / 2 : ℚ), (-1 / 12 : ℚ), 0], ![(5 / 3 : ℚ), (-1 / 12 : ℚ), (-17 / 12 : ℚ), 0, (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (3 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-41 / 20 : ℚ), (5 / 4 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ)], ![(29 / 20 : ℚ), 0, (-23 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (3 / 2 : ℚ), (-1 / 24 : ℚ), 0], ![(5 / 3 : ℚ), (-1 / 12 : ℚ), (-17 / 12 : ℚ), 0, (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 8 : ℚ), (11 / 8 : ℚ), 0, (-1 / 8 : ℚ)], ![(3 / 2 : ℚ), 0, 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, 0, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-33 / 16 : ℚ), (21 / 16 : ℚ), 0, (-1 / 16 : ℚ)], ![(23 / 16 : ℚ), 0, 0, (-19 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 4 : ℚ), (3 / 2 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ)], ![(3 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 4 : ℚ), (7 / 4 : ℚ), (-7 / 4 : ℚ), 0], ![(7 / 4 : ℚ), 0, 0, (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-17 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, 1, -1, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, -4], ![(1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-9 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, 1, -1, (-17 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), (7 / 6 : ℚ), (-17 / 3 : ℚ)], ![(-4 / 3 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (7 / 6 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, 0, 0, -4], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-2 / 3 : ℚ), (-1 / 12 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, -3], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, -3]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-27 / 5 : ℚ), (-47 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-8 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-27 / 5 : ℚ), (-13 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-23 / 5 : ℚ), (-12 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-3 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-6 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-13 / 5 : ℚ), (-8 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), (-8 / 5 : ℚ), 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (2 / 5 : ℚ), (-14 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-11 / 5 : ℚ), (-8 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, 0, (-8 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 10 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-17 / 10 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 2 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-23 / 16 : ℚ), 0, 0], ![(-3 / 16 : ℚ), (-3 / 16 : ℚ), (-5 / 2 : ℚ), (-3 / 16 : ℚ), (-3 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 8 : ℚ), 0, 0, 0], ![(3 / 8 : ℚ), (-3 / 4 : ℚ), (-21 / 16 : ℚ), (-3 / 4 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-17 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-32 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), -6]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 10 : ℚ), 0, (-1 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-33 / 13 : ℚ), 0, 0, (-2 / 13 : ℚ)], ![(1 / 13 : ℚ), (-17 / 13 : ℚ), (1 / 13 : ℚ), (-67 / 26 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, 0, (-7 / 5 : ℚ)], ![(3 / 5 : ℚ), (-8 / 5 : ℚ), 0, (-17 / 5 : ℚ), (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 8 : ℚ), 0, (-3 / 4 : ℚ), 0], ![(3 / 8 : ℚ), (-3 / 4 : ℚ), (-15 / 8 : ℚ), (-15 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-33 / 13 : ℚ), 0, (-2 / 13 : ℚ), 0], ![(1 / 13 : ℚ), (-17 / 13 : ℚ), (-67 / 26 : ℚ), -2, (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (-3 / 4 : ℚ), 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), -2, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), (-4 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-26 / 5 : ℚ), 0, (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-14 / 5 : ℚ), (-27 / 5 : ℚ), (-43 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 11 : ℚ), 0, 0], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, (-4 / 3 : ℚ)], ![(1 / 6 : ℚ), (-4 / 3 : ℚ), 0, (-17 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, -2], ![(1 / 2 : ℚ), (-3 / 2 : ℚ), 0, -4, -2]] }
]

theorem conicDetC10_checked : conicDetC10.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
