import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC15 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, 0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), 0, (-20 / 9 : ℚ), 0, (-8 / 9 : ℚ)], ![(4 / 9 : ℚ), 0, (-20 / 9 : ℚ), (8 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), 0, 0], ![0, 0, (-1 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, 0, (-8 / 5 : ℚ), (4 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-5 / 8 : ℚ), 0, 0], ![(1 / 8 : ℚ), 0, (-5 / 8 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-28 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-54 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (21 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-29 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-20 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-36 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-38 / 7 : ℚ), (-18 / 7 : ℚ), (-2 / 7 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-10 / 3 : ℚ), (-4 / 9 : ℚ), 0, (-56 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-56 / 9 : ℚ), (-26 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -3, 2, (1 / 4 : ℚ), -2], ![-2, (-23 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -3, 3, (1 / 3 : ℚ), 0], ![-3, -6, 0, 0, 2]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-10 / 3 : ℚ), 2, (1 / 3 : ℚ), (-19 / 3 : ℚ)], ![(-7 / 3 : ℚ), (-19 / 3 : ℚ), (-1 / 3 : ℚ), 0, -3]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-10 / 3 : ℚ), 3, (1 / 3 : ℚ), (-23 / 3 : ℚ)], ![(-11 / 3 : ℚ), (-19 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-25 / 11 : ℚ), 0, (-41 / 33 : ℚ), (-8 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-49 / 11 : ℚ), (-1 / 11 : ℚ), (4 / 3 : ℚ), (12 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-4 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-9 / 2 : ℚ), 0, (8 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 3 : ℚ), 0, (-2 / 9 : ℚ), 0], ![(-1 / 9 : ℚ), (-41 / 9 : ℚ), (-1 / 9 : ℚ), (32 / 9 : ℚ), (13 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 3 : ℚ), 0, (-5 / 3 : ℚ), (5 / 3 : ℚ)], ![(-5 / 3 : ℚ), (-16 / 3 : ℚ), (-1 / 3 : ℚ), (5 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 28 : ℚ), (-59 / 28 : ℚ), 0, (-1 / 7 : ℚ), (-67 / 28 : ℚ)], ![(-1 / 14 : ℚ), (-117 / 28 : ℚ), (-1 / 28 : ℚ), (85 / 28 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-74 / 25 : ℚ), (6 / 25 : ℚ), (-47 / 25 : ℚ), (-96 / 25 : ℚ)], ![(-18 / 25 : ℚ), (-142 / 25 : ℚ), 0, (53 / 25 : ℚ), (98 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-9 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-9 / 2 : ℚ), 0, (8 / 3 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-9 / 4 : ℚ), 0, (-5 / 8 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-35 / 8 : ℚ), 0, (5 / 4 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-25 / 11 : ℚ), 0, (-8 / 11 : ℚ), 0], ![(-1 / 11 : ℚ), (-49 / 11 : ℚ), (-1 / 11 : ℚ), (12 / 11 : ℚ), (15 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, (-3 / 2 : ℚ), (3 / 2 : ℚ)], ![(-3 / 2 : ℚ), -5, (-1 / 4 : ℚ), 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-17 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-25 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-33 / 7 : ℚ), (-1 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-26 / 11 : ℚ), (1 / 11 : ℚ), (-20 / 11 : ℚ), (-51 / 11 : ℚ)], ![(-19 / 11 : ℚ), (-51 / 11 : ℚ), 0, (1 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-16 / 7 : ℚ), 0, (-5 / 7 : ℚ), (-31 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-31 / 7 : ℚ), 0, (8 / 7 : ℚ), (-31 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-19 / 4 : ℚ), 0, (7 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-9 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-11 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-35 / 8 : ℚ), 0, (-5 / 4 : ℚ), (9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-13 / 6 : ℚ), 0, (-7 / 6 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-17 / 4 : ℚ), 0, (-7 / 6 : ℚ), (29 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), (1 / 6 : ℚ), 0, (3 / 2 : ℚ)], ![(-5 / 3 : ℚ), -5, 0, (3 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, 0, (-21 / 5 : ℚ)], ![(-1 / 5 : ℚ), -5, (-1 / 5 : ℚ), (9 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-43 / 20 : ℚ), 0, 0, (-7 / 10 : ℚ)], ![(-1 / 20 : ℚ), (-17 / 4 : ℚ), (-1 / 20 : ℚ), (6 / 5 : ℚ), (143 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, (-19 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-19 / 4 : ℚ), 0, (7 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), 0, (1 / 2 : ℚ), (-53 / 12 : ℚ)], ![(-2 / 3 : ℚ), (-53 / 12 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-7 / 3 : ℚ), 0, (1 / 2 : ℚ), (-41 / 9 : ℚ)], ![(-13 / 18 : ℚ), (-41 / 9 : ℚ), (-1 / 9 : ℚ), (7 / 18 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 15 : ℚ), (-34 / 15 : ℚ), (1 / 15 : ℚ), (-71 / 15 : ℚ), (-14 / 3 : ℚ)], ![(-7 / 3 : ℚ), (-67 / 15 : ℚ), 0, (1 / 15 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, -3, (-9 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-9 / 2 : ℚ), 0, (5 / 6 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-5 / 2 : ℚ), (1 / 8 : ℚ), (-43 / 8 : ℚ), (-11 / 4 : ℚ)], ![(-21 / 8 : ℚ), (-39 / 8 : ℚ), 0, (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-14 / 5 : ℚ), 0, (-16 / 5 : ℚ), (-26 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-26 / 5 : ℚ), 0, (22 / 5 : ℚ), (-26 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (11 / 8 : ℚ), 0, (-11 / 8 : ℚ)], ![(-11 / 8 : ℚ), (-9 / 4 : ℚ), 0, (-5 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 6 : ℚ), (-31 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-3 / 2 : ℚ), (-7 / 6 : ℚ), -1, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 2 : ℚ), 0, (-37 / 8 : ℚ)], ![(-5 / 8 : ℚ), (-9 / 4 : ℚ), 0, (-13 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 3 : ℚ), (-3 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (11 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), 0, (-7 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-11 / 5 : ℚ), 0, (3 / 2 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), (7 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), (3 / 2 : ℚ)], ![(-3 / 2 : ℚ), (-5 / 2 : ℚ), (-1 / 2 : ℚ), (3 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), 0, (-15 / 11 : ℚ), (-48 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (16 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ), (-54 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (21 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-9 / 5 : ℚ), (-23 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-12 / 5 : ℚ), 0, 2, (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-7 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-12 / 5 : ℚ), 0, (1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-11 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), (4 / 3 : ℚ)], ![(-4 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 3 : ℚ), 0, (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ), (-13 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-7 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-29 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-23 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-12 / 5 : ℚ), 0, (1 / 5 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), 0, (7 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-9 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-4 / 3 : ℚ), (-29 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-7 / 3 : ℚ), 0, (-4 / 3 : ℚ), 2]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-11 / 5 : ℚ), (-1 / 5 : ℚ), (2 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-40 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-18 / 7 : ℚ), (-4 / 7 : ℚ), (8 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -6], ![(-2 / 3 : ℚ), (-8 / 3 : ℚ), 0, (4 / 3 : ℚ), -6]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), 0, (1 / 2 : ℚ), (-48 / 11 : ℚ)], ![(-15 / 22 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (9 / 22 : ℚ), (-47 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-1 / 9 : ℚ), 0, (1 / 2 : ℚ), (-41 / 9 : ℚ)], ![(-13 / 18 : ℚ), (-20 / 9 : ℚ), (-1 / 9 : ℚ), (7 / 18 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-54 / 11 : ℚ), (-52 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (2 / 11 : ℚ), (-14 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), 0, (-32 / 7 : ℚ), (-31 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-16 / 7 : ℚ), 0, (-5 / 7 : ℚ), (-31 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, 0, (-5 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-48 / 7 : ℚ), (-40 / 7 : ℚ)], ![(-8 / 7 : ℚ), (-22 / 7 : ℚ), 0, (4 / 7 : ℚ), (-40 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 2, 0, -2, (-3 / 2 : ℚ)], ![-2, 0, 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 2, (1 / 2 : ℚ), -2, (-11 / 2 : ℚ)], ![-2, 0, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![0, 0, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 2, 0, -2, (-9 / 2 : ℚ)], ![-2, 0, 0, 0, (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 4 : ℚ), 2, 0, (-3 / 2 : ℚ), (-13 / 2 : ℚ)], ![-6, (-1 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (7 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-23 / 3 : ℚ)], ![(-8 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-37 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-17 / 40 : ℚ), (-13 / 8 : ℚ), (-21 / 20 : ℚ), (-9 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), 0, (-7 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0], ![(1 / 6 : ℚ), (-1 / 3 : ℚ), (-5 / 2 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 12 : ℚ), 2, (1 / 12 : ℚ), (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-25 / 12 : ℚ), (-1 / 12 : ℚ), 0, (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (13 / 6 : ℚ), (1 / 6 : ℚ), (2 / 3 : ℚ), (-29 / 6 : ℚ)], ![(-7 / 3 : ℚ), 0, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (12 / 5 : ℚ), (2 / 5 : ℚ), -6, -6], ![(-14 / 5 : ℚ), 0, 0, 0, (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 5 : ℚ), 2, 0, (-34 / 5 : ℚ), (-26 / 5 : ℚ)], ![-6, (-2 / 5 : ℚ), 0, (-16 / 5 : ℚ), (-26 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, 0, -3, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (7 / 3 : ℚ), 0, (-17 / 3 : ℚ), -5], ![(-8 / 3 : ℚ), 0, 0, 0, -5]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 4 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), (6 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0], ![0, (-4 / 5 : ℚ), (6 / 5 : ℚ), 0, (12 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), (6 / 5 : ℚ), 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, 2, (-4 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (3 / 2 : ℚ), (3 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (3 / 2 : ℚ), (3 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 5 : ℚ), 0, 0, (-4 / 5 : ℚ)], ![0, (-8 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ), (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (1 / 2 : ℚ), (1 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-12 / 11 : ℚ), (12 / 11 : ℚ), (4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-8 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, 2, 0, (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-12 / 11 : ℚ), (12 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (-4 / 5 : ℚ), (6 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (2 / 5 : ℚ), 0], ![0, (-4 / 5 : ℚ), (6 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0], ![0, (-4 / 5 : ℚ), (2 / 5 : ℚ), 0, (12 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), (2 / 5 : ℚ), 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, (2 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 5 : ℚ), 0, (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), (6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), (2 / 5 : ℚ), (4 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-8 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (-7 / 6 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 2 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (-4 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), 0], ![0, (-4 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0, (9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0, (17 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ), -1], ![(-1 / 2 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, (1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, -1, (1 / 2 : ℚ), (-1 / 2 : ℚ), (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, 0, (-1 / 2 : ℚ), (-5 / 2 : ℚ)], ![0, -1, 0, 4, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, 0, 0, (1 / 2 : ℚ)], ![0, -1, 0, (5 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, 0, -4, (-1 / 2 : ℚ)], ![0, -1, 0, (1 / 2 : ℚ), 2]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0], ![0, (-4 / 3 : ℚ), 0, 4, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), -1, -1, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, 0], ![(1 / 3 : ℚ), -1, (-5 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ)], ![(2 / 5 : ℚ), -2, 0, (4 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-5 / 12 : ℚ), (-5 / 12 : ℚ), 0, 0], ![(1 / 12 : ℚ), (-7 / 12 : ℚ), (-7 / 12 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ), 0, (4 / 7 : ℚ)], ![0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), (2 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-5 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), 0, 0, (-20 / 7 : ℚ), (-12 / 7 : ℚ)], ![(-8 / 7 : ℚ), 0, 0, (4 / 7 : ℚ), (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![0, (1 / 5 : ℚ), 0, (-2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (1 / 5 : ℚ), 0, (-2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![0, (1 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, -1, 0], ![(1 / 6 : ℚ), 0, 0, -1, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, -1, 0], ![(1 / 6 : ℚ), 0, 0, -1, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, -1, 0], ![(1 / 6 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, (-13 / 6 : ℚ)], ![(-1 / 3 : ℚ), 0, -1, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, (-13 / 6 : ℚ)], ![(-1 / 3 : ℚ), 0, -1, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, -2], ![(-1 / 3 : ℚ), 0, -1, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, 0, (-5 / 2 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), (-1 / 8 : ℚ), 0, 0], ![(1 / 8 : ℚ), 0, 0, (-9 / 8 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ)], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -1, 1, 0, -2], ![-1, 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), 0, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), 0, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 3 : ℚ), 0, (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0, -2], ![(-1 / 6 : ℚ), (2 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (2 / 3 : ℚ), 0, 0, (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (2 / 3 : ℚ), 0, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 10 : ℚ), 0, (-3 / 10 : ℚ), 0], ![(1 / 10 : ℚ), (1 / 5 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0], ![0, (1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, (1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0], ![0, (1 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, (-3 / 2 : ℚ), 0], ![0, 0, (1 / 4 : ℚ), (-3 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-4 / 3 : ℚ), 0], ![(1 / 12 : ℚ), 0, (1 / 6 : ℚ), (-4 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), 0, -3], ![(-1 / 2 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-11 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-24 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-11 / 7 : ℚ), (-11 / 7 : ℚ), 0, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![0, 0, 0, -1, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![0, 0, 0, -1, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-6 / 5 : ℚ), 1, 0, (-27 / 10 : ℚ)], ![(-11 / 10 : ℚ), (-6 / 5 : ℚ), (-1 / 10 : ℚ), 0, (-13 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 0, (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), 0], ![(1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)], ![(1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![(1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, (1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![0, 0, (1 / 2 : ℚ), (-1 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, (1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, 0, (1 / 2 : ℚ), (-1 / 2 : ℚ), (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 8 : ℚ), 0, (-3 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), 0, (-10 / 9 : ℚ), 0, (-4 / 9 : ℚ)], ![(2 / 9 : ℚ), 0, (-10 / 9 : ℚ), (4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -1, 0, 0], ![0, 0, -1, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-4 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-4 / 7 : ℚ), 0], ![0, 0, (-8 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-10 / 7 : ℚ), (-1 / 7 : ℚ), 0, (-18 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-19 / 7 : ℚ), (-9 / 7 : ℚ), (-1 / 7 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-5 / 3 : ℚ), (-2 / 9 : ℚ), 0, (-28 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-28 / 9 : ℚ), (-13 / 9 : ℚ), (-2 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![0, 0, 0, -1, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![0, 0, 0, -1, (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 12 : ℚ), (-4 / 3 : ℚ), 1, (1 / 12 : ℚ), (-31 / 12 : ℚ)], ![(-13 / 12 : ℚ), (-31 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-5 / 3 : ℚ), (3 / 2 : ℚ), (1 / 6 : ℚ), (-23 / 6 : ℚ)], ![(-11 / 6 : ℚ), (-19 / 6 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-8 / 5 : ℚ)], ![0, -2, 0, 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-1 / 2 : ℚ)], ![0, -2, 0, 0, (13 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-5 / 2 : ℚ)], ![0, -2, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-5 / 3 : ℚ)], ![0, -2, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, -2], ![0, -2, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-5 / 2 : ℚ)], ![0, -2, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0, (-3 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), 0, 0, (13 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-5 / 4 : ℚ)], ![(-1 / 8 : ℚ), -2, 0, 0, (5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-3 / 8 : ℚ)], ![(-1 / 8 : ℚ), -2, 0, 0, (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-9 / 4 : ℚ)], ![(-1 / 4 : ℚ), -2, 0, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 30 : ℚ), (-17 / 15 : ℚ), (1 / 30 : ℚ), (-71 / 30 : ℚ), (-7 / 3 : ℚ)], ![(-7 / 6 : ℚ), (-67 / 30 : ℚ), 0, (1 / 30 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-7 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-9 / 4 : ℚ)], ![(-1 / 6 : ℚ), (-9 / 4 : ℚ), 0, (5 / 12 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-5 / 4 : ℚ), (1 / 16 : ℚ), (-43 / 16 : ℚ), (-11 / 8 : ℚ)], ![(-21 / 16 : ℚ), (-39 / 16 : ℚ), 0, (1 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-7 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-13 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-13 / 5 : ℚ), 0, (11 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 13 : ℚ), 0, 0], ![(2 / 13 : ℚ), (2 / 13 : ℚ), (-4 / 13 : ℚ), (-24 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 12 : ℚ), (-31 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-3 / 4 : ℚ), (-7 / 12 : ℚ), (-1 / 2 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (5 / 4 : ℚ), (1 / 4 : ℚ), (-15 / 4 : ℚ)], ![(-3 / 2 : ℚ), (-7 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-9 / 4 : ℚ)], ![0, -1, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![0, -1, 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![0, -1, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-9 / 4 : ℚ)], ![0, -1, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![0, -1, 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![0, -1, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, (-10 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (-11 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), 0, -3]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (-1 / 22 : ℚ), 0, (-49 / 22 : ℚ), (-24 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-12 / 11 : ℚ), (-1 / 22 : ℚ), (1 / 22 : ℚ), (-7 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (-1 / 14 : ℚ), 0, (-16 / 7 : ℚ), (-31 / 14 : ℚ)], ![(-1 / 7 : ℚ), (-8 / 7 : ℚ), 0, (-5 / 14 : ℚ), (-31 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-17 / 6 : ℚ), (-3 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-24 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-11 / 7 : ℚ), 0, (2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-1 / 2 : ℚ), (4 / 3 : ℚ), (-4 / 3 : ℚ), (-2 / 3 : ℚ)], ![(1 / 3 : ℚ), (-1 / 6 : ℚ), (4 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 1, 0, 0, -4], ![(-7 / 6 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 14 : ℚ), (-25 / 14 : ℚ)], ![(-1 / 14 : ℚ), (-11 / 28 : ℚ), (-15 / 14 : ℚ), (-19 / 28 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 0, (-9 / 4 : ℚ)], ![(-1 / 3 : ℚ), (-5 / 6 : ℚ), (-5 / 6 : ℚ), 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 5 : ℚ), (-7 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (5 / 4 : ℚ), 0, (-13 / 4 : ℚ), (-7 / 4 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 10 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (6 / 5 : ℚ), (1 / 5 : ℚ), -3, -3], ![(-7 / 5 : ℚ), 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 5 : ℚ), 1, 0, (-17 / 5 : ℚ), (-13 / 5 : ℚ)], ![-3, (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (7 / 6 : ℚ), 0, (-17 / 6 : ℚ), (-5 / 2 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![(2 / 3 : ℚ), -1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![1, -1, 1, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![(1 / 3 : ℚ), -1, 1, (-13 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![(1 / 2 : ℚ), -2, 2, (-9 / 2 : ℚ), (1 / 2 : ℚ)]] }
]

theorem conicDetC15_checked : conicDetC15.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
