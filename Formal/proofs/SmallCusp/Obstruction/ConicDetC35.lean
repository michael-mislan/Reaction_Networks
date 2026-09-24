import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC35 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), (1 / 6 : ℚ), 0, (-15 / 4 : ℚ), (-11 / 6 : ℚ)], ![(-1 / 2 : ℚ), -4, 0, (-15 / 4 : ℚ), (-11 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 7 : ℚ), 0, (-16 / 7 : ℚ), (-16 / 7 : ℚ), (1 / 2 : ℚ)], ![(-8 / 7 : ℚ), 0, (-32 / 7 : ℚ), (-17 / 7 : ℚ), (-5 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 20 : ℚ), 0, (-21 / 10 : ℚ), (-21 / 10 : ℚ), 1], ![(-37 / 20 : ℚ), 0, (-21 / 5 : ℚ), (-43 / 20 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 2 : ℚ)], ![0, (-9 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(9 / 4 : ℚ), (-41 / 16 : ℚ), 0, (3 / 16 : ℚ), (3 / 16 : ℚ)], ![0, (-41 / 8 : ℚ), 0, 0, (17 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, (-11 / 4 : ℚ), (-11 / 4 : ℚ), (-1 / 4 : ℚ)], ![(-9 / 8 : ℚ), 0, (-11 / 2 : ℚ), (-25 / 8 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (-8 / 3 : ℚ), (-2 / 3 : ℚ), 0, -6], ![0, (-16 / 3 : ℚ), (-4 / 3 : ℚ), 0, -6]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 5 : ℚ), (31 / 20 : ℚ), (-43 / 20 : ℚ), (69 / 20 : ℚ), 0], ![(-43 / 20 : ℚ), (-12 / 5 : ℚ), (-43 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 4 : ℚ), (23 / 16 : ℚ), (-35 / 16 : ℚ), (25 / 16 : ℚ), 0], ![(-35 / 16 : ℚ), (-5 / 2 : ℚ), (-35 / 16 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (-13 / 2 : ℚ)], ![0, (1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (-13 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 14 : ℚ), 0, (-8 / 7 : ℚ), 0, (-27 / 14 : ℚ)], ![(-8 / 7 : ℚ), (-47 / 28 : ℚ), (-8 / 7 : ℚ), 0, (-27 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-24 / 5 : ℚ), 0, (-13 / 5 : ℚ), (2 / 5 : ℚ), 0], ![(-13 / 5 : ℚ), (-37 / 10 : ℚ), (-13 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 3 : ℚ), (1 / 2 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(-5 / 2 : ℚ), (-10 / 3 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), 0, (-13 / 12 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ)], ![(-9 / 8 : ℚ), 0, (-13 / 6 : ℚ), 0, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0], ![-1, (-1 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 5 : ℚ), 0, (-17 / 15 : ℚ), (1 / 3 : ℚ), (2 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, (-34 / 15 : ℚ), (-2 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-3, 0, -3, 1, -1], ![(-5 / 2 : ℚ), 0, -6, -1, -1]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, (-5 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ)], ![(-9 / 8 : ℚ), 0, (-5 / 2 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-102 / 55 : ℚ), (-16 / 55 : ℚ), -1, (24 / 55 : ℚ), (-38 / 11 : ℚ)], ![(-63 / 55 : ℚ), (-32 / 55 : ℚ), -2, 0, (-178 / 55 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (-1 / 4 : ℚ), -1, -1], ![0, (-5 / 2 : ℚ), (-1 / 2 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 12 : ℚ), 0, (-19 / 18 : ℚ), (1 / 3 : ℚ), (1 / 12 : ℚ)], ![(-13 / 12 : ℚ), 0, (-19 / 9 : ℚ), (1 / 12 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, -3, 1, -1], ![(-3 / 2 : ℚ), 0, -6, 0, -1]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 20 : ℚ), 0, (-21 / 20 : ℚ), (1 / 4 : ℚ), (-1 / 20 : ℚ)], ![(-41 / 40 : ℚ), 0, (-21 / 10 : ℚ), (3 / 40 : ℚ), (-1 / 40 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-38 / 17 : ℚ), 0, (-59 / 51 : ℚ), (16 / 17 : ℚ), (-42 / 17 : ℚ)], ![(-21 / 17 : ℚ), 0, (-118 / 51 : ℚ), (4 / 17 : ℚ), (-40 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (-1 / 4 : ℚ), 0, -1], ![0, (-5 / 2 : ℚ), (-1 / 2 : ℚ), 1, -1]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 2 : ℚ), 0, -3, 1, -1], ![(-5 / 2 : ℚ), 0, -6, 1, -1]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 4 : ℚ), 0, (-23 / 16 : ℚ), (-3 / 16 : ℚ), -4], ![(-11 / 8 : ℚ), 0, (-23 / 8 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 17 : ℚ), 0, (-19 / 17 : ℚ), (-9 / 17 : ℚ), (-40 / 17 : ℚ)], ![(-20 / 17 : ℚ), 0, (-38 / 17 : ℚ), (-6 / 17 : ℚ), (-77 / 34 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, -3, 0, -1], ![(-3 / 2 : ℚ), 0, -6, -1, -1]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), 0, (-16 / 15 : ℚ), (1 / 5 : ℚ), (-11 / 5 : ℚ)], ![(-11 / 10 : ℚ), 0, (-32 / 15 : ℚ), 0, (-43 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 12 : ℚ), 0, (-19 / 6 : ℚ), (-13 / 12 : ℚ), (-19 / 12 : ℚ)], ![(-4 / 3 : ℚ), 0, (-19 / 3 : ℚ), (-13 / 12 : ℚ), (-19 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 17 : ℚ), 0, (-21 / 17 : ℚ), (-46 / 17 : ℚ), (-35 / 17 : ℚ)], ![(-23 / 17 : ℚ), 0, (-42 / 17 : ℚ), (-43 / 17 : ℚ), (-29 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-112 / 25 : ℚ), (24 / 25 : ℚ), (99 / 25 : ℚ), (9 / 5 : ℚ), 0], ![(-58 / 25 : ℚ), (-73 / 25 : ℚ), 0, (4 / 25 : ℚ), (2 / 25 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (3 / 10 : ℚ), (-11 / 10 : ℚ), (-11 / 10 : ℚ), (-31 / 5 : ℚ)], ![(1 / 10 : ℚ), 0, (11 / 10 : ℚ), (-11 / 10 : ℚ), (-31 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (1 / 10 : ℚ), 0, 0, (-29 / 10 : ℚ)], ![-1, (-8 / 5 : ℚ), 0, 0, (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-24 / 5 : ℚ), 0, (133 / 75 : ℚ), (8 / 25 : ℚ), (-4 / 25 : ℚ)], ![(-64 / 25 : ℚ), (-92 / 25 : ℚ), (-109 / 75 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 5 : ℚ), (31 / 20 : ℚ), (69 / 20 : ℚ), (-23 / 20 : ℚ), 0], ![(-43 / 20 : ℚ), (-12 / 5 : ℚ), 0, (-23 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-26 / 5 : ℚ), (-13 / 10 : ℚ), (11 / 5 : ℚ), 0, 0], ![(-13 / 5 : ℚ), (-97 / 20 : ℚ), (-8 / 5 : ℚ), 0, (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (4 / 3 : ℚ), (10 / 3 : ℚ), 0, 0], ![-2, (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 25 : ℚ), (-18 / 25 : ℚ), (-148 / 25 : ℚ), (-71 / 25 : ℚ)], ![(-3 / 25 : ℚ), 0, (24 / 25 : ℚ), (-26 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), -1, -1, -6], ![0, 0, 0, -1, -3]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (1 / 10 : ℚ), 0, 0, (-29 / 10 : ℚ)], ![-1, (-8 / 5 : ℚ), 0, 0, (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-80 / 17 : ℚ), 0, (37 / 17 : ℚ), (14 / 17 : ℚ), 0], ![(-42 / 17 : ℚ), (-61 / 17 : ℚ), (4 / 17 : ℚ), (-18 / 17 : ℚ), (2 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 4 : ℚ), (23 / 16 : ℚ), (25 / 16 : ℚ), (-19 / 16 : ℚ), 0], ![(-35 / 16 : ℚ), (-5 / 2 : ℚ), (1 / 8 : ℚ), (-19 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-56 / 13 : ℚ), (15 / 13 : ℚ), (21 / 13 : ℚ), 0, 0], ![(-28 / 13 : ℚ), (-71 / 26 : ℚ), (2 / 13 : ℚ), 0, (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (6 / 5 : ℚ), (11 / 5 : ℚ), 0, 0], ![-2, (-13 / 5 : ℚ), (2 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 20 : ℚ), (1 / 20 : ℚ), (-41 / 60 : ℚ), (-401 / 60 : ℚ), (-11 / 5 : ℚ)], ![0, (1 / 20 : ℚ), (1 / 20 : ℚ), (-65 / 12 : ℚ), (-43 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, -4], ![-1, (-5 / 3 : ℚ), 0, 0, -2]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, -3], ![-1, (-5 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (1 / 2 : ℚ), 0, 0, -4], ![-1, (-3 / 2 : ℚ), 0, 0, -2]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (-9 / 4 : ℚ)], ![(-5 / 4 : ℚ), (-3 / 2 : ℚ), 0, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-43 / 17 : ℚ), (-4 / 17 : ℚ), 0, (-65 / 17 : ℚ), (-28 / 17 : ℚ)], ![(-43 / 34 : ℚ), (-35 / 17 : ℚ), (3 / 34 : ℚ), (-65 / 34 : ℚ), (-109 / 68 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 12 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 3 : ℚ), -1], ![(-4 / 3 : ℚ), (-25 / 12 : ℚ), (1 / 12 : ℚ), (-13 / 8 : ℚ), (-11 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 3 : ℚ), (1 / 4 : ℚ), (1 / 6 : ℚ), (-5 / 4 : ℚ), 0], ![(-9 / 4 : ℚ), (-19 / 6 : ℚ), (-5 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-52 / 11 : ℚ), 0, (6 / 11 : ℚ), 0, 0], ![(-26 / 11 : ℚ), (-41 / 11 : ℚ), (-14 / 11 : ℚ), 0, (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, 0, (5 / 3 : ℚ), 0, 0], ![-2, (-37 / 12 : ℚ), (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 22 : ℚ), (1 / 11 : ℚ), (-63 / 11 : ℚ), (-51 / 22 : ℚ)], ![(-1 / 22 : ℚ), 0, 1, (-109 / 22 : ℚ), (-49 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 6 : ℚ), (5 / 3 : ℚ), (-7 / 6 : ℚ), 0, (1 / 12 : ℚ)], ![(-25 / 12 : ℚ), (-7 / 3 : ℚ), (-7 / 6 : ℚ), 0, (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (6 / 5 : ℚ), (-7 / 5 : ℚ), 0, 0], ![-2, (-13 / 5 : ℚ), (-7 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, 0, (-13 / 4 : ℚ), (-3 / 2 : ℚ)], ![-1, (-9 / 4 : ℚ), 0, (-13 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(232 / 109 : ℚ), (-314 / 109 : ℚ), (24 / 109 : ℚ), 0, (-197 / 109 : ℚ)], ![(104 / 109 : ℚ), (-604 / 109 : ℚ), 0, (-12 / 109 : ℚ), (221 / 109 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(14 / 11 : ℚ), (-26 / 11 : ℚ), (1 / 11 : ℚ), (9 / 22 : ℚ), (-29 / 22 : ℚ)], ![(13 / 22 : ℚ), (-51 / 11 : ℚ), 0, (4 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 6 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 24 : ℚ), (1 / 12 : ℚ)], ![(3 / 8 : ℚ), (-17 / 4 : ℚ), (-1 / 6 : ℚ), 0, (17 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-116 / 23 : ℚ), (-64 / 23 : ℚ), (-116 / 23 : ℚ), (49 / 23 : ℚ), 0], ![(-64 / 23 : ℚ), (-64 / 23 : ℚ), (-116 / 23 : ℚ), (-37 / 23 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 4 : ℚ), (-35 / 16 : ℚ), (-17 / 4 : ℚ), (25 / 16 : ℚ), 0], ![(-35 / 16 : ℚ), (-35 / 16 : ℚ), (-17 / 4 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xx, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 4 : ℚ), -7], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 4 : ℚ), (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 5 : ℚ), (-23 / 10 : ℚ), (-22 / 5 : ℚ), (6 / 5 : ℚ), 0], ![(-23 / 10 : ℚ), (-23 / 10 : ℚ), (-22 / 5 : ℚ), (-7 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(14 / 11 : ℚ), (-26 / 11 : ℚ), (1 / 11 : ℚ), (-4 / 3 : ℚ), (-29 / 22 : ℚ)], ![(13 / 22 : ℚ), (-51 / 11 : ℚ), 0, (47 / 33 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 5 : ℚ), (-14 / 5 : ℚ), 0, (-9 / 5 : ℚ), (-9 / 5 : ℚ)], ![(4 / 5 : ℚ), (-26 / 5 : ℚ), 0, (9 / 5 : ℚ), (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-83 / 38 : ℚ), 0, (-85 / 38 : ℚ), (33 / 38 : ℚ), (3 / 38 : ℚ)], ![(-43 / 38 : ℚ), (3 / 38 : ℚ), (-44 / 19 : ℚ), (9 / 38 : ℚ), (-9 / 38 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 3 : ℚ), (-13 / 6 : ℚ), 0, (-7 / 6 : ℚ), (7 / 6 : ℚ)], ![(-3 / 4 : ℚ), (-13 / 3 : ℚ), (-1 / 12 : ℚ), (7 / 6 : ℚ), (7 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(17 / 8 : ℚ), (-11 / 4 : ℚ), 0, (-13 / 8 : ℚ), (-55 / 8 : ℚ)], ![(7 / 8 : ℚ), (-41 / 8 : ℚ), 0, 2, (-55 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (-7 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-4 / 3 : ℚ)], ![(1 / 3 : ℚ), (-9 / 2 : ℚ), 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-461 / 188 : ℚ), (-3 / 94 : ℚ), (-203 / 94 : ℚ), 1, (81 / 188 : ℚ)], ![(-85 / 47 : ℚ), 0, (-209 / 94 : ℚ), (3 / 47 : ℚ), (-2 / 47 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 16 : ℚ), (-17 / 8 : ℚ), 0, (-9 / 8 : ℚ), (9 / 8 : ℚ)], ![(3 / 16 : ℚ), (-17 / 4 : ℚ), (-1 / 16 : ℚ), 0, (9 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(12 / 5 : ℚ), (-62 / 25 : ℚ), 0, (-34 / 25 : ℚ), (-172 / 25 : ℚ)], ![(27 / 25 : ℚ), (-118 / 25 : ℚ), 0, (6 / 25 : ℚ), (-172 / 25 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), (-9 / 4 : ℚ), 0, 0, (-11 / 8 : ℚ)], ![(3 / 8 : ℚ), (-35 / 8 : ℚ), 0, (11 / 8 : ℚ), (-11 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 6 : ℚ), (-5 / 2 : ℚ), (1 / 6 : ℚ), 0, (3 / 2 : ℚ)], ![(1 / 2 : ℚ), -5, 0, (3 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 5 : ℚ), (-23 / 10 : ℚ), (39 / 10 : ℚ), (19 / 10 : ℚ), 0], ![(-23 / 10 : ℚ), (-23 / 10 : ℚ), 0, (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), -1, -1, -6], ![0, (-1 / 4 : ℚ), 1, -1, -3]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (-5 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)], ![-1, (-5 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 5 : ℚ), (-23 / 10 : ℚ), (43 / 30 : ℚ), (6 / 5 : ℚ), 0], ![(-23 / 10 : ℚ), (-23 / 10 : ℚ), (-37 / 30 : ℚ), (-7 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 9 : ℚ), (-7 / 3 : ℚ), (14 / 9 : ℚ), (-4 / 3 : ℚ), 0], ![(-7 / 3 : ℚ), (-7 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 5 : ℚ), (-29 / 10 : ℚ), (19 / 10 : ℚ), (-3 / 5 : ℚ), 0], ![(-23 / 10 : ℚ), (-29 / 10 : ℚ), (-13 / 10 : ℚ), (-3 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (-8 / 3 : ℚ), (11 / 3 : ℚ), 0, 0], ![-2, (-8 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-56 / 13 : ℚ), (-29 / 13 : ℚ), (48 / 13 : ℚ), 0, (-1 / 13 : ℚ)], ![(-29 / 13 : ℚ), (-29 / 13 : ℚ), 0, 0, (-1 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), -1, -1, -6], ![0, (-1 / 2 : ℚ), 0, -1, -3]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), -1, -1, (-9 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, -1, (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 4 : ℚ), (-35 / 16 : ℚ), (25 / 16 : ℚ), (3 / 2 : ℚ), 0], ![(-35 / 16 : ℚ), (-35 / 16 : ℚ), (1 / 8 : ℚ), (-7 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 2 : ℚ), (-19 / 8 : ℚ), (17 / 8 : ℚ), (-11 / 8 : ℚ), 0], ![(-19 / 8 : ℚ), (-19 / 8 : ℚ), (1 / 4 : ℚ), (-11 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 3 : ℚ), (-8 / 3 : ℚ), (7 / 3 : ℚ), 0, (1 / 3 : ℚ)], ![(-7 / 3 : ℚ), (-8 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (-12 / 5 : ℚ), (11 / 5 : ℚ), 0, 0], ![-2, (-12 / 5 : ℚ), (2 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 5 : ℚ), (-12 / 5 : ℚ), 2, (1 / 5 : ℚ), 0], ![(-12 / 5 : ℚ), (-12 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, -1, -6], ![0, (-1 / 2 : ℚ), 1, -1, -3]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (-3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![-1, (-3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (-3 / 2 : ℚ), 0, 0, -4], ![-1, (-3 / 2 : ℚ), 0, 0, -2]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-9 / 2 : ℚ), (-7 / 4 : ℚ)], ![(-5 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-9 / 4 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 3 : ℚ), (-9 / 4 : ℚ), (1 / 3 : ℚ), (-5 / 4 : ℚ), 0], ![(-9 / 4 : ℚ), (-9 / 4 : ℚ), (-13 / 12 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 2 : ℚ), (-11 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![(-9 / 4 : ℚ), (-11 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (-7 / 3 : ℚ), (4 / 3 : ℚ), 0, 0], ![-2, (-7 / 3 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-32 / 7 : ℚ), (-17 / 7 : ℚ), (2 / 7 : ℚ), 0, (-1 / 7 : ℚ)], ![(-17 / 7 : ℚ), (-17 / 7 : ℚ), (-9 / 7 : ℚ), 0, (-1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 3 : ℚ), (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0, (1 / 3 : ℚ)], ![(-7 / 3 : ℚ), (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0], ![-2, (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0]] }
]

theorem conicDetC35_checked : conicDetC35.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
