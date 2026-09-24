import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC34 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), 0, (5 / 4 : ℚ), (-1 / 3 : ℚ), (-1 / 24 : ℚ)], ![(-1 / 24 : ℚ), (-17 / 4 : ℚ), (-29 / 24 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 17 : ℚ), (-7 / 17 : ℚ), (26 / 17 : ℚ), (-20 / 17 : ℚ), 0], ![(-2 / 17 : ℚ), (-74 / 17 : ℚ), (-24 / 17 : ℚ), (-20 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 12 : ℚ), 0, (5 / 4 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, (-17 / 4 : ℚ), (-7 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-11 / 12 : ℚ), 2, (-1 / 6 : ℚ), (5 / 12 : ℚ)], ![(-1 / 6 : ℚ), -5, (-11 / 6 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 19 : ℚ), (-12 / 19 : ℚ), (29 / 19 : ℚ), (-2 / 19 : ℚ), (-2 / 19 : ℚ)], ![0, (-84 / 19 : ℚ), (-25 / 19 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-47 / 22 : ℚ), (-13 / 22 : ℚ), (31 / 22 : ℚ), (-1 / 22 : ℚ), (-3 / 22 : ℚ)], ![(-1 / 11 : ℚ), (-47 / 11 : ℚ), (-29 / 22 : ℚ), 0, (-1 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), -3], ![0, (-43 / 20 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-3 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-41 / 10 : ℚ)], ![0, (-23 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (-79 / 40 : ℚ)], ![0, (-43 / 20 : ℚ), 0, 0, (-39 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, (7 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-19 / 4 : ℚ), 0, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 13 : ℚ), (-12 / 13 : ℚ), (23 / 13 : ℚ), (4 / 13 : ℚ), (-2 / 13 : ℚ)], ![0, (-60 / 13 : ℚ), 0, (-19 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 20 : ℚ), 0, (23 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ)], ![0, (-83 / 20 : ℚ), 0, (-11 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 12 : ℚ), (-5 / 12 : ℚ), (17 / 12 : ℚ), (-5 / 4 : ℚ), 0], ![0, (-13 / 3 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 9 : ℚ), 0, (8 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ)], ![0, (-16 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), (-2 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ)], ![0, (-9 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 5 : ℚ), (-6 / 5 : ℚ), (3 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-24 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 20 : ℚ), (-11 / 20 : ℚ), (3 / 20 : ℚ), (-1 / 20 : ℚ), (-3 / 20 : ℚ)], ![0, (-21 / 5 : ℚ), 0, 0, (-1 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-35 / 12 : ℚ), (-35 / 12 : ℚ), 0, (23 / 12 : ℚ), 0], ![0, -6, (-23 / 12 : ℚ), (23 / 12 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-1 / 2 : ℚ), 0, 0, -4], ![0, (-9 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-9 / 4 : ℚ), 0, (5 / 4 : ℚ), 0], ![0, (-19 / 4 : ℚ), (-5 / 4 : ℚ), (5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0, (-10 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-1 / 2 : ℚ), 0, 0, -4], ![0, (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-10 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-81 / 20 : ℚ), -3], ![0, (-43 / 20 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 11 : ℚ), (-7 / 22 : ℚ), (-1 / 22 : ℚ), (-67 / 22 : ℚ), (-87 / 44 : ℚ)], ![(-1 / 22 : ℚ), (-24 / 11 : ℚ), 0, (-23 / 22 : ℚ), (-43 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-3 / 5 : ℚ), (-1 / 10 : ℚ), (-41 / 10 : ℚ), (-21 / 10 : ℚ)], ![0, (-23 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-3 / 5 : ℚ), (-1 / 10 : ℚ), (-41 / 10 : ℚ), (-39 / 20 : ℚ)], ![0, (-23 / 10 : ℚ), 0, 0, (-19 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 11 : ℚ), (-7 / 22 : ℚ), (-1 / 22 : ℚ), (-87 / 44 : ℚ), (-23 / 22 : ℚ)], ![(-1 / 22 : ℚ), (-24 / 11 : ℚ), 0, (-43 / 22 : ℚ), -1]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, (1 / 12 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-9 / 2 : ℚ), (-4 / 3 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 8 : ℚ), (-7 / 8 : ℚ), (1 / 4 : ℚ), (-11 / 8 : ℚ), 0], ![(-1 / 4 : ℚ), (-19 / 4 : ℚ), (-13 / 8 : ℚ), (-11 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 7 : ℚ), 0, (2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, (-34 / 7 : ℚ), (-11 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 11 : ℚ), -1, (2 / 11 : ℚ), (-2 / 11 : ℚ), (5 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-56 / 11 : ℚ), (-19 / 11 : ℚ), 0, (6 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 13 : ℚ), (-12 / 13 : ℚ), (4 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ)], ![0, (-60 / 13 : ℚ), (-19 / 13 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-13 / 12 : ℚ), (1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 6 : ℚ), (-9 / 2 : ℚ), (-17 / 12 : ℚ), 0, (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), 0, (-3 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (-43 / 10 : ℚ), (-6 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), (-1 / 2 : ℚ), (-13 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-23 / 5 : ℚ), (-13 / 10 : ℚ), 0, (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), (-5 / 6 : ℚ), (-3 / 2 : ℚ), (-1 / 6 : ℚ), 0], ![0, (-14 / 3 : ℚ), (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-35 / 16 : ℚ), (-9 / 16 : ℚ), (-19 / 16 : ℚ), 0, (-1 / 16 : ℚ)], ![(-1 / 8 : ℚ), (-35 / 8 : ℚ), (-19 / 16 : ℚ), 0, (-1 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 5 : ℚ), (-62 / 25 : ℚ), (3 / 25 : ℚ), (27 / 50 : ℚ), (-36 / 25 : ℚ)], ![(-3 / 25 : ℚ), (-121 / 25 : ℚ), 0, (12 / 25 : ℚ), (39 / 25 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (-12 / 5 : ℚ), (1 / 10 : ℚ), (9 / 20 : ℚ), (-7 / 5 : ℚ)], ![0, (-47 / 10 : ℚ), 0, (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (-7 / 3 : ℚ), (1 / 12 : ℚ), (3 / 8 : ℚ), (1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-55 / 12 : ℚ), 0, (1 / 3 : ℚ), (19 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-10 / 3 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ), (-19 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-19 / 3 : ℚ), 0, (1 / 3 : ℚ), -3]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(20 / 17 : ℚ), (-66 / 17 : ℚ), (8 / 17 : ℚ), (36 / 17 : ℚ), (-128 / 17 : ℚ)], ![0, (-124 / 17 : ℚ), 0, (32 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), (-9 / 2 : ℚ), (2 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-5 / 2 : ℚ), (-55 / 12 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), (3 / 10 : ℚ), (-7 / 5 : ℚ)], ![0, (-23 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), (-1 / 3 : ℚ), (-13 / 24 : ℚ), (5 / 4 : ℚ), (-1 / 24 : ℚ)], ![(-1 / 24 : ℚ), (-17 / 8 : ℚ), (-101 / 24 : ℚ), (-29 / 24 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 17 : ℚ), (-40 / 17 : ℚ), (-76 / 17 : ℚ), (35 / 17 : ℚ), 0], ![(-4 / 17 : ℚ), (-40 / 17 : ℚ), (-76 / 17 : ℚ), (-31 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), (-3 / 5 : ℚ), (-9 / 10 : ℚ), (3 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (-11 / 5 : ℚ), (-43 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), -3, (-16 / 3 : ℚ), (5 / 3 : ℚ), 0], ![0, -3, (-16 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-3 / 2 : ℚ), (-11 / 4 : ℚ), 0, (-7 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-11 / 4 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-5 / 3 : ℚ), -3, 0, (-13 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), -3, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 11 : ℚ), (-16 / 11 : ℚ), (-26 / 11 : ℚ), (2 / 11 : ℚ), (-2 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-28 / 11 : ℚ), (-54 / 11 : ℚ), (-19 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 8 : ℚ), (-19 / 8 : ℚ), (-9 / 2 : ℚ), (1 / 4 : ℚ), 0], ![(-1 / 4 : ℚ), (-19 / 8 : ℚ), (-9 / 2 : ℚ), (-13 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-2 / 3 : ℚ), (-13 / 12 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (-53 / 12 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 5 : ℚ), (-12 / 5 : ℚ), (1 / 10 : ℚ), (-27 / 20 : ℚ), (-7 / 5 : ℚ)], ![0, (-47 / 10 : ℚ), 0, (3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (-11 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-6 / 5 : ℚ)], ![0, (-43 / 10 : ℚ), 0, (6 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(24 / 37 : ℚ), (-86 / 37 : ℚ), (3 / 37 : ℚ), (-48 / 37 : ℚ), (3 / 37 : ℚ)], ![(-7 / 37 : ℚ), (-169 / 37 : ℚ), 0, (51 / 37 : ℚ), (58 / 37 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 12 : ℚ), (-9 / 4 : ℚ), (1 / 12 : ℚ), (-5 / 4 : ℚ), (5 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-9 / 2 : ℚ), 0, (5 / 4 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), (-3 / 76 : ℚ), (-167 / 76 : ℚ), (75 / 76 : ℚ), (-20 / 19 : ℚ)], ![(-3 / 38 : ℚ), 0, (-173 / 76 : ℚ), (-69 / 76 : ℚ), (-37 / 76 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(17 / 50 : ℚ), (-56 / 25 : ℚ), (3 / 50 : ℚ), (-61 / 50 : ℚ), (-89 / 20 : ℚ)], ![0, (-221 / 50 : ℚ), 0, (32 / 25 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(56 / 51 : ℚ), (-42 / 17 : ℚ), 0, (-71 / 51 : ℚ), (-352 / 51 : ℚ)], ![(-4 / 17 : ℚ), (-80 / 17 : ℚ), 0, (83 / 51 : ℚ), (-352 / 51 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (-9 / 4 : ℚ), 0, (-11 / 8 : ℚ), (-5 / 4 : ℚ)], ![0, (-35 / 8 : ℚ), 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (-7 / 3 : ℚ), (1 / 12 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ)], ![0, (-55 / 12 : ℚ), 0, 0, (19 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 8 : ℚ), -1, (-5 / 4 : ℚ), 0, 0], ![0, -2, (-11 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (-12 / 5 : ℚ), (1 / 10 : ℚ), (-7 / 5 : ℚ), (-93 / 20 : ℚ)], ![0, (-47 / 10 : ℚ), 0, 0, (-11 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (-12 / 5 : ℚ), (1 / 10 : ℚ), (-7 / 5 : ℚ), (-19 / 4 : ℚ)], ![0, (-47 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (-8 / 3 : ℚ), 0, (-5 / 3 : ℚ), -5], ![0, -5, 0, 0, -5]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), (-5 / 2 : ℚ), 0, 0, (-7 / 4 : ℚ)], ![0, (-19 / 4 : ℚ), 0, (7 / 4 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, (-3 / 2 : ℚ), (-13 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-19 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (-7 / 3 : ℚ), 0, (-11 / 6 : ℚ), (-47 / 6 : ℚ)], ![0, (-9 / 2 : ℚ), 0, (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (-9 / 4 : ℚ), (1 / 12 : ℚ), 0, (5 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-9 / 2 : ℚ), 0, (5 / 4 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 7 : ℚ), (-16 / 7 : ℚ), (1 / 14 : ℚ), (1 / 14 : ℚ), (-79 / 14 : ℚ)], ![(-1 / 14 : ℚ), (-9 / 2 : ℚ), 0, (3 / 2 : ℚ), (-39 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(10 / 7 : ℚ), (-18 / 7 : ℚ), (1 / 7 : ℚ), (2 / 7 : ℚ), (-71 / 14 : ℚ)], ![0, -5, 0, (16 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(6 / 11 : ℚ), (-24 / 11 : ℚ), 0, (1 / 11 : ℚ), (-59 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-47 / 11 : ℚ), 0, (16 / 11 : ℚ), (-59 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 3 : ℚ), (1 / 12 : ℚ), (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-55 / 12 : ℚ), 0, (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 17 : ℚ), (-33 / 17 : ℚ), (-13 / 17 : ℚ), (4 / 17 : ℚ), (-64 / 17 : ℚ)], ![0, (-62 / 17 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(10 / 7 : ℚ), (-18 / 7 : ℚ), (1 / 7 : ℚ), (-51 / 7 : ℚ), (-51 / 7 : ℚ)], ![0, -5, 0, 0, (-25 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 5 : ℚ), 0, (-34 / 5 : ℚ), (-26 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-26 / 5 : ℚ), 0, (-16 / 5 : ℚ), (-26 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (-18 / 5 : ℚ), (2 / 5 : ℚ), -7, (-18 / 5 : ℚ)], ![0, (-34 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 9 : ℚ), (-26 / 9 : ℚ), 0, (-68 / 9 : ℚ), (-22 / 3 : ℚ)], ![0, (-16 / 3 : ℚ), 0, 0, (-22 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)], ![0, 0, (-9 / 4 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 9 : ℚ), (-8 / 9 : ℚ), -1, -1], ![0, (-14 / 9 : ℚ), (-8 / 9 : ℚ), 1, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, (-6 / 5 : ℚ), 0], ![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (13 / 10 : ℚ), (13 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, (-13 / 6 : ℚ), 1, -1], ![(-1 / 6 : ℚ), 0, (-7 / 3 : ℚ), -1, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 3 : ℚ), (-41 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, (11 / 6 : ℚ), (-41 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-7 / 4 : ℚ), (-3 / 2 : ℚ)], ![0, (-5 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (-9 / 4 : ℚ), (3 / 4 : ℚ), 0], ![0, 0, (-5 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), 0, (-7 / 6 : ℚ), 0, 0], ![0, -1, (-4 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-7 / 4 : ℚ), (-19 / 4 : ℚ)], ![0, (-5 / 2 : ℚ), 0, 0, (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, -1], ![0, (-11 / 6 : ℚ), (-1 / 3 : ℚ), 1, -1]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), (-3 / 4 : ℚ), (11 / 8 : ℚ), (11 / 8 : ℚ), (-1 / 8 : ℚ)], ![0, (-9 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), (-5 / 2 : ℚ), (11 / 6 : ℚ), (11 / 6 : ℚ), 0], ![0, (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-4 / 3 : ℚ), 0, 0, (-11 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-5 / 3 : ℚ), 0, 0, -4], ![0, (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-5 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-2 / 3 : ℚ), (3 / 2 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (-17 / 12 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 17 : ℚ), (-40 / 17 : ℚ), (35 / 17 : ℚ), (4 / 17 : ℚ), 0], ![(-4 / 17 : ℚ), (-40 / 17 : ℚ), (-31 / 17 : ℚ), (-27 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-2 / 3 : ℚ), (3 / 2 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (-17 / 12 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 17 : ℚ), (-40 / 17 : ℚ), (35 / 17 : ℚ), (-23 / 17 : ℚ), 0], ![(-4 / 17 : ℚ), (-40 / 17 : ℚ), (-31 / 17 : ℚ), (-23 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), -1, (3 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-7 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-5 / 2 : ℚ), 2, (-1 / 6 : ℚ), (1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-5 / 2 : ℚ), (-11 / 6 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-20 / 9 : ℚ), (-8 / 3 : ℚ), (19 / 9 : ℚ), (-2 / 9 : ℚ), 0], ![0, (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-43 / 20 : ℚ), (-43 / 20 : ℚ), (29 / 20 : ℚ), 0, (-1 / 20 : ℚ)], ![(-1 / 10 : ℚ), (-43 / 20 : ℚ), (-27 / 20 : ℚ), 0, (-1 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-13 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-17 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-5 / 4 : ℚ), (-1 / 8 : ℚ), 0, (-15 / 8 : ℚ)], ![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), (-3 / 4 : ℚ), (11 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ)], ![0, (-9 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), (-5 / 2 : ℚ), (11 / 6 : ℚ), (1 / 3 : ℚ), 0], ![0, (-5 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), (-3 / 5 : ℚ), (13 / 10 : ℚ), (-3 / 5 : ℚ), (-1 / 10 : ℚ)], ![0, (-11 / 5 : ℚ), 0, (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), (-5 / 2 : ℚ), (11 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![0, (-5 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), (-3 / 5 : ℚ), (3 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (-11 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-5 / 2 : ℚ), (3 / 4 : ℚ), (-1 / 4 : ℚ), 0], ![0, (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), -3, (5 / 3 : ℚ), (-1 / 3 : ℚ), 0], ![0, -3, 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), (-19 / 8 : ℚ), (5 / 8 : ℚ), 0, (-1 / 8 : ℚ)], ![0, (-19 / 8 : ℚ), 0, 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-4 / 3 : ℚ), 0, 0, (-11 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-3 / 2 : ℚ), 0, 0, -4], ![0, (-3 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-7 / 6 : ℚ), 0, 0, (-10 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-5 / 3 : ℚ), 0, 0, -4], ![0, (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-17 / 4 : ℚ), (-13 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-7 / 2 : ℚ), (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-5 / 4 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-17 / 4 : ℚ), (-9 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-4 / 3 : ℚ), 0, (-25 / 6 : ℚ), (-11 / 6 : ℚ)], ![0, (-4 / 3 : ℚ), 0, 0, (-11 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 8 : ℚ), 0, (1 / 8 : ℚ), 0, (-25 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-7 / 8 : ℚ), 0, (-1 / 8 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-35 / 16 : ℚ), (-35 / 16 : ℚ), (1 / 8 : ℚ), (-19 / 16 : ℚ), 0], ![(-1 / 8 : ℚ), (-35 / 16 : ℚ), (-21 / 16 : ℚ), (-19 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 7 : ℚ), (-6 / 7 : ℚ), (1 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ)], ![0, (-16 / 7 : ℚ), (-9 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 11 : ℚ), (-28 / 11 : ℚ), (2 / 11 : ℚ), (-2 / 11 : ℚ), (6 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-28 / 11 : ℚ), (-19 / 11 : ℚ), 0, (6 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), (-5 / 2 : ℚ), (1 / 3 : ℚ), (-1 / 6 : ℚ), 0], ![0, (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), (-23 / 10 : ℚ), (1 / 5 : ℚ), 0, (-1 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-23 / 10 : ℚ), (-3 / 2 : ℚ), 0, (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 20 : ℚ), (-3 / 10 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ)], ![0, (-21 / 10 : ℚ), (-11 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 5 : ℚ), (-13 / 5 : ℚ), (-8 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-13 / 5 : ℚ), (-8 / 5 : ℚ), 0, (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-20 / 9 : ℚ), (-8 / 3 : ℚ), (-5 / 3 : ℚ), (-2 / 9 : ℚ), 0], ![0, (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-27 / 16 : ℚ), (-1 / 16 : ℚ), (15 / 16 : ℚ), (15 / 16 : ℚ), -1], ![0, 0, (-13 / 16 : ℚ), 0, (-7 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, 0, (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 24 : ℚ), (1 / 8 : ℚ), (29 / 24 : ℚ), (29 / 24 : ℚ), (-1 / 24 : ℚ)], ![0, (1 / 2 : ℚ), (-9 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 4 : ℚ), (3 / 4 : ℚ), (7 / 4 : ℚ), (7 / 4 : ℚ), (-1 / 2 : ℚ)], ![0, (7 / 4 : ℚ), (-7 / 4 : ℚ), (7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-15 / 4 : ℚ)], ![0, 0, (-1 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), (1 / 8 : ℚ), (9 / 8 : ℚ), (9 / 8 : ℚ), (-1 / 4 : ℚ)], ![0, (1 / 2 : ℚ), (-9 / 8 : ℚ), (9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-42 / 29 : ℚ), (-2 / 29 : ℚ), (4 / 29 : ℚ), (-144 / 29 : ℚ)], ![(-4 / 29 : ℚ), (-66 / 29 : ℚ), (21 / 29 : ℚ), (25 / 29 : ℚ), (-70 / 29 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 2 : ℚ), (1 / 5 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-3 / 10 : ℚ), (-3 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-66 / 49 : ℚ), (-11 / 49 : ℚ), (8 / 49 : ℚ), (-32 / 7 : ℚ)], ![(-8 / 49 : ℚ), (-114 / 49 : ℚ), (19 / 49 : ℚ), (41 / 49 : ℚ), (-220 / 49 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 14 : ℚ), (5 / 14 : ℚ), (19 / 14 : ℚ), (-19 / 14 : ℚ), (-1 / 14 : ℚ)], ![(-1 / 14 : ℚ), (5 / 7 : ℚ), (-19 / 14 : ℚ), (-19 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 1, -1, (-1 / 3 : ℚ)], ![0, 0, -1, -1, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 5 : ℚ), (14 / 15 : ℚ), (29 / 15 : ℚ), (-29 / 15 : ℚ), 0], ![(-4 / 15 : ℚ), (28 / 15 : ℚ), (-29 / 15 : ℚ), (-29 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), (8 / 9 : ℚ), 2, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (19 / 9 : ℚ), (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (17 / 18 : ℚ), 2, (-1 / 6 : ℚ), (5 / 12 : ℚ)], ![(-1 / 6 : ℚ), (37 / 18 : ℚ), (-11 / 6 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 16 : ℚ), (-3 / 16 : ℚ), (15 / 16 : ℚ), (-3 / 16 : ℚ), (-3 / 16 : ℚ)], ![0, 0, (-9 / 16 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-35 / 16 : ℚ), (13 / 16 : ℚ), (31 / 16 : ℚ), (-3 / 16 : ℚ), (-3 / 16 : ℚ)], ![0, 2, (-25 / 16 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 11 : ℚ), (25 / 33 : ℚ), (20 / 11 : ℚ), (-1 / 11 : ℚ), (-3 / 11 : ℚ)], ![(-2 / 11 : ℚ), (56 / 33 : ℚ), (-18 / 11 : ℚ), 0, (-1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), (1 / 2 : ℚ), (13 / 10 : ℚ), (1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (11 / 10 : ℚ), 0, (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 20 : ℚ), (-1 / 20 : ℚ), (1 / 4 : ℚ), (1 / 10 : ℚ), (-1 / 20 : ℚ)], ![0, 0, 0, (-3 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-81 / 40 : ℚ), (9 / 40 : ℚ), (9 / 8 : ℚ), (1 / 20 : ℚ), (-1 / 40 : ℚ)], ![0, (1 / 2 : ℚ), 0, (-43 / 40 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), (1 / 4 : ℚ), (5 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 8 : ℚ)], ![0, (1 / 2 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 1, -1, (-1 / 3 : ℚ)], ![0, 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (3 / 4 : ℚ), (7 / 4 : ℚ), (-7 / 4 : ℚ), 0], ![0, (3 / 2 : ℚ), 0, (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), (2 / 3 : ℚ), 0, (4 / 3 : ℚ), -1], ![0, (5 / 3 : ℚ), (-4 / 3 : ℚ), (4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-1 / 2 : ℚ), 0, 0, -4], ![0, (-1 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-65 / 32 : ℚ), (3 / 32 : ℚ), 0, (33 / 32 : ℚ), (-1 / 16 : ℚ)], ![0, (1 / 4 : ℚ), (-33 / 32 : ℚ), (33 / 32 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (1 / 6 : ℚ), (4 / 3 : ℚ), (-4 / 3 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 6 : ℚ), (1 / 2 : ℚ), (4 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-3 / 2 : ℚ), 0, 0, -4], ![0, (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-23 / 12 : ℚ), 0, (11 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-23 / 6 : ℚ), (11 / 12 : ℚ), (11 / 12 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, -1, (-1 / 3 : ℚ)], ![0, 0, -1, -1, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), -1, 0, 0, (-11 / 3 : ℚ)], ![(-1 / 3 : ℚ), -2, 0, 0, (-11 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), (1 / 2 : ℚ), (1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (11 / 10 : ℚ), (-6 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-18 / 11 : ℚ), (1 / 11 : ℚ), (-51 / 11 : ℚ), (-95 / 22 : ℚ)], ![(-1 / 11 : ℚ), (-24 / 11 : ℚ), (10 / 11 : ℚ), (-25 / 11 : ℚ), (-47 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-3 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-81 / 40 : ℚ), (9 / 40 : ℚ), (1 / 20 : ℚ), (-1 / 40 : ℚ), (-1 / 40 : ℚ)], ![0, (1 / 2 : ℚ), (-43 / 40 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), (1 / 6 : ℚ), (-55 / 12 : ℚ), (-5 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 3 : ℚ), (5 / 6 : ℚ), (-9 / 2 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 13 : ℚ), (-4 / 13 : ℚ), (-15 / 13 : ℚ), (-16 / 13 : ℚ), (-5 / 13 : ℚ)], ![0, (-6 / 13 : ℚ), (-17 / 13 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 5 : ℚ), -1, (-8 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-3 / 5 : ℚ), (-8 / 5 : ℚ), 0, (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 2 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-17 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 9 : ℚ), (-10 / 9 : ℚ), (-4 / 3 : ℚ), (-10 / 9 : ℚ), 0], ![0, -1, (-4 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-32 / 25 : ℚ), (6 / 25 : ℚ), (6 / 25 : ℚ), 0], ![(-3 / 25 : ℚ), (-58 / 25 : ℚ), 0, 0, (21 / 25 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-44 / 37 : ℚ), (6 / 37 : ℚ), (6 / 37 : ℚ), 0], ![(-3 / 37 : ℚ), (-82 / 37 : ℚ), 0, 0, (14 / 37 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-80 / 33 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ), (-14 / 33 : ℚ)], ![(-43 / 33 : ℚ), (2 / 11 : ℚ), (-80 / 33 : ℚ), (-40 / 33 : ℚ), (-8 / 33 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-57 / 25 : ℚ), 0, (3 / 25 : ℚ), (3 / 25 : ℚ), (3 / 25 : ℚ)], ![(-6 / 5 : ℚ), (3 / 25 : ℚ), (-57 / 25 : ℚ), (-57 / 50 : ℚ), (-7 / 50 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 6 : ℚ)], ![(-5 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 2 : ℚ), (-5 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-58 / 25 : ℚ), (-3 / 25 : ℚ), (18 / 25 : ℚ), (6 / 25 : ℚ), 0], ![(-32 / 25 : ℚ), 0, (-52 / 25 : ℚ), (-29 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-41 / 25 : ℚ), (3 / 25 : ℚ), (3 / 25 : ℚ), (-109 / 25 : ℚ)], ![(-3 / 50 : ℚ), (-241 / 100 : ℚ), 0, 0, (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-56 / 11 : ℚ), (24 / 55 : ℚ), (24 / 55 : ℚ), (113 / 55 : ℚ), (-12 / 55 : ℚ)], ![(-152 / 55 : ℚ), (-56 / 11 : ℚ), (-28 / 11 : ℚ), (-89 / 55 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-80 / 17 : ℚ), (4 / 17 : ℚ), (4 / 17 : ℚ), (37 / 17 : ℚ), 0], ![(-42 / 17 : ℚ), (-80 / 17 : ℚ), (-40 / 17 : ℚ), (4 / 17 : ℚ), (2 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (-8 / 5 : ℚ), (-34 / 5 : ℚ)], ![0, 0, 0, (-7 / 5 : ℚ), (-17 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 11 : ℚ), (1 / 11 : ℚ), (-20 / 11 : ℚ), (-47 / 11 : ℚ)], ![(-1 / 22 : ℚ), 0, 0, (-65 / 44 : ℚ), (-93 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-9 / 2 : ℚ)], ![(-1 / 12 : ℚ), 0, 0, (1 / 2 : ℚ), (-53 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 4 : ℚ), 0], ![(-9 / 4 : ℚ), (-13 / 2 : ℚ), (-13 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), 0, (1 / 8 : ℚ), (-13 / 12 : ℚ), (5 / 24 : ℚ)], ![(-9 / 8 : ℚ), 0, (-17 / 8 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), 0, (9 / 8 : ℚ), (-13 / 12 : ℚ), (1 / 2 : ℚ)], ![(-9 / 8 : ℚ), 0, (-13 / 8 : ℚ), (-13 / 6 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-48 / 23 : ℚ), 0, (82 / 69 : ℚ), (-73 / 69 : ℚ), (-6 / 23 : ℚ)], ![(-25 / 23 : ℚ), 0, (-106 / 69 : ℚ), (-146 / 69 : ℚ), (-4 / 23 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-29 / 28 : ℚ), (1 / 14 : ℚ), (-1 / 84 : ℚ), (1 / 14 : ℚ)], ![(-1 / 28 : ℚ), (-29 / 14 : ℚ), 0, (-1 / 42 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-24 / 11 : ℚ), 0, (31 / 33 : ℚ), (-13 / 11 : ℚ), (-2 / 11 : ℚ)], ![(-12 / 11 : ℚ), 0, (-61 / 33 : ℚ), (-26 / 11 : ℚ), (-1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 5 : ℚ), 0, (2 / 3 : ℚ), (-19 / 15 : ℚ), 0], ![(-7 / 5 : ℚ), 0, (-34 / 15 : ℚ), (-38 / 15 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, (11 / 12 : ℚ), (-7 / 6 : ℚ), (-5 / 2 : ℚ)], ![(-5 / 4 : ℚ), 0, (-23 / 12 : ℚ), (-7 / 3 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-24 / 5 : ℚ), (8 / 25 : ℚ), 0, (133 / 75 : ℚ), (-4 / 25 : ℚ)], ![(-64 / 25 : ℚ), (-24 / 5 : ℚ), (-92 / 25 : ℚ), (-109 / 75 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-78 / 17 : ℚ), (104 / 17 : ℚ), 0, (36 / 17 : ℚ), (-2 / 17 : ℚ)], ![(-41 / 17 : ℚ), (-28 / 17 : ℚ), (-7 / 2 : ℚ), (4 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-30 / 13 : ℚ), (37 / 13 : ℚ), 0, (-1 / 13 : ℚ), -4], ![(-15 / 13 : ℚ), (-12 / 13 : ℚ), (-23 / 13 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 15 : ℚ), (1 / 15 : ℚ), 0, 0, (-26 / 15 : ℚ)], ![(-19 / 15 : ℚ), (-37 / 15 : ℚ), (-28 / 15 : ℚ), (1 / 15 : ℚ), (-17 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-24 / 5 : ℚ), (8 / 25 : ℚ), 0, (8 / 25 : ℚ), (-4 / 25 : ℚ)], ![(-64 / 25 : ℚ), (-24 / 5 : ℚ), (-92 / 25 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 3 : ℚ), 5, 0, (-3 / 2 : ℚ), 0], ![(-5 / 2 : ℚ), (-7 / 3 : ℚ), (-23 / 6 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), 0, 0, -2, (1 / 2 : ℚ)], ![(-13 / 10 : ℚ), 0, -4, -2, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), 0, 0, -2, (1 / 2 : ℚ)], ![(-9 / 8 : ℚ), 0, -4, -2, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 5 : ℚ), 0, 0, -2, (1 / 10 : ℚ)], ![(-3 / 2 : ℚ), 0, -4, -2, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 7 : ℚ), 0, 0, -2, (2 / 7 : ℚ)], ![(-9 / 7 : ℚ), 0, -4, -2, (-1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, 0, -2, (-1 / 2 : ℚ)], ![(-5 / 4 : ℚ), 0, -4, -2, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 5 : ℚ), 0, 0, -2, 0], ![(-7 / 5 : ℚ), 0, -4, -2, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, 0, -2, (-5 / 2 : ℚ)], ![(-3 / 2 : ℚ), 0, -4, -2, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-116 / 23 : ℚ), (36 / 23 : ℚ), (-64 / 23 : ℚ), (49 / 23 : ℚ), 0], ![(-64 / 23 : ℚ), (-104 / 23 : ℚ), (-64 / 23 : ℚ), (-37 / 23 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 2 : ℚ), (13 / 2 : ℚ), (-19 / 8 : ℚ), (17 / 8 : ℚ), 0], ![(-19 / 8 : ℚ), (-11 / 8 : ℚ), (-19 / 8 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (5 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (-13 / 2 : ℚ)], ![0, (1 / 4 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (-13 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (13 / 4 : ℚ), (-7 / 6 : ℚ), 0, (-23 / 12 : ℚ)], ![(-7 / 6 : ℚ), (-2 / 3 : ℚ), (-7 / 6 : ℚ), 0, (-23 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-24 / 5 : ℚ), (2 / 5 : ℚ), (-13 / 5 : ℚ), (2 / 5 : ℚ), 0], ![(-13 / 5 : ℚ), (-26 / 5 : ℚ), (-13 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 9 : ℚ), (20 / 3 : ℚ), (-7 / 3 : ℚ), (-4 / 3 : ℚ), 0], ![(-7 / 3 : ℚ), (-11 / 9 : ℚ), (-7 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-64 / 25 : ℚ), 0, (18 / 25 : ℚ), (6 / 5 : ℚ), (28 / 25 : ℚ)], ![(-7 / 5 : ℚ), (6 / 25 : ℚ), (-58 / 25 : ℚ), 0, (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), (2 / 5 : ℚ), -1, -1], ![0, (-12 / 5 : ℚ), 0, 1, -1]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-57 / 50 : ℚ), (3 / 25 : ℚ), 0, (3 / 25 : ℚ)], ![(-3 / 50 : ℚ), (-54 / 25 : ℚ), 0, (21 / 50 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 10 : ℚ), (1 / 10 : ℚ), 0, (-32 / 15 : ℚ)], ![0, (-21 / 10 : ℚ), 0, (3 / 10 : ℚ), (-16 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-3 / 32 : ℚ), (41 / 48 : ℚ), (11 / 32 : ℚ), 0], ![(-39 / 32 : ℚ), 0, (-23 / 12 : ℚ), (-5 / 32 : ℚ), (3 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-3 / 32 : ℚ), (3 / 16 : ℚ), (11 / 32 : ℚ), (-37 / 16 : ℚ)], ![(-39 / 32 : ℚ), 0, (-9 / 4 : ℚ), (-5 / 32 : ℚ), (-71 / 32 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 5 : ℚ), (-1 / 10 : ℚ), (13 / 15 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)], ![(-11 / 10 : ℚ), 0, (-28 / 15 : ℚ), 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 5 : ℚ), (-3 / 40 : ℚ), (3 / 20 : ℚ), (5 / 8 : ℚ), (3 / 20 : ℚ)], ![(-47 / 40 : ℚ), 0, (-11 / 5 : ℚ), (3 / 20 : ℚ), (-19 / 40 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-18 / 7 : ℚ), 0, (2 / 3 : ℚ), (8 / 7 : ℚ), (4 / 21 : ℚ)], ![(-9 / 7 : ℚ), (2 / 7 : ℚ), (-50 / 21 : ℚ), (2 / 7 : ℚ), (2 / 21 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-32 / 25 : ℚ), (6 / 25 : ℚ), (-4 / 25 : ℚ), (-58 / 25 : ℚ)], ![(-3 / 25 : ℚ), (-58 / 25 : ℚ), 0, (6 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-110 / 51 : ℚ), (-1 / 17 : ℚ), (158 / 153 : ℚ), (25 / 51 : ℚ), (-112 / 51 : ℚ)], ![(-58 / 51 : ℚ), 0, (-260 / 153 : ℚ), (2 / 17 : ℚ), (-109 / 51 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ)], ![(-7 / 5 : ℚ), (2 / 5 : ℚ), (-14 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 2 : ℚ), (23 / 16 : ℚ), (1 / 8 : ℚ), (11 / 8 : ℚ), 0], ![(-13 / 4 : ℚ), 3, (-13 / 2 : ℚ), (7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-68 / 27 : ℚ), 0, (2 / 9 : ℚ), (-14 / 27 : ℚ), (-58 / 27 : ℚ)], ![(-37 / 27 : ℚ), (2 / 9 : ℚ), (-68 / 27 : ℚ), (-8 / 27 : ℚ), (-55 / 27 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 6 : ℚ)], ![(-5 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-41 / 25 : ℚ), (3 / 25 : ℚ), (3 / 25 : ℚ), (-109 / 25 : ℚ)], ![(-3 / 50 : ℚ), (-241 / 100 : ℚ), 0, 1, (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 10 : ℚ), (1 / 5 : ℚ), (-22 / 5 : ℚ), (-22 / 5 : ℚ)], ![0, (-49 / 20 : ℚ), 0, (-11 / 5 : ℚ), (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-55 / 32 : ℚ), (3 / 16 : ℚ), (-73 / 16 : ℚ), (-85 / 32 : ℚ)], ![(-3 / 32 : ℚ), (-5 / 2 : ℚ), 0, (-143 / 32 : ℚ), (-79 / 32 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-53 / 12 : ℚ), (20 / 3 : ℚ), (31 / 8 : ℚ), (43 / 24 : ℚ), (-1 / 12 : ℚ)], ![(-55 / 24 : ℚ), (-7 / 6 : ℚ), 0, (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), -1, -1, -6], ![0, 0, 1, -1, -3]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), -1, -1, -5], ![0, 0, 1, -1, (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 5 : ℚ), (6 / 25 : ℚ), (79 / 50 : ℚ), (6 / 25 : ℚ), (-3 / 25 : ℚ)], ![(-121 / 50 : ℚ), (-23 / 5 : ℚ), (-67 / 50 : ℚ), (-79 / 50 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-44 / 9 : ℚ), (16 / 3 : ℚ), (23 / 9 : ℚ), (-5 / 3 : ℚ), 0], ![(-8 / 3 : ℚ), (-22 / 9 : ℚ), (-11 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 10 : ℚ), (22 / 5 : ℚ), (41 / 20 : ℚ), (-3 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-49 / 20 : ℚ), -3, (-29 / 20 : ℚ), (-3 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (22 / 3 : ℚ), (10 / 3 : ℚ), 0, 0], ![-2, (-1 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 50 : ℚ), (-93 / 100 : ℚ), (-162 / 25 : ℚ), (-221 / 100 : ℚ)], ![(-3 / 100 : ℚ), 0, (99 / 100 : ℚ), (-53 / 10 : ℚ), (-43 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (13 / 4 : ℚ), 0, 0, -4], ![-1, (-1 / 2 : ℚ), 0, 0, -2]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), -1, -1, -6], ![0, 0, 0, -1, (-16 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-73 / 17 : ℚ), (2 / 17 : ℚ), (53 / 34 : ℚ), (24 / 17 : ℚ), (-1 / 17 : ℚ)], ![(-75 / 34 : ℚ), (-73 / 17 : ℚ), (2 / 17 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 4 : ℚ), (29 / 4 : ℚ), (25 / 16 : ℚ), (-19 / 16 : ℚ), 0], ![(-35 / 16 : ℚ), (-11 / 16 : ℚ), (1 / 8 : ℚ), (-19 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-58 / 13 : ℚ), (80 / 13 : ℚ), (28 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ)], ![(-29 / 13 : ℚ), (-20 / 13 : ℚ), (4 / 13 : ℚ), (-1 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (36 / 5 : ℚ), (11 / 5 : ℚ), 0, 0], ![-2, (-3 / 5 : ℚ), (2 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-101 / 24 : ℚ), (1 / 24 : ℚ), (5 / 4 : ℚ), (-25 / 16 : ℚ), (-1 / 24 : ℚ)], ![(-17 / 8 : ℚ), (-101 / 24 : ℚ), (1 / 24 : ℚ), (-37 / 24 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (1 / 2 : ℚ), 0, 0, -4], ![-1, -2, 0, 0, -2]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (1 / 4 : ℚ), 0, 0, (-11 / 4 : ℚ)], ![-1, -2, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (7 / 2 : ℚ), 0, 0, -4], ![-1, (-1 / 2 : ℚ), 0, 0, -2]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (1 / 4 : ℚ), 0, 0, (-9 / 4 : ℚ)], ![(-5 / 4 : ℚ), (-15 / 4 : ℚ), 0, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), -4, (-7 / 4 : ℚ)], ![(-5 / 4 : ℚ), (-5 / 2 : ℚ), 0, -2, (-27 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 18 : ℚ), (55 / 18 : ℚ), (-1 / 18 : ℚ), (-17 / 9 : ℚ), (-19 / 18 : ℚ)], ![(-7 / 6 : ℚ), (-7 / 9 : ℚ), 0, (-67 / 36 : ℚ), -1]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 4 : ℚ), 0], ![(-9 / 4 : ℚ), (-13 / 2 : ℚ), (-5 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![(-23 / 10 : ℚ), (-23 / 5 : ℚ), (-13 / 10 : ℚ), (-1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (2 / 3 : ℚ), (2 / 3 : ℚ), 0, 0], ![-2, -4, -1, 0, 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 11 : ℚ), (1 / 11 : ℚ), (-63 / 11 : ℚ), (-51 / 22 : ℚ)], ![(-1 / 22 : ℚ), 0, 1, (-109 / 22 : ℚ), (-49 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 3 : ℚ), (20 / 3 : ℚ), (-3 / 2 : ℚ), (-1 / 3 : ℚ), 0], ![(-13 / 6 : ℚ), (-7 / 6 : ℚ), (-3 / 2 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-4, (48 / 7 : ℚ), (-11 / 7 : ℚ), 0, 0], ![-2, (-6 / 7 : ℚ), (-11 / 7 : ℚ), 0, 0]] }
]

theorem conicDetC34_checked : conicDetC34.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
