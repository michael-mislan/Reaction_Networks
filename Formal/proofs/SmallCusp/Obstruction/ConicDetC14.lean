import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC14 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (-1 / 7 : ℚ), 0, (-3 / 14 : ℚ), (-3 / 7 : ℚ)], ![(-3 / 14 : ℚ), (-2 / 7 : ℚ), 0, 0, (10 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, -1, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, -2, 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), 0, 0], ![0, 0, (-12 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, -2, 0, 0], ![(-1 / 4 : ℚ), -2, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-2 / 3 : ℚ), 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 34 : ℚ), (-20 / 17 : ℚ), -2, 0, (-32 / 17 : ℚ)], ![(-3 / 17 : ℚ), (-40 / 17 : ℚ), -4, (-3 / 34 : ℚ), (-5 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-14 / 11 : ℚ), (-21 / 11 : ℚ), (1 / 11 : ℚ), (-31 / 11 : ℚ)], ![(-15 / 11 : ℚ), (-28 / 11 : ℚ), (-42 / 11 : ℚ), 0, (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-7 / 3 : ℚ), 0, -3], ![(-2 / 3 : ℚ), (-8 / 3 : ℚ), (-14 / 3 : ℚ), 0, -3]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 13 : ℚ), (-24 / 13 : ℚ), 0, (-84 / 13 : ℚ), (-72 / 13 : ℚ)], ![(-36 / 13 : ℚ), (-48 / 13 : ℚ), 0, (12 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 8 : ℚ), (-3 / 2 : ℚ), 0, 0], ![0, (1 / 4 : ℚ), -3, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), 0, (-12 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, 0, (-24 / 5 : ℚ), (4 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 17 : ℚ), (4 / 17 : ℚ), (-56 / 17 : ℚ), 0, 0], ![(8 / 17 : ℚ), (8 / 17 : ℚ), (-112 / 17 : ℚ), (16 / 17 : ℚ), (8 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), 0, (-12 / 5 : ℚ), 0, 0], ![0, 0, (-24 / 5 : ℚ), (4 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-1 / 9 : ℚ), (13 / 9 : ℚ), 0, (-13 / 9 : ℚ)], ![(-13 / 9 : ℚ), (-7 / 3 : ℚ), 0, (-10 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-1 / 18 : ℚ), 0, (-23 / 18 : ℚ), (-5 / 9 : ℚ)], ![(-1 / 18 : ℚ), (-8 / 9 : ℚ), (-13 / 9 : ℚ), (-47 / 18 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-6 / 25 : ℚ), 0, (-116 / 75 : ℚ), (-326 / 75 : ℚ)], ![(-6 / 25 : ℚ), (-88 / 75 : ℚ), (-68 / 75 : ℚ), (-10 / 3 : ℚ), (-154 / 75 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (-8 / 17 : ℚ), 2, 0, (-124 / 17 : ℚ)], ![(-42 / 17 : ℚ), (-58 / 17 : ℚ), 0, (-8 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 17 : ℚ), (-4 / 17 : ℚ), 0, (-10 / 17 : ℚ), -6], ![(-4 / 17 : ℚ), (-36 / 17 : ℚ), (-48 / 17 : ℚ), (-24 / 17 : ℚ), (-100 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-11 / 6 : ℚ), (-5 / 3 : ℚ)], ![(-1 / 2 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), 2, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-17 / 12 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (3 / 2 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), (7 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), (7 / 4 : ℚ)], ![(-7 / 4 : ℚ), (-11 / 4 : ℚ), (-1 / 2 : ℚ), (7 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 24 : ℚ), 0, (-29 / 24 : ℚ), (-17 / 4 : ℚ)], ![(-1 / 8 : ℚ), (-17 / 8 : ℚ), (-1 / 24 : ℚ), (5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-11 / 6 : ℚ), (-31 / 6 : ℚ)], ![(-1 / 2 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), 2, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 24 : ℚ), 0, (-29 / 24 : ℚ), (-101 / 24 : ℚ)], ![(-1 / 8 : ℚ), (-17 / 8 : ℚ), (-1 / 24 : ℚ), (5 / 4 : ℚ), (-13 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-4 / 3 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 6 : ℚ), (7 / 6 : ℚ)], ![(-7 / 6 : ℚ), (-13 / 6 : ℚ), (-3 / 2 : ℚ), 0, (7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ), (-56 / 11 : ℚ)], ![(-6 / 11 : ℚ), (-28 / 11 : ℚ), (-2 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ), (-58 / 11 : ℚ)], ![(-6 / 11 : ℚ), (-28 / 11 : ℚ), (-2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ), (-54 / 11 : ℚ)], ![(-6 / 11 : ℚ), (-28 / 11 : ℚ), (-2 / 11 : ℚ), (2 / 11 : ℚ), (-26 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-11 / 10 : ℚ)], ![(-1 / 20 : ℚ), (-41 / 20 : ℚ), (-1 / 20 : ℚ), (23 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-4 / 3 : ℚ), (4 / 3 : ℚ)], ![(-3 / 2 : ℚ), (-5 / 2 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ), (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ), (-9 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (-2 / 3 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 24 : ℚ), 0, (-9 / 8 : ℚ), (-101 / 24 : ℚ)], ![(-1 / 8 : ℚ), (-17 / 8 : ℚ), (-1 / 24 : ℚ), (-1 / 3 : ℚ), (-13 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 3 : ℚ)], ![(-4 / 9 : ℚ), (-22 / 9 : ℚ), (-4 / 9 : ℚ), (8 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -6], ![(-2 / 3 : ℚ), (-8 / 3 : ℚ), (-2 / 3 : ℚ), (4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-58 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-28 / 13 : ℚ), (-2 / 13 : ℚ), (4 / 13 : ℚ), (-18 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), 0, (13 / 22 : ℚ), (-50 / 11 : ℚ)], ![(-17 / 22 : ℚ), (-25 / 11 : ℚ), (-31 / 22 : ℚ), (1 / 2 : ℚ), (-49 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-1 / 9 : ℚ), (7 / 36 : ℚ), (47 / 36 : ℚ), (-31 / 6 : ℚ)], ![(-55 / 36 : ℚ), (-91 / 36 : ℚ), 0, (25 / 36 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (2 / 3 : ℚ), (-29 / 6 : ℚ)], ![-1, (-5 / 2 : ℚ), (-3 / 2 : ℚ), (2 / 3 : ℚ), (-29 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), (-4 / 15 : ℚ), 0, (-88 / 15 : ℚ), (-28 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-14 / 5 : ℚ), (-4 / 15 : ℚ), (4 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), (-4 / 15 : ℚ), 0, (-28 / 5 : ℚ), (-16 / 3 : ℚ)], ![(-4 / 5 : ℚ), (-14 / 5 : ℚ), (-4 / 15 : ℚ), 0, (-52 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, (-72 / 11 : ℚ), (-38 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-34 / 11 : ℚ), (-4 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), 0, (-50 / 9 : ℚ), (-46 / 9 : ℚ)], ![(-2 / 3 : ℚ), (-8 / 3 : ℚ), (-2 / 9 : ℚ), (2 / 9 : ℚ), (-26 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-53 / 12 : ℚ), (-9 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (-13 / 12 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), 2, (1 / 9 : ℚ), -2, (-13 / 9 : ℚ)], ![-2, 0, 0, 0, (-11 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 14 : ℚ), 2, (1 / 7 : ℚ), -2, (-34 / 7 : ℚ)], ![-2, 0, 0, 0, (-16 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-6 / 7 : ℚ), 0, (-2 / 7 : ℚ)], ![0, 0, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 14 : ℚ), 2, (1 / 7 : ℚ), -2, (-31 / 7 : ℚ)], ![-2, 0, 0, 0, (-30 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (3 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0], ![-1, (-1 / 4 : ℚ), (-13 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 7 : ℚ), (5 / 7 : ℚ), -1, (-1 / 7 : ℚ), (-22 / 7 : ℚ)], ![(-6 / 7 : ℚ), (-1 / 7 : ℚ), (-18 / 7 : ℚ), 0, (-8 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (21 / 10 : ℚ), (1 / 10 : ℚ), (-3 / 2 : ℚ), (-34 / 5 : ℚ)], ![(-23 / 10 : ℚ), 0, 0, (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 14 : ℚ), (6 / 7 : ℚ), -1, (-1 / 14 : ℚ), (-55 / 28 : ℚ)], ![(-13 / 14 : ℚ), (-1 / 14 : ℚ), (-16 / 7 : ℚ), 0, (-27 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, (-17 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-61 / 10 : ℚ), (-11 / 10 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), 0, (-13 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 13 : ℚ), 0, (-20 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-17 / 26 : ℚ), (-7 / 2 : ℚ), (-15 / 13 : ℚ), (-19 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-5 / 12 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(1 / 6 : ℚ), (-1 / 12 : ℚ), (-9 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, 0, (-9 / 2 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 2 : ℚ), (-7 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), -5, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), -2, (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, 0, -6, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 3 : ℚ), (-14 / 9 : ℚ), (-2 / 9 : ℚ), (-1 / 9 : ℚ)], ![(4 / 9 : ℚ), (-2 / 9 : ℚ), (-16 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), -1, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, -5, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (12 / 5 : ℚ), (2 / 5 : ℚ), (-36 / 5 : ℚ), -6], ![(-16 / 5 : ℚ), 0, 0, 0, (-28 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-2 / 11 : ℚ), (-7 / 11 : ℚ), 0, (-1 / 11 : ℚ)], ![(-1 / 22 : ℚ), (-1 / 11 : ℚ), (-48 / 11 : ℚ), (1 / 22 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), (-8 / 5 : ℚ), (4 / 15 : ℚ), 0, (-4 / 15 : ℚ)], ![(4 / 5 : ℚ), (-52 / 15 : ℚ), 0, (4 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, (-7 / 12 : ℚ), (1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-5 / 12 : ℚ), (-1 / 3 : ℚ), (-5 / 12 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 12 : ℚ), (1 / 2 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (-5 / 16 : ℚ), (-3 / 16 : ℚ), (-3 / 8 : ℚ)], ![(-3 / 16 : ℚ), (-1 / 16 : ℚ), (3 / 8 : ℚ), 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 2 : ℚ), (1 / 12 : ℚ), (1 / 4 : ℚ), 0], ![(1 / 4 : ℚ), (-13 / 12 : ℚ), 0, (1 / 3 : ℚ), (41 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-5 / 9 : ℚ), 0, (-1 / 9 : ℚ), 0], ![(2 / 9 : ℚ), (-11 / 9 : ℚ), (2 / 9 : ℚ), 0, (1 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (3 / 2 : ℚ), (3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (3 / 2 : ℚ), (3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, -3, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, -3, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, -3, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), 0], ![0, (-7 / 12 : ℚ), (1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, (-7 / 6 : ℚ), (1 / 2 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, (1 / 6 : ℚ), 0, 0], ![(1 / 2 : ℚ), (-13 / 6 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 24 : ℚ)], ![0, (-7 / 12 : ℚ), (1 / 4 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-5 / 12 : ℚ), (-5 / 12 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 12 : ℚ), (1 / 2 : ℚ), (-3 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), 0, (-11 / 6 : ℚ)], ![0, (-7 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, -2, (2 / 7 : ℚ), 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -1, (-3 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-3 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), -2, (1 / 2 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-10 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-10 / 3 : ℚ), 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-10 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-28 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), 0, (-2 / 11 : ℚ)], ![0, (-28 / 11 : ℚ), (4 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-28 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-28 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-9 / 11 : ℚ), (-7 / 11 : ℚ), (-2 / 11 : ℚ), (-3 / 11 : ℚ)], ![(-3 / 11 : ℚ), -2, (4 / 11 : ℚ), 0, (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), -1, (1 / 5 : ℚ), (1 / 5 : ℚ), (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 2 : ℚ), 0, (11 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 10 : ℚ), 0, (-1 / 10 : ℚ), 0], ![(1 / 10 : ℚ), (-4 / 5 : ℚ), (3 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-7 / 2 : ℚ), (11 / 6 : ℚ), (-11 / 6 : ℚ), 0], ![(1 / 2 : ℚ), (-22 / 3 : ℚ), (11 / 6 : ℚ), (-11 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, -1], ![(-1 / 3 : ℚ), (-8 / 3 : ℚ), 0, 0, 3]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), 0], ![(-1 / 6 : ℚ), -3, (1 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 21 : ℚ), (-2 / 7 : ℚ), (-1 / 3 : ℚ), (-2 / 21 : ℚ), 0], ![0, (-2 / 3 : ℚ), (6 / 7 : ℚ), (16 / 7 : ℚ), (1 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), 0], ![(-1 / 6 : ℚ), -2, (1 / 6 : ℚ), (3 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, -2, 0, 4, 2]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![0, -2, 0, 4, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -1, 0, (1 / 3 : ℚ), 0], ![0, (-7 / 3 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-16 / 5 : ℚ), -1, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 7 : ℚ), 0, (-6 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (-26 / 7 : ℚ), (-10 / 7 : ℚ), (-10 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, 0], ![(1 / 3 : ℚ), (-14 / 3 : ℚ), (-5 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, (-4 / 5 : ℚ)], ![(2 / 5 : ℚ), (-16 / 5 : ℚ), 0, (4 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, 0], ![(2 / 5 : ℚ), (-16 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (-10 / 3 : ℚ), 0, (2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, 0], ![(2 / 5 : ℚ), (-16 / 5 : ℚ), 0, (4 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), 0, 0, (-7 / 18 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), -2, (-1 / 18 : ℚ), (1 / 18 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-16 / 7 : ℚ), (-12 / 7 : ℚ)], ![(-8 / 7 : ℚ), (-22 / 7 : ℚ), 0, (-6 / 7 : ℚ), (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (3 / 2 : ℚ), (1 / 12 : ℚ), (-23 / 6 : ℚ), (-11 / 6 : ℚ)], ![(-7 / 4 : ℚ), (-5 / 12 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-10 / 7 : ℚ), (-6 / 7 : ℚ), (-8 / 7 : ℚ), 0], ![(-2 / 7 : ℚ), (-34 / 7 : ℚ), (-6 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-3 / 2 : ℚ), -1], ![-1, -3, 0, (-3 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 2 : ℚ), 0, (1 / 6 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 12 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), -1, (-1 / 3 : ℚ)], ![0, (1 / 3 : ℚ), -1, (-7 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xx, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (1 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 2 : ℚ), 1, 0, (1 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xx, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(-1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xx, .yy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-5 / 6 : ℚ), (-1 / 2 : ℚ)], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (-11 / 12 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -1, 0, (1 / 3 : ℚ), (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (-7 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xx, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), -1, (-1 / 5 : ℚ), 0, (-4 / 5 : ℚ)], ![(-3 / 5 : ℚ), (2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0, 2]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-4 / 5 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xx, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(-1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-8 / 5 : ℚ), 0, 0, (-16 / 5 : ℚ)], ![(-8 / 5 : ℚ), (-8 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 8 : ℚ), (-1 / 8 : ℚ), 0, -1], ![(-3 / 8 : ℚ), (-3 / 8 : ℚ), (-1 / 8 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-17 / 7 : ℚ), 0, (1 / 7 : ℚ), (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-33 / 7 : ℚ), (-1 / 7 : ℚ), (1 / 14 : ℚ), (22 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-25 / 11 : ℚ), 0, (1 / 11 : ℚ), (-8 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-49 / 11 : ℚ), (-1 / 11 : ℚ), (1 / 22 : ℚ), (12 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, (1 / 2 : ℚ), 0], ![(-7 / 20 : ℚ), -5, (-1 / 5 : ℚ), (2 / 5 : ℚ), (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-8 / 3 : ℚ), (1 / 6 : ℚ), (3 / 4 : ℚ), (-25 / 6 : ℚ)], ![(-5 / 8 : ℚ), (-31 / 6 : ℚ), 0, (2 / 3 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-8 / 3 : ℚ), 0, 0, (-28 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-46 / 9 : ℚ), (-2 / 9 : ℚ), (-1 / 9 : ℚ), (38 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), 0, (-18 / 11 : ℚ)], ![(-3 / 11 : ℚ), (-25 / 11 : ℚ), (-3 / 11 : ℚ), (-1 / 11 : ℚ), (20 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0, (-3 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, 0, (-52 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (-14 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), 0, 0, (-56 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-26 / 9 : ℚ), (-4 / 9 : ℚ), (-2 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 2, (1 / 3 : ℚ), (1 / 6 : ℚ), -2], ![-2, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 2, (1 / 3 : ℚ), (1 / 2 : ℚ), (-19 / 3 : ℚ)], ![(-7 / 3 : ℚ), (-1 / 3 : ℚ), 0, (1 / 3 : ℚ), -3]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (8 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ), (-22 / 3 : ℚ)], ![(-10 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-16 / 11 : ℚ), (-28 / 11 : ℚ), 0, 0], ![(8 / 11 : ℚ), (-20 / 11 : ℚ), (-30 / 11 : ℚ), (4 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-16 / 11 : ℚ), (-28 / 11 : ℚ), 0, 0], ![(8 / 11 : ℚ), (-20 / 11 : ℚ), (-30 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![0, (-4 / 5 : ℚ), (-6 / 5 : ℚ), (6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 6 : ℚ), -1], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-7 / 12 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-3 / 2 : ℚ)], ![(-3 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-4 / 3 : ℚ), -2, 0, (-2 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), -2, 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), (-8 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), -2, -2, 0, (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (1 / 7 : ℚ), (-2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .xy), (.xx, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 3 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ)], ![0, (-4 / 3 : ℚ), (-14 / 9 : ℚ), (-4 / 3 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ), 0], ![(2 / 3 : ℚ), (1 / 3 : ℚ), 0, (-4 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), 0], ![0, 1, 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), (1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (1 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-6 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(-4 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-3 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (2 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, -2, (1 / 5 : ℚ)], ![(3 / 5 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, -2, (2 / 5 : ℚ)], ![(3 / 5 : ℚ), 0, 0, -2, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, -2, 0, -1], ![(-1 / 2 : ℚ), 0, -4, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![(1 / 2 : ℚ), 0, 0, -2, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, -2, -1], ![(1 / 6 : ℚ), 0, 0, -2, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, -2, 0], ![(1 / 3 : ℚ), 0, 0, -2, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, -2, 0], ![(1 / 3 : ℚ), 0, 0, -2, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, -2, 0], ![(1 / 3 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, 0, 0, (-7 / 6 : ℚ)], ![(-1 / 3 : ℚ), 0, -2, 0, (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, 0, 0, (-7 / 6 : ℚ)], ![(-1 / 3 : ℚ), 0, -2, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, -1], ![(-1 / 2 : ℚ), 0, -2, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(-1 / 4 : ℚ), 0, -2, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, 0, 0, 1], ![(-4 / 3 : ℚ), 0, -2, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, 0, 0, (-13 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, -2, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, 0, 0, (-13 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, -2, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, 0, 0, -4], ![(-2 / 3 : ℚ), 0, -2, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ), 0], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), -2, 2, 0, -1], ![-2, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 2, (1 / 2 : ℚ), 0], ![-2, 0, 0, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, 2, (1 / 6 : ℚ), (7 / 6 : ℚ)], ![-2, 0, 0, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), -2, 2, (2 / 3 : ℚ), (-14 / 3 : ℚ)], ![-2, 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, 2, 0, -4], ![-2, 0, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 3 : ℚ), (1 / 12 : ℚ), (-5 / 12 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 4 : ℚ), (1 / 12 : ℚ), 0, (1 / 2 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-2 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), (7 / 6 : ℚ), (-2 / 3 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (2 / 5 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, (-1 / 3 : ℚ), (1 / 3 : ℚ)], ![(-1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 3 : ℚ), (1 / 12 : ℚ), (-5 / 12 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (1 / 12 : ℚ), 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ)], ![0, (1 / 12 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![0, (2 / 5 : ℚ), (-4 / 5 : ℚ), (6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ), 0], ![0, 1, (-1 / 4 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (2 / 5 : ℚ), (-4 / 5 : ℚ), (2 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, (1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 3 : ℚ), (-4 / 3 : ℚ), -2], ![-1, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ)], ![0, (2 / 5 : ℚ), (-4 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (5 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (2 / 3 : ℚ), (-1 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-9 / 4 : ℚ)], ![0, 1, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 4 : ℚ)], ![0, 1, (-1 / 2 : ℚ), 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)], ![0, 1, (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), -1, 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), (-3 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0], ![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-3 / 10 : ℚ), 0, 0, (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), (1 / 10 : ℚ), 0, 0, (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-3 / 20 : ℚ), (-3 / 20 : ℚ), (-1 / 10 : ℚ), 0], ![(-1 / 20 : ℚ), (1 / 10 : ℚ), (-3 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-2 / 3 : ℚ), (1 / 6 : ℚ), (-7 / 6 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (2 / 5 : ℚ), (-4 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .xy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0], ![0, (2 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-7 / 3 : ℚ), (1 / 2 : ℚ)], ![(5 / 6 : ℚ), 0, (1 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 16 : ℚ), (-1 / 16 : ℚ), (-35 / 16 : ℚ), (7 / 16 : ℚ)], ![(9 / 16 : ℚ), (-1 / 16 : ℚ), 0, (-35 / 16 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 2 : ℚ), 0], ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-5 / 2 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, -3, 0], ![0, 0, (1 / 2 : ℚ), -3, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), 0, 0, (-22 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, 0, (4 / 7 : ℚ), (-22 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-21 / 10 : ℚ), (-1 / 20 : ℚ), 0, (-6 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-21 / 10 : ℚ), 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-12 / 5 : ℚ), (-12 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, 0], ![(-1 / 4 : ℚ), (-5 / 2 : ℚ), (-9 / 4 : ℚ), 0, (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 2 : ℚ), (-1 / 4 : ℚ), 0, -5], ![(-1 / 2 : ℚ), (-5 / 2 : ℚ), (-5 / 2 : ℚ), 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-22 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-48 / 7 : ℚ)], ![(-8 / 7 : ℚ), (-22 / 7 : ℚ), (-22 / 7 : ℚ), 0, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-5 / 2 : ℚ), 2, 0, -2], ![-2, (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), (5 / 2 : ℚ), 0, 0], ![(-5 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-12 / 5 : ℚ), 2, 0, (-27 / 5 : ℚ)], ![(-11 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-10 / 3 : ℚ), (8 / 3 : ℚ), 0, (-22 / 3 : ℚ)], ![(-10 / 3 : ℚ), (-10 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![(2 / 5 : ℚ), 0, (-6 / 5 : ℚ), (4 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![0, 0, (-4 / 5 : ℚ), (6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, 0], ![(-1 / 2 : ℚ), -1, 0, (3 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, (-2 / 3 : ℚ), (2 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-4 / 3 : ℚ), 0, (2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 10 : ℚ), (-4 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (1 / 10 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0, 0], ![(4 / 5 : ℚ), 0, (-8 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0, 0], ![(4 / 5 : ℚ), 0, (-8 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), 0, (-6 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 2 : ℚ), 0, -1, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-4 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-4 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ)], ![0, 0, (-4 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -1, 0, 0], ![0, 0, -1, 0, (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![0, 0, (-4 / 3 : ℚ), 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0, 0]] }
]

theorem conicDetC14_checked : conicDetC14.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
