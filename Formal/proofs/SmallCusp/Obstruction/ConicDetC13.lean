import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC13 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, (1 / 2 : ℚ), 4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 0, -4, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 0, 4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![0, 0, 0, -4, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![0, 0, 0, -4, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, -4, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, 0, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, 0, -4, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, -4, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 0, -4, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 0, 4, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![0, 0, 0, -4, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 8 : ℚ)], ![0, 0, 0, -4, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 2 : ℚ), 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), -4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-28 / 17 : ℚ), 0, 0], ![(4 / 17 : ℚ), (4 / 17 : ℚ), (-8 / 17 : ℚ), (-132 / 17 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(4 / 9 : ℚ), (4 / 9 : ℚ), 0, (-68 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (-38 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-41 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (-30 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-10 / 3 : ℚ)], ![(-4 / 9 : ℚ), (-13 / 9 : ℚ), (-40 / 9 : ℚ), 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 4, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 3 : ℚ), 4, (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 2 : ℚ), 4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, -4, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 4, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![0, 0, -4, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, -2, -5], ![-2, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 8 : ℚ), 0, (3 / 8 : ℚ), 0], ![(3 / 8 : ℚ), 0, (-19 / 4 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), -4, (1 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 2 : ℚ)], ![0, 0, -4, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 6 : ℚ)], ![0, (-1 / 3 : ℚ), -4, (1 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-21 / 5 : ℚ), (-6 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), 0, (-13 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-56 / 13 : ℚ), (-17 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 12 : ℚ), (-31 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-7 / 12 : ℚ), (-59 / 12 : ℚ), (-1 / 2 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, -5, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-10 / 3 : ℚ)], ![(-4 / 9 : ℚ), (-13 / 9 : ℚ), (-40 / 9 : ℚ), 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 9 : ℚ), 0, (-8 / 9 : ℚ), (-8 / 9 : ℚ)], ![0, 0, (-20 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-56 / 17 : ℚ), (-28 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-76 / 17 : ℚ), (-24 / 17 : ℚ), (-24 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 3 : ℚ), 0, (-20 / 3 : ℚ), (-11 / 3 : ℚ)], ![-3, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 3 : ℚ), (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), 0, (-44 / 9 : ℚ), 0, (-8 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, (5 / 8 : ℚ), 0], ![(1 / 2 : ℚ), (-1 / 4 : ℚ), (-23 / 4 : ℚ), (3 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -4, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 8 : ℚ), (-1 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (-17 / 4 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -4, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -4, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -4, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -4, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -4, 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -4, 0, 0, (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![(1 / 2 : ℚ), -5, (1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-28 / 5 : ℚ), -1, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-32 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-14 / 3 : ℚ), (-2 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 3 : ℚ), (-13 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, -2], ![(-2 / 3 : ℚ), (-14 / 3 : ℚ), 0, (-2 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (11 / 5 : ℚ), (-28 / 5 : ℚ), -3], ![(-13 / 5 : ℚ), 0, (9 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (-36 / 5 : ℚ), (-6 / 5 : ℚ), (4 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, -6, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-8 / 7 : ℚ), 0, 0, (-10 / 7 : ℚ)], ![(-6 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (12 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-3 / 4 : ℚ), (1 / 12 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-7 / 12 : ℚ), (1 / 6 : ℚ), 0, (1 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0], ![0, 1, (-7 / 4 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(-1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 23 : ℚ), (-63 / 46 : ℚ), (1 / 46 : ℚ), 0, (57 / 46 : ℚ)], ![(-61 / 46 : ℚ), (1 / 23 : ℚ), 0, (-1 / 23 : ℚ), (21 / 46 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -1, (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (1 / 3 : ℚ), -1, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-6 / 11 : ℚ), (-10 / 11 : ℚ), (-6 / 11 : ℚ), 0], ![(-2 / 11 : ℚ), (4 / 11 : ℚ), (-24 / 11 : ℚ), (-6 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -1, 0, 0, (-5 / 3 : ℚ)], ![-1, -1, (-1 / 3 : ℚ), 0, 2]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-12 / 11 : ℚ), 0, (4 / 11 : ℚ), (-16 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-6 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ)], ![(-6 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, 0], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, (5 / 3 : ℚ)], ![-2, (-5 / 3 : ℚ), (-1 / 3 : ℚ), 0, (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-7 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ)], ![(-7 / 5 : ℚ), (-7 / 5 : ℚ), 0, (1 / 5 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-14 / 5 : ℚ), (-4 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-6 / 5 : ℚ), 0, 0, -2], ![(-6 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-24 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (14 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-23 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), (-9 / 5 : ℚ)], ![(-17 / 10 : ℚ), (-23 / 5 : ℚ), (-1 / 5 : ℚ), 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-9 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, 0], ![(-1 / 4 : ℚ), -5, 0, (-1 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-40 / 17 : ℚ), 0, 0, (-64 / 17 : ℚ)], ![(-9 / 17 : ℚ), (-80 / 17 : ℚ), 0, (-3 / 17 : ℚ), (-5 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-30 / 11 : ℚ), 0, 0, (-72 / 11 : ℚ)], ![(-34 / 11 : ℚ), (-60 / 11 : ℚ), 0, (-4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-8 / 3 : ℚ), (-2 / 3 : ℚ), 0, -6], ![(-4 / 3 : ℚ), (-16 / 3 : ℚ), (-4 / 3 : ℚ), 0, -6]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), 0, 0, (-23 / 13 : ℚ)], ![(-6 / 13 : ℚ), (-32 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ), (25 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-5 / 3 : ℚ)], ![(-1 / 2 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)], ![(-3 / 5 : ℚ), (-13 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), 0, 0, (-64 / 13 : ℚ)], ![(-6 / 13 : ℚ), (-32 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ), (-18 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, 0, (-72 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-34 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (-21 / 4 : ℚ)], ![(-3 / 4 : ℚ), (-11 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-21 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 2, (1 / 7 : ℚ), (2 / 7 : ℚ), -2], ![-2, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (1 / 2 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(-3 / 4 : ℚ), (-1 / 4 : ℚ), (-13 / 4 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 2 : ℚ), (-5 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ)], ![(1 / 3 : ℚ), (-1 / 6 : ℚ), -5, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (7 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (-20 / 3 : ℚ)], ![-3, 0, 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 2 : ℚ), (-7 / 6 : ℚ), (-5 / 2 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), -5, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), 0, 0, (-20 / 13 : ℚ), (-24 / 13 : ℚ)], ![(-12 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (24 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), 0, 0, (-20 / 13 : ℚ), (-28 / 13 : ℚ)], ![(-12 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (24 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ)], ![0, (-7 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (1 / 12 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 12 : ℚ), 0, (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 12 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (-4 / 3 : ℚ)], ![(-7 / 12 : ℚ), 0, (1 / 12 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), 0, (4 / 11 : ℚ), (-16 / 11 : ℚ), (-20 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-4 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ), (-20 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-6 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0], ![0, (-14 / 5 : ℚ), (-4 / 5 : ℚ), 0, (12 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-6 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![0, (-14 / 5 : ℚ), (-4 / 5 : ℚ), 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ), -2], ![(-6 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, 0, (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-16 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), 0, (4 / 9 : ℚ), (4 / 9 : ℚ), (-28 / 9 : ℚ)], ![(-4 / 3 : ℚ), (-14 / 9 : ℚ), 0, 0, (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), -2, (-4 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)], ![0, -6, (-4 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), -1, (-1 / 4 : ℚ)], ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (-9 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 17 : ℚ), (-18 / 17 : ℚ), (-14 / 17 : ℚ), (2 / 17 : ℚ), (-18 / 17 : ℚ)], ![(-14 / 17 : ℚ), (4 / 17 : ℚ), 0, 0, (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ), 0], ![0, (5 / 7 : ℚ), 0, -2, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), -1, (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)], ![(-7 / 8 : ℚ), (3 / 8 : ℚ), (-1 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ), 0], ![0, (2 / 7 : ℚ), 0, -2, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 17 : ℚ), (-18 / 17 : ℚ), (-14 / 17 : ℚ), (2 / 17 : ℚ), (-32 / 17 : ℚ)], ![(-14 / 17 : ℚ), (4 / 17 : ℚ), 0, 0, (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), -1, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (-9 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (-6 / 17 : ℚ), (6 / 17 : ℚ), (-18 / 17 : ℚ), (-12 / 17 : ℚ)], ![0, (6 / 17 : ℚ), (12 / 17 : ℚ), (-36 / 17 : ℚ), (18 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (2 / 5 : ℚ), (4 / 5 : ℚ), (-12 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 8 : ℚ)], ![(-3 / 8 : ℚ), (5 / 8 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(2 / 3 : ℚ), (2 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), (-6 / 5 : ℚ), 0], ![0, (2 / 5 : ℚ), (4 / 5 : ℚ), (-12 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (2 / 5 : ℚ), 0, (-12 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ), (-1 / 5 : ℚ)], ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, (-16 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, 0, (-9 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, -2, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, 0, 0, (-7 / 6 : ℚ)], ![(-1 / 2 : ℚ), 0, -2, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, 0, (-9 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, -2, 0, (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(-1 / 4 : ℚ), 0, -2, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, (-17 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, (-17 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, -2, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, (-17 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, -2, 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, (-6 / 7 : ℚ), 0], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 20 : ℚ), -2, 2, (1 / 10 : ℚ), (-27 / 20 : ℚ)], ![-2, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 2, (1 / 4 : ℚ), 0], ![-2, 0, 0, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, 2, (3 / 2 : ℚ), (7 / 6 : ℚ)], ![-2, 0, 0, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 14 : ℚ), -2, 2, (1 / 7 : ℚ), (-30 / 7 : ℚ)], ![-2, 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, (-6 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 14 : ℚ), -2, 2, (1 / 7 : ℚ), (-29 / 7 : ℚ)], ![-2, 0, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-7 / 6 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-1 / 4 : ℚ), (1 / 36 : ℚ), (-11 / 36 : ℚ), (-7 / 36 : ℚ)], ![(-7 / 36 : ℚ), (29 / 36 : ℚ), 0, (13 / 36 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-23 / 12 : ℚ), (1 / 4 : ℚ), (-11 / 6 : ℚ), (11 / 6 : ℚ)], ![(-11 / 6 : ℚ), (1 / 12 : ℚ), 0, (11 / 6 : ℚ), (11 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ), 0], ![0, (1 / 6 : ℚ), (-7 / 6 : ℚ), (1 / 2 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-3 / 8 : ℚ), (1 / 24 : ℚ), (-11 / 24 : ℚ), (-2 / 3 : ℚ)], ![(-7 / 24 : ℚ), (1 / 12 : ℚ), 0, (13 / 24 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-2 / 3 : ℚ), (-1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-3 / 2 : ℚ), (1 / 3 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-1 / 4 : ℚ), (1 / 36 : ℚ), (-1 / 4 : ℚ), (-7 / 36 : ℚ)], ![(-7 / 36 : ℚ), (29 / 36 : ℚ), 0, (1 / 18 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, (1 / 3 : ℚ), (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), 0], ![0, (4 / 11 : ℚ), (-28 / 11 : ℚ), (4 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (4 / 11 : ℚ), (-28 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (4 / 11 : ℚ), (-28 / 11 : ℚ), (4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![(-1 / 12 : ℚ), (11 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (3 / 5 : ℚ), (-12 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-1 / 18 : ℚ), (-1 / 6 : ℚ), (-17 / 36 : ℚ), 0], ![0, (2 / 9 : ℚ), (-7 / 18 : ℚ), (7 / 9 : ℚ), (1 / 36 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 1, -2, 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![0, 1, -2, 0, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 7 : ℚ), (-6 / 7 : ℚ), 0, 0], ![(2 / 7 : ℚ), (4 / 7 : ℚ), (-16 / 7 : ℚ), 0, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-8 / 7 : ℚ), 0, 0], ![(4 / 7 : ℚ), (4 / 7 : ℚ), (-20 / 7 : ℚ), 0, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 7 : ℚ), (-6 / 7 : ℚ), 0, 0], ![(2 / 7 : ℚ), (4 / 7 : ℚ), (-16 / 7 : ℚ), 0, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 19 : ℚ), (-35 / 19 : ℚ), 0, (29 / 19 : ℚ), (-66 / 19 : ℚ)], ![(-33 / 19 : ℚ), (2 / 19 : ℚ), (-2 / 19 : ℚ), (20 / 19 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-11 / 12 : ℚ), 0, (19 / 24 : ℚ), (-43 / 24 : ℚ)], ![(-7 / 8 : ℚ), (1 / 24 : ℚ), (-11 / 24 : ℚ), 0, (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-39 / 20 : ℚ), (1 / 4 : ℚ), (9 / 5 : ℚ), (-15 / 4 : ℚ)], ![(-19 / 10 : ℚ), (1 / 20 : ℚ), 0, (9 / 5 : ℚ), (-15 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (4 / 11 : ℚ), (-28 / 11 : ℚ), (4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-12 / 11 : ℚ), 0, 0], ![0, (4 / 11 : ℚ), (-28 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (4 / 11 : ℚ), (-28 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (4 / 11 : ℚ), (-28 / 11 : ℚ), (4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-6 / 11 : ℚ), (-10 / 11 : ℚ), 0, (-2 / 11 : ℚ)], ![(-2 / 11 : ℚ), (4 / 11 : ℚ), (-24 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), 0, 0, (-18 / 17 : ℚ), (-12 / 17 : ℚ)], ![0, (6 / 17 : ℚ), 0, (-36 / 17 : ℚ), (18 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (2 / 5 : ℚ), 0, (-12 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-6 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-6 / 7 : ℚ)], ![(-6 / 7 : ℚ), 0, (-8 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ), 0], ![0, (2 / 5 : ℚ), 0, (-12 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-6 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-10 / 7 : ℚ)], ![(-6 / 7 : ℚ), 0, (-8 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, 0, (-9 / 8 : ℚ)], ![(-3 / 8 : ℚ), -2, -2, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, 0, 0, (-7 / 6 : ℚ)], ![(-1 / 2 : ℚ), -2, -2, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, 0, 0, (-7 / 6 : ℚ)], ![(-1 / 2 : ℚ), -2, -2, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(-1 / 4 : ℚ), -2, -2, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, 0, 0, (-13 / 3 : ℚ)], ![-1, -2, -2, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, 0, 0, (-13 / 3 : ℚ)], ![-1, -2, -2, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, 0, 0, (-13 / 3 : ℚ)], ![-1, -2, -2, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), -2, 2, 0, -2], ![-2, -2, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, -2, (1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, 0, -4, (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![0, 0, 0, -4, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, -2, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, -4, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (1 / 4 : ℚ), 0, (-9 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, -2, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, -4, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (1 / 5 : ℚ), 0], ![(3 / 5 : ℚ), 0, (-13 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (2 / 5 : ℚ), -2, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 4 : ℚ), (1 / 4 : ℚ), (-7 / 4 : ℚ), (7 / 4 : ℚ)], ![(-7 / 4 : ℚ), (-7 / 4 : ℚ), 0, (7 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 6 : ℚ), 0], ![0, (1 / 12 : ℚ), (-7 / 12 : ℚ), (1 / 4 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ), (-4 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, -2, (6 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 6 : ℚ), 0], ![0, (1 / 12 : ℚ), (-7 / 12 : ℚ), (1 / 4 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![0, 0, -2, (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (2 / 5 : ℚ), -2, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 4 : ℚ), (1 / 4 : ℚ), (-7 / 4 : ℚ), (7 / 4 : ℚ)], ![(-7 / 4 : ℚ), (-7 / 4 : ℚ), 0, 0, (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, -1, (-3 / 2 : ℚ)], ![(-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, -1, (-5 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), 0, 0], ![0, (1 / 12 : ℚ), (-7 / 12 : ℚ), (1 / 12 : ℚ), (23 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, -2, 0, 4]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![0, 0, (-5 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-8 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, -1], ![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-8 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 3 : ℚ), 0, (5 / 3 : ℚ), -4], ![-2, (-5 / 3 : ℚ), (-1 / 3 : ℚ), (5 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-11 / 6 : ℚ), 0, (11 / 6 : ℚ), (-25 / 6 : ℚ)], ![-2, (-11 / 6 : ℚ), (-1 / 6 : ℚ), (11 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 6 : ℚ), (-5 / 6 : ℚ), (-1 / 6 : ℚ), 0], ![(-1 / 6 : ℚ), (1 / 6 : ℚ), -3, (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), (-4 / 15 : ℚ), (-14 / 15 : ℚ), 0, 0], ![(2 / 15 : ℚ), 0, (-32 / 15 : ℚ), (4 / 15 : ℚ), (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-5 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![0, 0, -2, (2 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-40 / 17 : ℚ), (-3 / 17 : ℚ), 0, (-32 / 17 : ℚ)], ![(-9 / 17 : ℚ), (-80 / 17 : ℚ), (-43 / 17 : ℚ), 0, (35 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-9 / 5 : ℚ)], ![(-3 / 5 : ℚ), (-24 / 5 : ℚ), (-13 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(-3 / 5 : ℚ), (-24 / 5 : ℚ), (-13 / 5 : ℚ), 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, 0], ![(-1 / 4 : ℚ), -5, (-9 / 4 : ℚ), 0, (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-22 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-52 / 7 : ℚ)], ![(-12 / 7 : ℚ), (-44 / 7 : ℚ), (-26 / 7 : ℚ), 0, (-24 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-23 / 4 : ℚ)], ![(-3 / 4 : ℚ), -5, (-11 / 4 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 13 : ℚ), (-42 / 13 : ℚ), (-8 / 13 : ℚ), 0, (-92 / 13 : ℚ)], ![(-24 / 13 : ℚ), (-84 / 13 : ℚ), (-50 / 13 : ℚ), 0, (-88 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-13 / 6 : ℚ), 2, 0, -2], ![-2, (-13 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-11 / 5 : ℚ), 2, 0, (-8 / 5 : ℚ)], ![(-13 / 5 : ℚ), (-22 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 3 : ℚ), (7 / 3 : ℚ), 0, 0], ![(-7 / 3 : ℚ), (-14 / 3 : ℚ), 0, 0, (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-5 / 2 : ℚ), 2, 0, (-15 / 2 : ℚ)], ![(-5 / 2 : ℚ), -5, (-1 / 2 : ℚ), 0, (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (-26 / 9 : ℚ), (22 / 9 : ℚ), 0, (-68 / 9 : ℚ)], ![(-10 / 3 : ℚ), (-52 / 9 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-12 / 5 : ℚ), 2, 0, (-27 / 5 : ℚ)], ![(-12 / 5 : ℚ), (-24 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-26 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), 0, (-18 / 17 : ℚ), (-12 / 17 : ℚ), (-6 / 17 : ℚ)], ![0, 0, (-36 / 17 : ℚ), (18 / 17 : ℚ), (6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), 0, (-18 / 17 : ℚ), (-12 / 17 : ℚ), 0], ![0, 0, (-36 / 17 : ℚ), (18 / 17 : ℚ), (6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 2 : ℚ), 0, -2, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, -2, 0, 0], ![0, -2, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (6 / 17 : ℚ), (-18 / 17 : ℚ), (-12 / 17 : ℚ), 0], ![0, (12 / 17 : ℚ), (-36 / 17 : ℚ), (18 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (-12 / 17 : ℚ), 0, (-30 / 17 : ℚ), (-42 / 17 : ℚ)], ![(-18 / 17 : ℚ), (-24 / 17 : ℚ), 0, (36 / 17 : ℚ), (6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), 0, (-30 / 17 : ℚ), 0, 0], ![(12 / 17 : ℚ), 0, (-60 / 17 : ℚ), (6 / 17 : ℚ), (6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, 0, -1, (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 2 : ℚ), 0, -2, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, -2, 0, 0], ![0, -2, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (2 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (4 / 5 : ℚ), (-12 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), 0, (-16 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 20 : ℚ), (-4 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 10 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 2 : ℚ), 0, -2, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, -2, 0, 0], ![(-1 / 2 : ℚ), -2, -4, 0, 0]] }
]

theorem conicDetC13_checked : conicDetC13.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
