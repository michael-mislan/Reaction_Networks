import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC26 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -4], ![0, -2, (-2 / 7 : ℚ), (5 / 7 : ℚ), (-13 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -4], ![0, -2, (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -4], ![0, -2, (-2 / 7 : ℚ), (2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -4], ![0, -2, 0, (-1 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -2], ![0, -2, (-2 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -4], ![0, -2, 0, (1 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), 1, -1, 0, 0], ![(-1 / 4 : ℚ), 0, -1, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 24 : ℚ), 0, (-5 / 24 : ℚ), (11 / 8 : ℚ), (-31 / 24 : ℚ)], ![(-25 / 24 : ℚ), (-7 / 24 : ℚ), (-7 / 4 : ℚ), (-4 / 3 : ℚ), (-5 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 15 : ℚ), (26 / 15 : ℚ), 0, (1 / 15 : ℚ), -4], ![(4 / 15 : ℚ), (-4 / 15 : ℚ), 0, (1 / 5 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 2, 0, (-7 / 6 : ℚ), -1], ![(1 / 3 : ℚ), 0, 0, 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 15 : ℚ), (32 / 15 : ℚ), (7 / 15 : ℚ), (-2 / 5 : ℚ), (-14 / 3 : ℚ)], ![(7 / 15 : ℚ), 0, 0, 0, (-34 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 2, 0, (-1 / 4 : ℚ), -4], ![(1 / 2 : ℚ), 0, 0, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, -2, 0, 1], ![(-3 / 2 : ℚ), 0, -2, -1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (5 / 3 : ℚ), 0, -1, 1], ![(1 / 3 : ℚ), (-1 / 3 : ℚ), 0, -1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 2, 0, -1, -5], ![1, 0, 0, -1, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 2, 0, -1, -6], ![1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (5 / 3 : ℚ), 0, -1, -4], ![(1 / 3 : ℚ), (-1 / 3 : ℚ), 0, -1, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), 0, (-5 / 11 : ℚ), (1 / 11 : ℚ), (-18 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-15 / 44 : ℚ), (-7 / 4 : ℚ), (-12 / 11 : ℚ), (-17 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), 0, (-12 / 7 : ℚ), (2 / 7 : ℚ), (-4 / 7 : ℚ)], ![(-10 / 7 : ℚ), (-2 / 7 : ℚ), (-12 / 7 : ℚ), (-9 / 7 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(31 / 18 : ℚ), 2, (1 / 36 : ℚ), (5 / 18 : ℚ), (-151 / 36 : ℚ)], ![(35 / 36 : ℚ), (-1 / 36 : ℚ), 0, (5 / 24 : ℚ), (-25 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (5 / 3 : ℚ), 0, 1, -4], ![(1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 1, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 15 : ℚ), (32 / 15 : ℚ), (7 / 15 : ℚ), (-14 / 3 : ℚ), (-14 / 3 : ℚ)], ![(7 / 15 : ℚ), 0, 0, 0, (-34 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 8 : ℚ), (31 / 16 : ℚ), 0, (-77 / 16 : ℚ), -4], ![(7 / 8 : ℚ), (-1 / 16 : ℚ), 0, (-17 / 8 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 2, 0, (-17 / 4 : ℚ), -4], ![(1 / 2 : ℚ), 0, 0, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (5 / 3 : ℚ), 0, -4, -2], ![(1 / 3 : ℚ), (-1 / 3 : ℚ), 0, -4, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 1, 0], ![(7 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 1, 0], ![2, (-1 / 2 : ℚ), 0, 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, (-3 / 4 : ℚ)], ![-1, 0, 0, -1, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, 0, (-5 / 2 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, (-4 / 3 : ℚ)], ![-1, 0, 0, -1, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, (-1 / 4 : ℚ), (-11 / 4 : ℚ)], ![0, -1, 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, (-1 / 4 : ℚ), (-9 / 4 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, (-1 / 4 : ℚ), (-5 / 2 : ℚ)], ![0, -1, 0, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 12 : ℚ), (-5 / 12 : ℚ)], ![-1, 0, 0, (11 / 12 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, (-1 / 2 : ℚ), -4], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 6 : ℚ), (-1 / 3 : ℚ)], ![-1, 0, 0, (1 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![-1, 0, 0, -1, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![-1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![-1, 0, 0, -1, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 1, 0], ![2, (-1 / 2 : ℚ), 0, 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, (-3 / 2 : ℚ)], ![-1, 0, 0, -1, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, 0, (-9 / 4 : ℚ)], ![0, -2, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, (-6 / 5 : ℚ)], ![-1, 0, 0, -1, (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, (-1 / 16 : ℚ), (-19 / 8 : ℚ)], ![0, -2, 0, 0, (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, (-1 / 3 : ℚ), (-7 / 3 : ℚ)], ![0, -2, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, (-1 / 6 : ℚ), (-5 / 2 : ℚ)], ![0, -2, 0, 0, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 24 : ℚ), (-5 / 24 : ℚ)], ![-1, 0, 0, (23 / 24 : ℚ), (-1 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 1, (-1 / 4 : ℚ), -4], ![0, -2, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 6 : ℚ), (-1 / 4 : ℚ)], ![-1, 0, 0, (1 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![-1, 0, 0, -1, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![-1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![-1, 0, 0, -1, (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 3 : ℚ), (-1 / 3 : ℚ), -1, 1, 0], ![(7 / 3 : ℚ), (-1 / 3 : ℚ), -1, 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 3 : ℚ), (-1 / 6 : ℚ), (5 / 6 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ)], ![(13 / 6 : ℚ), 0, (5 / 6 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, (-1 / 2 : ℚ)], ![(-7 / 6 : ℚ), 0, 0, -1, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), (-1 / 2 : ℚ), (-7 / 2 : ℚ)], ![0, (-3 / 2 : ℚ), 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, (-2 / 3 : ℚ)], ![(-13 / 9 : ℚ), 0, 0, -1, (-4 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 4 : ℚ), (-3 / 8 : ℚ)], ![(-9 / 8 : ℚ), (-1 / 8 : ℚ), 0, 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-3 / 4 : ℚ), (-13 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (9 / 8 : ℚ), (-3 / 8 : ℚ), (-21 / 8 : ℚ)], ![0, (-5 / 4 : ℚ), 0, 0, (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (2 / 13 : ℚ), (-23 / 13 : ℚ)], ![(-14 / 13 : ℚ), (-1 / 13 : ℚ), (-1 / 13 : ℚ), (9 / 26 : ℚ), (-3 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-1 / 3 : ℚ), -4], ![0, (-7 / 6 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 5 : ℚ), (-7 / 20 : ℚ)], ![(-11 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 10 : ℚ)], ![(-11 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-4 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 13 : ℚ)], ![(-17 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-17 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 17 : ℚ), (-24 / 17 : ℚ)], ![(-22 / 17 : ℚ), (-12 / 17 : ℚ), (-21 / 68 : ℚ), (-3 / 4 : ℚ), (-23 / 34 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (8 / 5 : ℚ), 1, -4], ![0, -2, 0, (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), 0, -2], ![-1, -1, (-1 / 2 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, 0, 0, 2]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, (-2 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, -2], ![-1, -1, (-1 / 7 : ℚ), (1 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, -2], ![-1, -1, 0, (-1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, -1], ![-1, -1, (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, -2], ![-1, -1, 0, (1 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-13 / 4 : ℚ)], ![0, 0, 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (17 / 13 : ℚ), (4 / 13 : ℚ), (4 / 13 : ℚ), (-40 / 13 : ℚ)], ![0, 0, 0, 0, (-38 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 12 : ℚ), (13 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-10 / 3 : ℚ)], ![0, 0, (1 / 12 : ℚ), (-1 / 12 : ℚ), (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 1, 0, 0, -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (9 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-22 / 7 : ℚ)], ![0, 0, (2 / 7 : ℚ), (-2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 0, (5 / 4 : ℚ), (1 / 12 : ℚ), (-7 / 12 : ℚ)], ![(-13 / 12 : ℚ), (-1 / 12 : ℚ), (-7 / 6 : ℚ), (-13 / 12 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 35 : ℚ), 0, (59 / 35 : ℚ), (8 / 35 : ℚ), (-4 / 5 : ℚ)], ![(-43 / 35 : ℚ), (-8 / 35 : ℚ), (-51 / 35 : ℚ), (-43 / 35 : ℚ), (-24 / 35 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(12 / 11 : ℚ), (12 / 11 : ℚ), (2 / 11 : ℚ), 0, (-31 / 11 : ℚ)], ![0, (-1 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 11 : ℚ), (-15 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 15 : ℚ), (-4 / 15 : ℚ), (31 / 15 : ℚ), -1, 0], ![(-23 / 15 : ℚ), (-4 / 15 : ℚ), (-9 / 5 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (9 / 7 : ℚ), (2 / 7 : ℚ), (-24 / 7 : ℚ), (-24 / 7 : ℚ)], ![0, 0, 0, 0, (-11 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 3 : ℚ), (-7 / 2 : ℚ), (-35 / 12 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 3 : ℚ), (-17 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (17 / 13 : ℚ), (4 / 13 : ℚ), (-40 / 13 : ℚ), (-40 / 13 : ℚ)], ![0, 0, 0, 0, (-38 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 3 : ℚ), (-35 / 12 : ℚ), (-5 / 3 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-17 / 6 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (7 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-11 / 3 : ℚ)], ![0, 0, 0, (-1 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 1, (-1 / 3 : ℚ), (-1 / 3 : ℚ), -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (6 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), (-27 / 10 : ℚ)], ![0, 0, 0, (-2 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, (3 / 2 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (17 / 13 : ℚ), (4 / 13 : ℚ), (4 / 13 : ℚ), (-40 / 13 : ℚ)], ![0, 0, 0, 0, (-38 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, (7 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-17 / 6 : ℚ)], ![0, 0, 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), (5 / 4 : ℚ), 0, (1 / 4 : ℚ), (-5 / 2 : ℚ)], ![0, 0, 0, (1 / 4 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (9 / 7 : ℚ), 0, (-24 / 7 : ℚ), (-24 / 7 : ℚ)], ![0, 0, 0, 0, (-11 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 7 : ℚ), (8 / 7 : ℚ), 0, (-19 / 7 : ℚ), (-5 / 2 : ℚ)], ![0, 0, 0, (-9 / 7 : ℚ), (-17 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (17 / 13 : ℚ), 0, (-40 / 13 : ℚ), (-40 / 13 : ℚ)], ![0, 0, 0, 0, (-38 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (6 / 5 : ℚ), 0, (-27 / 10 : ℚ), (-8 / 5 : ℚ)], ![0, 0, 0, (-13 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, 0, 1, (-4 / 3 : ℚ)], ![(-7 / 6 : ℚ), 0, -1, 1, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 1, -2], ![-1, 0, -1, 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), 0, 0, 1, (-4 / 7 : ℚ)], ![(-9 / 7 : ℚ), 0, -1, 1, (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, 1, -1, -1], ![-1, 0, 1, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 1, 0, 0, -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (2 / 3 : ℚ), 0, 0, -2], ![(-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 1, (-2 / 3 : ℚ), -4, (-8 / 3 : ℚ)], ![0, 0, 0, 0, (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 15 : ℚ), (16 / 15 : ℚ), (-13 / 15 : ℚ), (-43 / 15 : ℚ), (-71 / 30 : ℚ)], ![0, (-1 / 15 : ℚ), (-1 / 5 : ℚ), (-19 / 15 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 1, (-1 / 3 : ℚ), -4, -2], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 1, (-1 / 3 : ℚ), -4, (-5 / 2 : ℚ)], ![0, 0, 0, 0, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (1 / 2 : ℚ), 0, (-19 / 12 : ℚ), -1], ![(-2 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-3 / 2 : ℚ), (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 19 : ℚ), 0, (1 / 19 : ℚ), (-5 / 19 : ℚ), (-26 / 19 : ℚ)], ![(-24 / 19 : ℚ), (-23 / 76 : ℚ), (-20 / 19 : ℚ), (-3 / 4 : ℚ), (-25 / 38 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (5 / 7 : ℚ), (2 / 7 : ℚ), 0, -2], ![(-5 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (9 / 7 : ℚ), (2 / 7 : ℚ), (-24 / 7 : ℚ), (-24 / 7 : ℚ)], ![0, 0, 0, 0, (-11 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), 0, (1 / 11 : ℚ), (-7 / 11 : ℚ), (-7 / 22 : ℚ)], ![(-12 / 11 : ℚ), (-1 / 11 : ℚ), (-12 / 11 : ℚ), (-3 / 11 : ℚ), (-3 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (17 / 13 : ℚ), (4 / 13 : ℚ), (-40 / 13 : ℚ), (-40 / 13 : ℚ)], ![0, 0, 0, 0, (-38 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-7 / 12 : ℚ), (-1 / 2 : ℚ)], ![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 7 : ℚ), (8 / 7 : ℚ), 0, (-19 / 7 : ℚ), (-19 / 7 : ℚ)], ![0, 0, (-1 / 7 : ℚ), 0, (-9 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(17 / 24 : ℚ), 0, (-37 / 48 : ℚ), (-53 / 48 : ℚ), (-11 / 24 : ℚ)], ![(-17 / 16 : ℚ), (-11 / 48 : ℚ), (-37 / 48 : ℚ), (-25 / 48 : ℚ), (-11 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), (5 / 4 : ℚ), (1 / 4 : ℚ), (-21 / 8 : ℚ), (-5 / 2 : ℚ)], ![0, 0, (1 / 4 : ℚ), 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (4 / 3 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ), (-5 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)], ![(-3 / 2 : ℚ), (3 / 2 : ℚ), 0, (-7 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)], ![(-3 / 2 : ℚ), (3 / 2 : ℚ), 0, (-7 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(-5 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, 0, 0], ![(-5 / 4 : ℚ), (9 / 8 : ℚ), 0, (-21 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, 0, 0, 0], ![(-7 / 6 : ℚ), 1, 0, -4, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (1 / 2 : ℚ), 0, 0], ![-2, 2, (1 / 2 : ℚ), (-9 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, 0, (-3 / 2 : ℚ)], ![(-5 / 4 : ℚ), (5 / 4 : ℚ), 0, (-11 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, (5 / 6 : ℚ), 0, 0], ![(-5 / 2 : ℚ), (13 / 6 : ℚ), (5 / 6 : ℚ), (-16 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (1 / 3 : ℚ)], ![(-4 / 3 : ℚ), (4 / 3 : ℚ), (1 / 6 : ℚ), (-17 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (1 / 3 : ℚ)], ![(-4 / 3 : ℚ), (4 / 3 : ℚ), (1 / 6 : ℚ), (-17 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(-5 / 3 : ℚ), (4 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-5 / 2 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (1 / 6 : ℚ), 0, 0], ![-2, 2, (1 / 2 : ℚ), (-25 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (1 / 12 : ℚ), 0, 0], ![-2, 2, (1 / 4 : ℚ), (-49 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, (5 / 6 : ℚ), 0, 0], ![(-5 / 2 : ℚ), (13 / 6 : ℚ), 2, (-16 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), 1]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-7 / 6 : ℚ), (-1 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-5 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![0, (-8 / 9 : ℚ), (-17 / 9 : ℚ), (-8 / 9 : ℚ), (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![-1, 1, 0, -4, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, 0, 0, 0], ![(-9 / 8 : ℚ), 1, (-1 / 8 : ℚ), -4, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-5 / 4 : ℚ), 0, 0], ![-2, 2, (-1 / 2 : ℚ), (-27 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, -1, 0, 0], ![-2, 2, 0, -7, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, 0], ![(-8 / 3 : ℚ), (20 / 9 : ℚ), (-4 / 9 : ℚ), (-70 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![-1, 1, (-5 / 2 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![-1, 1, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, 0, (5 / 4 : ℚ), 0], ![(-9 / 4 : ℚ), (9 / 4 : ℚ), -5, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![-1, 1, (-5 / 2 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![-1, 1, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, 0, (5 / 4 : ℚ), 0], ![(-9 / 4 : ℚ), (9 / 4 : ℚ), -5, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, 0, (5 / 6 : ℚ), 0], ![(-5 / 2 : ℚ), (13 / 6 : ℚ), (-16 / 3 : ℚ), (5 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![-2, 2, (-14 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![-2, 2, (-14 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, 0, 0, 0], ![(-5 / 2 : ℚ), (13 / 6 : ℚ), (-16 / 3 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, (-5 / 4 : ℚ), 0], ![-2, 2, (-27 / 4 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), 0, 0, 0, (-14 / 5 : ℚ)], ![(-3 / 5 : ℚ), (3 / 5 : ℚ), (-22 / 5 : ℚ), (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0], ![(-8 / 3 : ℚ), (20 / 9 : ℚ), (-70 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, (-3 / 2 : ℚ), (1 / 4 : ℚ)], ![(-5 / 4 : ℚ), (5 / 4 : ℚ), 0, (-13 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 8 : ℚ), 0, (-13 / 8 : ℚ), (1 / 8 : ℚ), (-11 / 8 : ℚ)], ![(3 / 8 : ℚ), (-3 / 8 : ℚ), (-13 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0], ![(-7 / 5 : ℚ), 1, 0, (-17 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), 0], ![(-5 / 4 : ℚ), (9 / 8 : ℚ), 0, (-21 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (-1 / 6 : ℚ), (-11 / 6 : ℚ), 0, (11 / 6 : ℚ)], ![(2 / 3 : ℚ), -1, (-11 / 6 : ℚ), (-1 / 6 : ℚ), (11 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, (-3 / 2 : ℚ), 0, (-9 / 2 : ℚ)], ![(1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, (-3 / 2 : ℚ), 0, (-9 / 2 : ℚ)], ![(1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-9 / 5 : ℚ)], ![(-7 / 5 : ℚ), 1, 0, (-17 / 5 : ℚ), (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, 0, (-5 / 2 : ℚ), (3 / 4 : ℚ)], ![(-7 / 4 : ℚ), (7 / 4 : ℚ), 0, -5, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ), (2 / 3 : ℚ)], ![(-5 / 3 : ℚ), (5 / 3 : ℚ), 0, (-14 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-7 / 4 : ℚ), 0], ![(-3 / 2 : ℚ), 1, 0, (-7 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), 0], ![(-11 / 8 : ℚ), (9 / 8 : ℚ), 0, (-5 / 2 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (1 / 4 : ℚ), (-11 / 4 : ℚ), 0], ![-2, 2, (1 / 2 : ℚ), (-11 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), 0, 0, (-9 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-7 / 5 : ℚ), (7 / 5 : ℚ), 0, (-18 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-3, (-2 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ), 0], ![-3, (5 / 3 : ℚ), (2 / 3 : ℚ), (-22 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(15 / 17 : ℚ), 0, (-3 / 17 : ℚ), 0, (-32 / 17 : ℚ)], ![(15 / 17 : ℚ), (-15 / 17 : ℚ), (-43 / 17 : ℚ), (-3 / 17 : ℚ), (32 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 20 : ℚ), (-1 / 5 : ℚ), -1], ![0, 0, (-39 / 20 : ℚ), (-9 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![0, (-3 / 5 : ℚ), (-13 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0, (-19 / 4 : ℚ)], ![(3 / 8 : ℚ), (-3 / 8 : ℚ), (-19 / 8 : ℚ), (-1 / 8 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 10 : ℚ), 0, (-1 / 5 : ℚ), 0, (-27 / 5 : ℚ)], ![(7 / 10 : ℚ), (-7 / 10 : ℚ), (-13 / 5 : ℚ), (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-21 / 4 : ℚ)], ![0, (-3 / 4 : ℚ), (-11 / 4 : ℚ), (-1 / 4 : ℚ), (-21 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-1 / 3 : ℚ), -1], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0], ![(-4 / 3 : ℚ), (5 / 6 : ℚ), (-2 / 3 : ℚ), (-7 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-17 / 16 : ℚ), (-45 / 16 : ℚ), 0], ![-2, 2, (-1 / 2 : ℚ), (-91 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-1 / 2 : ℚ), -4], ![0, 0, 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 5 : ℚ), (-2 / 5 : ℚ), (-8 / 5 : ℚ), (-17 / 5 : ℚ), 0], ![(-13 / 5 : ℚ), (9 / 5 : ℚ), (-2 / 5 : ℚ), (-36 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, (-8 / 5 : ℚ), 0, -2], ![-1, 1, (-19 / 5 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), -1, -4], ![0, 0, (-9 / 5 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, (-8 / 5 : ℚ), 0, (-13 / 5 : ℚ)], ![-1, 1, (-19 / 5 : ℚ), 0, (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), -1, -4], ![0, 0, (-3 / 4 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), -1, -4], ![0, 0, (-3 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), 0, (-19 / 8 : ℚ), (9 / 8 : ℚ), 0], ![(-17 / 8 : ℚ), (17 / 8 : ℚ), -5, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (-13 / 10 : ℚ), 0, (-19 / 10 : ℚ)], ![(-6 / 5 : ℚ), 1, (-27 / 10 : ℚ), 0, (-19 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), 0, 0, 0, (-16 / 3 : ℚ)], ![(2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 1, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-8 / 3 : ℚ), 0, 0], ![-2, 2, -6, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -5], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (2 / 3 : ℚ), -5]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 16 : ℚ), (15 / 16 : ℚ), -4], ![0, 0, (-3 / 4 : ℚ), (1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), 0, -1, 0, (-14 / 5 : ℚ)], ![(-3 / 5 : ℚ), (3 / 5 : ℚ), -3, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, (-1 / 3 : ℚ), 0, 2, -7], ![1, (-5 / 3 : ℚ), (-1 / 3 : ℚ), 2, -7]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ), (2 / 3 : ℚ)], ![(-5 / 3 : ℚ), (5 / 3 : ℚ), 0, (-7 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, -2, (1 / 2 : ℚ)], ![(-3 / 2 : ℚ), (3 / 2 : ℚ), 0, -2, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), 0], ![(-5 / 4 : ℚ), (9 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, 0, (-5 / 4 : ℚ), (-7 / 4 : ℚ)], ![(-9 / 8 : ℚ), (9 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-7 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, 0, (-4 / 3 : ℚ), (-5 / 3 : ℚ)], ![(-7 / 6 : ℚ), (7 / 6 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, (-19 / 8 : ℚ), (1 / 2 : ℚ)], ![(-3 / 2 : ℚ), (3 / 2 : ℚ), (1 / 8 : ℚ), (-5 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(19 / 20 : ℚ), 0, (-11 / 5 : ℚ), (1 / 20 : ℚ), (-39 / 20 : ℚ)], ![(19 / 20 : ℚ), (-19 / 20 : ℚ), (-87 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 10 : ℚ), 0, 0, (-23 / 10 : ℚ), 0], ![(-7 / 5 : ℚ), (11 / 10 : ℚ), (1 / 10 : ℚ), (-12 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 16 : ℚ), 0, (-1 / 16 : ℚ), (-37 / 16 : ℚ), (-13 / 8 : ℚ)], ![(-19 / 16 : ℚ), (19 / 16 : ℚ), 0, (-39 / 16 : ℚ), (-13 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(9 / 5 : ℚ), 0, (-18 / 5 : ℚ), (2 / 5 : ℚ), (-38 / 5 : ℚ)], ![(9 / 5 : ℚ), (-9 / 5 : ℚ), (-34 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), 0, (-1 / 10 : ℚ), 0, (-7 / 5 : ℚ)], ![(2 / 5 : ℚ), (-2 / 5 : ℚ), (-11 / 5 : ℚ), (-1 / 10 : ℚ), (7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(3 / 5 : ℚ), (-3 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0, (-28 / 5 : ℚ)], ![(4 / 5 : ℚ), (-4 / 5 : ℚ), (-14 / 5 : ℚ), (-2 / 5 : ℚ), (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), (-1 / 2 : ℚ), -4], ![0, 0, (-19 / 10 : ℚ), (-7 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-1 / 2 : ℚ), -1], ![0, 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), 0, (13 / 8 : ℚ), (1 / 8 : ℚ), (-11 / 2 : ℚ)], ![(3 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-2 / 3 : ℚ), -4], ![0, 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, (-5 / 4 : ℚ), 0, -2], ![-1, 1, (-3 / 2 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), -1, -4], ![0, 0, (-1 / 2 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, (-5 / 3 : ℚ), 0, (-8 / 3 : ℚ)], ![-1, 1, (-5 / 3 : ℚ), 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), -1, -4], ![0, 0, (-2 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), -1, -4], ![0, 0, (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, (-11 / 4 : ℚ), (5 / 4 : ℚ), 0], ![(-9 / 4 : ℚ), (9 / 4 : ℚ), (-11 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-9 / 4 : ℚ), 0, 0], ![-2, 2, (-5 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), 0, 0, 0, (-16 / 3 : ℚ)], ![(2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, (-5 / 2 : ℚ), 0, 0], ![(-5 / 2 : ℚ), (13 / 6 : ℚ), (-5 / 2 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-9 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![-2, 2, (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), 0, -1, 0, (-14 / 5 : ℚ)], ![(-3 / 5 : ℚ), (3 / 5 : ℚ), (-7 / 5 : ℚ), (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, 0, (3 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-7 / 4 : ℚ), (7 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 6 : ℚ), 0, 0, (5 / 6 : ℚ), (-1 / 3 : ℚ)], ![(-11 / 6 : ℚ), (11 / 6 : ℚ), 0, (-5 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), 0, (1 / 3 : ℚ), (7 / 6 : ℚ), 0], ![(-13 / 6 : ℚ), (13 / 6 : ℚ), (1 / 3 : ℚ), (-7 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, 0, (3 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-7 / 4 : ℚ), (7 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, (1 / 4 : ℚ), (-3 / 2 : ℚ)], ![(-5 / 4 : ℚ), (5 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, (3 / 4 : ℚ), (5 / 4 : ℚ), 0], ![(-9 / 4 : ℚ), (9 / 4 : ℚ), (3 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, (-2 / 3 : ℚ)], ![(-5 / 3 : ℚ), (5 / 3 : ℚ), 0, (-5 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, (-2 / 3 : ℚ)], ![(-5 / 3 : ℚ), (5 / 3 : ℚ), 0, (-5 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 8 : ℚ), 0, (7 / 8 : ℚ), 0, 0], ![(-19 / 8 : ℚ), (17 / 8 : ℚ), (7 / 8 : ℚ), (-13 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (1 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![-2, 2, (1 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (1 / 6 : ℚ), (-4 / 3 : ℚ), 0], ![-2, 2, (1 / 6 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 1, 0], ![-2, 2, (1 / 4 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 1, 0], ![-2, 2, (1 / 4 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), 0, 0, (7 / 6 : ℚ), 0], ![(-13 / 6 : ℚ), (13 / 6 : ℚ), (5 / 6 : ℚ), (-7 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, (1 / 4 : ℚ), (-3 / 2 : ℚ)], ![(-5 / 4 : ℚ), (5 / 4 : ℚ), (1 / 8 : ℚ), 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, (1 / 4 : ℚ), (-3 / 2 : ℚ)], ![(-5 / 4 : ℚ), (5 / 4 : ℚ), (1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 5 : ℚ), 0, 0, (6 / 5 : ℚ), 0], ![(-11 / 5 : ℚ), (11 / 5 : ℚ), (4 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (1 / 4 : ℚ), 0, 0], ![-2, 2, (5 / 8 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (1 / 4 : ℚ), 0, 0], ![-2, 2, (5 / 8 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 8 : ℚ), 0, (7 / 8 : ℚ), 0, 0], ![(-19 / 8 : ℚ), (17 / 8 : ℚ), 2, (-13 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-26 / 17 : ℚ), (9 / 34 : ℚ), -4], ![0, 0, (-101 / 34 : ℚ), (3 / 17 : ℚ), -2]] }
]

theorem conicDetC26_checked : conicDetC26.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
