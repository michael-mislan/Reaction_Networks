import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC07 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (5 / 3 : ℚ), (-5 / 3 : ℚ), 0], ![1, 2, (5 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (7 / 4 : ℚ), (-7 / 4 : ℚ), 0], ![(5 / 4 : ℚ), (9 / 4 : ℚ), (7 / 4 : ℚ), (-7 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(1 / 10 : ℚ), (21 / 10 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-10 / 7 : ℚ), 0], ![(1 / 7 : ℚ), (15 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (13 / 6 : ℚ), (-11 / 6 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-15 / 11 : ℚ), (-2 / 11 : ℚ), 0], ![0, 2, (-17 / 11 : ℚ), (2 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-10 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![0, (13 / 7 : ℚ), (-10 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-17 / 12 : ℚ), 0, (-1 / 12 : ℚ)], ![(1 / 12 : ℚ), (25 / 12 : ℚ), (-19 / 12 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-12 / 7 : ℚ), 0, 0], ![(1 / 7 : ℚ), (15 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-5 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-21 / 16 : ℚ), (-9 / 8 : ℚ), (-1 / 16 : ℚ), 0], ![(1 / 16 : ℚ), (-23 / 16 : ℚ), (-1 / 8 : ℚ), 0, (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (-8 / 3 : ℚ)], ![-1, (-1 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), 0, (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![(-3 / 5 : ℚ), 0, 0, 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, (-3 / 2 : ℚ), 0], ![(-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, 0, (-1 / 7 : ℚ), (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-3 / 7 : ℚ), (5 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (3 / 20 : ℚ), (1 / 4 : ℚ), (1 / 20 : ℚ), (-9 / 20 : ℚ)], ![(-7 / 20 : ℚ), (1 / 20 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 4 : ℚ), (-13 / 12 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-7 / 12 : ℚ), (-13 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 0, -4], ![-1, 0, 0, (-1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, (-1 / 2 : ℚ), (-3 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, (-3 / 2 : ℚ), 0, (-7 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, 0, 0, -6], ![-2, 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), -6]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 4 : ℚ), (-3 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-3 / 8 : ℚ), (-1 / 8 : ℚ), (-3 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 0, -4], ![(-2 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, (-3 / 4 : ℚ), 0, (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-6 / 11 : ℚ), 0, 0, (6 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-3 / 5 : ℚ), 0, 0, (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-3 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-7 / 6 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-7 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-9 / 8 : ℚ), (-17 / 16 : ℚ), 0, (3 / 16 : ℚ)], ![(1 / 4 : ℚ), (-9 / 8 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 2 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), -4], ![(-1 / 2 : ℚ), 0, 0, (-5 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-29 / 24 : ℚ), (-13 / 12 : ℚ), (-1 / 24 : ℚ), (1 / 3 : ℚ)], ![(1 / 2 : ℚ), (-31 / 24 : ℚ), (-1 / 12 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-29 / 24 : ℚ), (-25 / 24 : ℚ), (-1 / 24 : ℚ), (3 / 8 : ℚ)], ![(11 / 24 : ℚ), (-31 / 24 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 5 : ℚ), (-13 / 10 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-9 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, -2, 0, 0], ![0, -2, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-14 / 9 : ℚ), (-10 / 9 : ℚ), (-1 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, (-16 / 9 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), 0, 0, (-1 / 14 : ℚ), (-2 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-1 / 14 : ℚ), (-1 / 14 : ℚ), (-8 / 7 : ℚ), (5 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-6 / 5 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ)], ![(1 / 2 : ℚ), (-13 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, 0, (-1 / 8 : ℚ), -4], ![(-1 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-7 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0, 0], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, 0, (1 / 4 : ℚ), -4], ![(-1 / 3 : ℚ), 0, 0, (-5 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-2 / 3 : ℚ), -4], ![(-1 / 3 : ℚ), 0, 0, (5 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-10 / 11 : ℚ), (-8 / 11 : ℚ), (2 / 11 : ℚ), 0], ![(6 / 11 : ℚ), (-12 / 11 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, 0, (-4 / 7 : ℚ), (-31 / 7 : ℚ)], ![(-2 / 7 : ℚ), 0, (-1 / 7 : ℚ), (5 / 7 : ℚ), (-31 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, -2, (5 / 4 : ℚ), 0], ![(3 / 2 : ℚ), -2, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-3 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-35 / 16 : ℚ), (-33 / 16 : ℚ), (21 / 16 : ℚ), 0], ![(23 / 16 : ℚ), (-35 / 16 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -5], ![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (2 / 3 : ℚ), -5]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (1 / 2 : ℚ), -4], ![(-5 / 6 : ℚ), 0, 0, (1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, (-3 / 4 : ℚ), 0, (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 11 : ℚ), 0], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (2 / 11 : ℚ), (-2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 7 : ℚ), (-26 / 7 : ℚ), 0, 0], ![(4 / 21 : ℚ), (-37 / 21 : ℚ), (-41 / 21 : ℚ), (4 / 21 : ℚ), (-80 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-1 / 7 : ℚ), (-2 / 7 : ℚ), (6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ), -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-4 / 9 : ℚ), (-4 / 9 : ℚ), 0, (-4 / 9 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 7 : ℚ), 0, 0, (-8 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), (-8 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), 0, (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ), (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (1 / 5 : ℚ), (-7 / 5 : ℚ), (-1 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, 0, (-7 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-8 / 11 : ℚ), (-12 / 11 : ℚ), (-10 / 11 : ℚ), 0], ![(4 / 11 : ℚ), (-10 / 11 : ℚ), (-7 / 11 : ℚ), -2, (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, 0, (-3 / 2 : ℚ)], ![(-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-2 / 9 : ℚ), 0, -2], ![-1, (-1 / 3 : ℚ), (-1 / 9 : ℚ), (-1 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 3 : ℚ), (-4 / 9 : ℚ)], ![0, (-4 / 3 : ℚ), (-2 / 3 : ℚ), (-28 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 8 : ℚ), 0, (-3 / 8 : ℚ), (-9 / 2 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), -1, (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, 0, (-6 / 13 : ℚ), 0], ![(-4 / 13 : ℚ), (-2 / 13 : ℚ), (-1 / 13 : ℚ), (2 / 13 : ℚ), (-2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, 0, 0, (-8 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (-2 / 11 : ℚ), (10 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 4 : ℚ), (-7 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ)], ![0, (-3 / 8 : ℚ), (-1 / 2 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![0, (-6 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-2 / 3 : ℚ), (-7 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, -1, (-4 / 3 : ℚ), -1, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (2 / 15 : ℚ), 0, (-8 / 15 : ℚ), (-2 / 3 : ℚ)], ![(-2 / 5 : ℚ), 0, (-1 / 15 : ℚ), (2 / 15 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 11 : ℚ), 0], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0], ![0, (-1 / 2 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-13 / 10 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), (-13 / 10 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), (-7 / 16 : ℚ), 0, (-17 / 16 : ℚ), (-23 / 48 : ℚ)], ![(-7 / 16 : ℚ), (-7 / 16 : ℚ), (-1 / 48 : ℚ), (-17 / 16 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 8 : ℚ), 0, (-11 / 8 : ℚ), 0], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-11 / 8 : ℚ), (5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), -3], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-3 / 2 : ℚ), (-13 / 4 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 77 : ℚ), (-1 / 7 : ℚ), 0, (-12 / 11 : ℚ), (-18 / 77 : ℚ)], ![(-6 / 77 : ℚ), (-17 / 77 : ℚ), (-3 / 77 : ℚ), (-162 / 77 : ℚ), (102 / 77 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 41 : ℚ), (-97 / 82 : ℚ), (-86 / 41 : ℚ), (-3 / 82 : ℚ), (33 / 82 : ℚ)], ![(39 / 82 : ℚ), (-103 / 82 : ℚ), (-89 / 82 : ℚ), 0, (3 / 41 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 10 : ℚ), (-67 / 30 : ℚ), 0, 0], ![(1 / 10 : ℚ), (-7 / 5 : ℚ), (-7 / 6 : ℚ), (1 / 10 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-6 / 17 : ℚ), 0, (-20 / 17 : ℚ), (-38 / 17 : ℚ)], ![(-3 / 17 : ℚ), (-9 / 17 : ℚ), 0, (-37 / 17 : ℚ), (-19 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 65 : ℚ), (-22 / 65 : ℚ), 0, (-79 / 65 : ℚ), (-124 / 65 : ℚ)], ![(-12 / 65 : ℚ), (-34 / 65 : ℚ), (-6 / 65 : ℚ), (-146 / 65 : ℚ), (56 / 65 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, 0, (-2 / 11 : ℚ), (-8 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (-15 / 11 : ℚ), (10 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, 0, (-2 / 13 : ℚ), (-6 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-2 / 13 : ℚ), (-1 / 13 : ℚ), (-17 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ), (-14 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, (4 / 9 : ℚ), (-2 / 9 : ℚ), (-28 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (1 / 9 : ℚ), (-13 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-2 / 9 : ℚ), 0, 0, (-29 / 9 : ℚ)], ![(-1 / 18 : ℚ), (-5 / 18 : ℚ), 0, (-7 / 9 : ℚ), (-29 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (2 / 11 : ℚ), (8 / 11 : ℚ), (-10 / 11 : ℚ), (-12 / 11 : ℚ)], ![(-6 / 11 : ℚ), 0, (4 / 11 : ℚ), (12 / 11 : ℚ), (-6 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 37 : ℚ), (6 / 37 : ℚ), 0, (-30 / 37 : ℚ), (-42 / 37 : ℚ)], ![(-18 / 37 : ℚ), 0, (-3 / 37 : ℚ), (36 / 37 : ℚ), (6 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-16 / 5 : ℚ)], ![(2 / 5 : ℚ), (-4 / 5 : ℚ), (-7 / 10 : ℚ), (1 / 5 : ℚ), (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (1 / 3 : ℚ), (-1 / 2 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 8 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), (-7 / 16 : ℚ), 0, (-23 / 48 : ℚ), (-49 / 12 : ℚ)], ![(-7 / 16 : ℚ), (-7 / 16 : ℚ), (-1 / 48 : ℚ), (1 / 24 : ℚ), (-49 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-4 / 9 : ℚ), (-4 / 9 : ℚ), 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), -1, (-3 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 12 : ℚ), 0, 0, (-13 / 3 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 4 : ℚ), (-13 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-7 / 3 : ℚ)], ![-1, 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), -1, (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 2 : ℚ), 0, -1, (-1 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-8 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), -3, (-1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 7 : ℚ), 0, 0, 0], ![(2 / 7 : ℚ), (-6 / 7 : ℚ), (-10 / 7 : ℚ), (-6 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), -1, (-3 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 7 : ℚ), 0, 0, 0], ![(2 / 7 : ℚ), (-10 / 7 : ℚ), (-16 / 7 : ℚ), (-10 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), -2, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 2 : ℚ), 0, -1, (-1 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ)], ![(1 / 3 : ℚ), -2, 0, (-11 / 3 : ℚ), (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), -1, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, 0], ![(1 / 2 : ℚ), -1, (-5 / 2 : ℚ), (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, -2], ![(1 / 10 : ℚ), (-13 / 10 : ℚ), 0, -4, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), -1, (-8 / 5 : ℚ), -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 4 : ℚ), -1, 0, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 4 : ℚ), 0, 0, -1, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, -1, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 10 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![(-3 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![0, 0, (3 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, (-1 / 2 : ℚ), (1 / 4 : ℚ), -4, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 10 : ℚ), (-1 / 10 : ℚ), 0, 0], ![(1 / 10 : ℚ), (-1 / 2 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), 0, (1 / 3 : ℚ), (-11 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), (5 / 3 : ℚ), 0], ![(-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), -2, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, (-1 / 2 : ℚ), 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-10 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), -1, (-1 / 3 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 4 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-13 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), 0, 0, 0], ![0, (-8 / 5 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 5 : ℚ), (-3 / 25 : ℚ), 0, (24 / 25 : ℚ)], ![(6 / 5 : ℚ), (-46 / 25 : ℚ), 0, (-86 / 25 : ℚ), (-18 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-27 / 22 : ℚ), (-1 / 22 : ℚ), 0, (1 / 2 : ℚ)], ![(13 / 22 : ℚ), (-29 / 22 : ℚ), 0, (-28 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-5 / 2 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-19 / 13 : ℚ), 0, 0, 0], ![(2 / 13 : ℚ), (-21 / 13 : ℚ), (2 / 13 : ℚ), (-40 / 13 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 9 : ℚ), (-1 / 9 : ℚ), 0, 0], ![(1 / 9 : ℚ), (-16 / 9 : ℚ), 0, (-10 / 3 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, -1, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, (-1 / 2 : ℚ), (-3 / 4 : ℚ), -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 12 : ℚ), 0, (-41 / 12 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 12 : ℚ), (-7 / 12 : ℚ), (-13 / 4 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-13 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-10 / 3 : ℚ)], ![(-4 / 9 : ℚ), 0, (-13 / 9 : ℚ), (-40 / 9 : ℚ), (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), -1, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -3, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 7 : ℚ), 0, (-1 / 7 : ℚ), 0], ![(1 / 7 : ℚ), (-5 / 7 : ℚ), (-8 / 7 : ℚ), (3 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 7 : ℚ), 0, 0, 0], ![(2 / 7 : ℚ), (-6 / 7 : ℚ), (-10 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, (-1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (-1 / 2 : ℚ), (-4 / 3 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), -1, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, 0], ![0, (-2 / 3 : ℚ), -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-3 / 5 : ℚ), -1], ![(-2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, (-1 / 2 : ℚ), -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, 0, (-1 / 4 : ℚ), 0, (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-4 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), -1, (-8 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-22 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 7 : ℚ), 0, (-6 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (-10 / 7 : ℚ), (-44 / 7 : ℚ), (-10 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), 0, (-44 / 9 : ℚ), 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), -1, (-8 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 3 : ℚ), -1, (-8 / 3 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-6 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, 0], ![(2 / 5 : ℚ), (-6 / 5 : ℚ), (-16 / 5 : ℚ), (4 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 2 : ℚ), -1, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), 0, 0], ![(-6 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, (-2 / 11 : ℚ), 0, (-8 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-6 / 11 : ℚ), (-2 / 11 : ℚ), (10 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![0, (-4 / 5 : ℚ), (-14 / 5 : ℚ), (-4 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-2 / 7 : ℚ), 0, (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 3 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ)], ![0, (-4 / 3 : ℚ), (-28 / 9 : ℚ), (-4 / 3 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (-16 / 9 : ℚ), (-8 / 3 : ℚ), (-16 / 9 : ℚ), 0], ![0, (-16 / 9 : ℚ), (-56 / 9 : ℚ), (-16 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-3 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, (-7 / 6 : ℚ)], ![(1 / 6 : ℚ), -1, 0, 0, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, 0, -1], ![(-1 / 3 : ℚ), 0, 0, -1, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-5 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (7 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![(-1 / 2 : ℚ), 0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0], ![(-1 / 6 : ℚ), 0, (2 / 3 : ℚ), (-5 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 19 : ℚ), (22 / 19 : ℚ), (-35 / 19 : ℚ), 0, (29 / 19 : ℚ)], ![(-33 / 19 : ℚ), (20 / 19 : ℚ), (2 / 19 : ℚ), (-2 / 19 : ℚ), (20 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (1 / 12 : ℚ), (-1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-3 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), 0, -3]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 2 : ℚ), -2, 0, 0], ![(-3 / 2 : ℚ), (1 / 2 : ℚ), -2, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .yy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 4 : ℚ), -2, 2, 0], ![(-9 / 4 : ℚ), (1 / 4 : ℚ), -2, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), 0, (-5 / 12 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 12 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), 0, (-6 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 6 : ℚ), (-11 / 6 : ℚ), (1 / 6 : ℚ), (11 / 6 : ℚ)], ![(-13 / 6 : ℚ), (1 / 6 : ℚ), (-11 / 6 : ℚ), 0, (11 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-6 / 5 : ℚ), 0], ![0, (-4 / 5 : ℚ), 0, (-14 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), 0, (-14 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-6 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 13 : ℚ), (-15 / 13 : ℚ), 0, (-15 / 13 : ℚ), (7 / 26 : ℚ)], ![(11 / 26 : ℚ), (-16 / 13 : ℚ), 0, (-30 / 13 : ℚ), (-5 / 26 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (-8 / 7 : ℚ), 0, (-8 / 7 : ℚ), (5 / 14 : ℚ)], ![(3 / 7 : ℚ), (-17 / 14 : ℚ), 0, (-16 / 7 : ℚ), (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, -3, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-7 / 4 : ℚ), 0, -3, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0], ![0, (-3 / 2 : ℚ), 0, (-8 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-15 / 11 : ℚ), 0, (-15 / 11 : ℚ), (-6 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-17 / 11 : ℚ), 0, (-30 / 11 : ℚ), (2 / 11 : ℚ)]] }
]

theorem conicDetC07_checked : conicDetC07.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
