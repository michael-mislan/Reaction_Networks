import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC20 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, (-5 / 4 : ℚ), 0], ![0, 2, -2, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![(1 / 2 : ℚ), 2, -2, (1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -4], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![(1 / 3 : ℚ), 2, -2, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![(1 / 2 : ℚ), 2, -2, (1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![0, 2, -2, (1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 13 : ℚ), (-6 / 13 : ℚ), (-22 / 13 : ℚ), 0, (6 / 13 : ℚ)], ![(2 / 13 : ℚ), (27 / 13 : ℚ), (-24 / 13 : ℚ), (2 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-22 / 7 : ℚ), (-22 / 7 : ℚ)], ![(-5 / 7 : ℚ), (3 / 7 : ℚ), 0, (-10 / 7 : ℚ), (-22 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 19 : ℚ), (-9 / 19 : ℚ), (8 / 19 : ℚ), (-84 / 19 : ℚ), (-40 / 19 : ℚ)], ![(-9 / 19 : ℚ), 0, (6 / 19 : ℚ), (2 / 19 : ℚ), (2 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 7 : ℚ), (-9 / 14 : ℚ), (-13 / 7 : ℚ), 0, 0], ![(1 / 7 : ℚ), (29 / 14 : ℚ), (-13 / 7 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), (1 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-17 / 11 : ℚ), (2 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-32 / 11 : ℚ), (-4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-11 / 7 : ℚ), (-11 / 7 : ℚ), (2 / 7 : ℚ), 0], ![0, (-11 / 7 : ℚ), (-2 / 7 : ℚ), (-24 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, -2, (1 / 2 : ℚ), 0], ![0, -2, 0, (-9 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (4 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 11 : ℚ), (-34 / 11 : ℚ), (-34 / 11 : ℚ), (8 / 11 : ℚ), 0], ![0, (-34 / 11 : ℚ), (-8 / 11 : ℚ), (-76 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-5 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), (-1 / 4 : ℚ), 0, -3]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 8 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), (-5 / 4 : ℚ), 0], ![0, (-3 / 2 : ℚ), (-1 / 4 : ℚ), -3, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, -2, -2, 0], ![0, -2, 0, (-9 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ), (-5 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), -3, -3, (-7 / 3 : ℚ), 0], ![0, -3, (-2 / 3 : ℚ), -6, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, -2, -1, 0], ![0, -2, 0, (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 18 : ℚ), (-7 / 9 : ℚ), (-7 / 9 : ℚ), (-4 / 9 : ℚ), 0], ![(-7 / 18 : ℚ), (-7 / 9 : ℚ), (-1 / 9 : ℚ), (-4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 16 : ℚ), (-9 / 8 : ℚ), (-17 / 16 : ℚ), 0, (3 / 16 : ℚ)], ![(1 / 4 : ℚ), (-9 / 8 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, (-11 / 10 : ℚ), (1 / 20 : ℚ)], ![(-7 / 20 : ℚ), 0, (-1 / 20 : ℚ), (-11 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, -2, (1 / 4 : ℚ), 0], ![(1 / 4 : ℚ), -2, 0, (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-13 / 8 : ℚ), (-5 / 4 : ℚ), (-1 / 8 : ℚ), (7 / 8 : ℚ)], ![(1 / 24 : ℚ), (-15 / 8 : ℚ), (-1 / 4 : ℚ), 0, (-7 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 10 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), (-1 / 10 : ℚ), (9 / 10 : ℚ)], ![(13 / 10 : ℚ), (-17 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-29 / 24 : ℚ), (-13 / 12 : ℚ), (-1 / 24 : ℚ), (1 / 12 : ℚ)], ![(-1 / 24 : ℚ), (-31 / 24 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 5 : ℚ), -4], ![(-3 / 10 : ℚ), 0, 0, (-29 / 10 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-3 / 2 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-17 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)], ![0, (-8 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (-11 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 20 : ℚ), (1 / 5 : ℚ)], ![(1 / 4 : ℚ), (-23 / 20 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 8 : ℚ), -4], ![(-1 / 8 : ℚ), 0, 0, (-5 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-7 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, -2, (11 / 8 : ℚ), 0], ![(1 / 8 : ℚ), -2, 0, (-11 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 15 : ℚ), (-12 / 5 : ℚ), (-12 / 5 : ℚ), (29 / 15 : ℚ), 0], ![(1 / 15 : ℚ), (-12 / 5 : ℚ), (-4 / 15 : ℚ), (-29 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), -2, -2, (13 / 12 : ℚ), 0], ![(7 / 6 : ℚ), -2, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 16 : ℚ), (-35 / 16 : ℚ), (-33 / 16 : ℚ), (21 / 16 : ℚ), 0], ![(23 / 16 : ℚ), (-35 / 16 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, -2, (1 / 4 : ℚ), 0], ![0, -2, 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-7 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 16 : ℚ), (-19 / 8 : ℚ), (-19 / 8 : ℚ), (1 / 4 : ℚ), 0], ![(-1 / 16 : ℚ), (-19 / 8 : ℚ), (-1 / 4 : ℚ), (-13 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, -2, (-1 / 2 : ℚ), 0], ![0, -2, 0, (-7 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 7 : ℚ), 0, (-10 / 7 : ℚ), (2 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-10 / 7 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-17 / 11 : ℚ), (2 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (-32 / 11 : ℚ), (-4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 15 : ℚ), 0, 0, (2 / 15 : ℚ), (-8 / 15 : ℚ)], ![(-4 / 15 : ℚ), (-2 / 15 : ℚ), (-1 / 15 : ℚ), 0, (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 3 : ℚ), -3, (1 / 3 : ℚ), 0], ![0, (-5 / 3 : ℚ), (-5 / 3 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 7 : ℚ), (4 / 7 : ℚ), (4 / 7 : ℚ), (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-8 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-10 / 3 : ℚ), (-52 / 9 : ℚ), (8 / 9 : ℚ), 0], ![(-2 / 9 : ℚ), (-10 / 3 : ℚ), (-10 / 3 : ℚ), (-20 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 8 : ℚ), (-5 / 4 : ℚ), 0], ![(-1 / 8 : ℚ), 0, 0, (-5 / 4 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 9 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 6 : ℚ), (-7 / 18 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 8 : ℚ), (-17 / 8 : ℚ), (-9 / 8 : ℚ), (-1 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-9 / 8 : ℚ), (-9 / 8 : ℚ), (-19 / 8 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 7 : ℚ), (8 / 21 : ℚ), (4 / 21 : ℚ), (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (4 / 21 : ℚ), (-4 / 21 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 25 : ℚ), (-6 / 25 : ℚ), (-28 / 25 : ℚ), (-8 / 25 : ℚ), (-24 / 25 : ℚ)], ![0, (-18 / 25 : ℚ), (-4 / 5 : ℚ), (-28 / 25 : ℚ), (12 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), (-13 / 3 : ℚ), (-1 / 2 : ℚ), -1], ![(-2 / 3 : ℚ), (-5 / 2 : ℚ), (-5 / 2 : ℚ), (-11 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (-1 / 15 : ℚ), (-8 / 15 : ℚ), (-1 / 15 : ℚ), (-4 / 15 : ℚ)], ![0, (-1 / 5 : ℚ), (-1 / 3 : ℚ), (-1 / 5 : ℚ), (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 7 : ℚ), (8 / 21 : ℚ), (2 / 7 : ℚ), (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (4 / 21 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (2 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), -2], ![(-3 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 9 : ℚ), 0, (1 / 6 : ℚ), (-4 / 3 : ℚ), (-5 / 12 : ℚ)], ![(-1 / 9 : ℚ), 0, 0, (-4 / 3 : ℚ), (5 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 48 : ℚ), (-1 / 48 : ℚ), 0, (-17 / 16 : ℚ), (-41 / 48 : ℚ)], ![(-37 / 48 : ℚ), (-1 / 48 : ℚ), (-1 / 48 : ℚ), (-17 / 16 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 5 : ℚ), 0, (1 / 10 : ℚ), (-6 / 5 : ℚ), (1 / 10 : ℚ)], ![(-7 / 10 : ℚ), 0, 0, (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), -3], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-13 / 9 : ℚ), (-8 / 3 : ℚ), 0, (-4 / 9 : ℚ)], ![0, (-13 / 9 : ℚ), (-13 / 9 : ℚ), 0, (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 9 : ℚ), (1 / 9 : ℚ), 0, (-13 / 9 : ℚ), (-4 / 9 : ℚ)], ![(-1 / 9 : ℚ), 0, (-1 / 18 : ℚ), (-25 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 22 : ℚ), 0, (1 / 4 : ℚ), (-53 / 44 : ℚ), (-35 / 44 : ℚ)], ![(-29 / 44 : ℚ), (-3 / 44 : ℚ), (1 / 11 : ℚ), (-103 / 44 : ℚ), (3 / 44 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, 0, (-9 / 8 : ℚ), (1 / 24 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 24 : ℚ), (-1 / 48 : ℚ), (-53 / 24 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 34 : ℚ), 0, (-1 / 17 : ℚ), (-26 / 17 : ℚ), (-50 / 17 : ℚ)], ![(-3 / 34 : ℚ), (-3 / 17 : ℚ), (-1 / 34 : ℚ), (-49 / 17 : ℚ), (-25 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-16 / 11 : ℚ), (-74 / 33 : ℚ), (-1 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-18 / 11 : ℚ), (-40 / 33 : ℚ), 0, (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 60 : ℚ), 0, 0, (-1 / 10 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 60 : ℚ), (-1 / 10 : ℚ), (-1 / 20 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-4 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-14 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 9 : ℚ), (-28 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-1 / 9 : ℚ), (-13 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![0, (-3 / 10 : ℚ), (-1 / 10 : ℚ), 0, (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-8 / 9 : ℚ)], ![0, (-4 / 9 : ℚ), (-8 / 9 : ℚ), 0, (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-23 / 9 : ℚ), (-14 / 3 : ℚ), (16 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, (-23 / 9 : ℚ), (-23 / 9 : ℚ), (-16 / 9 : ℚ), (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 34 : ℚ), (3 / 17 : ℚ), (5 / 17 : ℚ), (-21 / 34 : ℚ), (-9 / 17 : ℚ)], ![(-9 / 34 : ℚ), 0, (5 / 34 : ℚ), (3 / 17 : ℚ), (-9 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ), (-7 / 13 : ℚ), (-10 / 13 : ℚ)], ![(-3 / 13 : ℚ), 0, 0, (2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 8 : ℚ), (-53 / 24 : ℚ), (-25 / 6 : ℚ), (11 / 8 : ℚ), 0], ![(37 / 24 : ℚ), (-53 / 24 : ℚ), (-17 / 8 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ), -1], ![(-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 6 : ℚ), -1, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), 0, 0, (4 / 9 : ℚ), (-8 / 9 : ℚ)], ![0, (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 3 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 13 : ℚ), (-32 / 13 : ℚ), (-60 / 13 : ℚ), (8 / 13 : ℚ), 0], ![(-1 / 13 : ℚ), (-32 / 13 : ℚ), (-32 / 13 : ℚ), (-15 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-16 / 21 : ℚ), (-2 / 7 : ℚ), 0], ![0, (-6 / 7 : ℚ), (-8 / 21 : ℚ), (-6 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, 0, (-12 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-4 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-11 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-21 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (-8 / 5 : ℚ), (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 7 : ℚ), (3 / 7 : ℚ), -1], ![(-3 / 7 : ℚ), (-3 / 7 : ℚ), (-6 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (-8 / 5 : ℚ), (-12 / 5 : ℚ), (-8 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (16 / 17 : ℚ), (16 / 17 : ℚ), (-24 / 17 : ℚ)], ![(-16 / 17 : ℚ), 0, (-32 / 17 : ℚ), (-32 / 17 : ℚ), (-24 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), (2 / 3 : ℚ), 0], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-4 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 9 : ℚ), (2 / 9 : ℚ), 0], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-26 / 9 : ℚ), (-4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 6 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 7 : ℚ), 0, -1], ![(-3 / 7 : ℚ), (-3 / 7 : ℚ), (-6 / 7 : ℚ), (-3 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 25 : ℚ), 0, (12 / 25 : ℚ), (6 / 25 : ℚ), (-52 / 25 : ℚ)], ![(-14 / 25 : ℚ), (-12 / 25 : ℚ), (-4 / 5 : ℚ), 0, (12 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), 0, (-3 / 8 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), (2 / 3 : ℚ), 0], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-18 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 4 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), 0, (2 / 3 : ℚ), 0, (-4 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(6 / 31 : ℚ), 0, (12 / 31 : ℚ), (12 / 31 : ℚ), (-40 / 31 : ℚ)], ![(-18 / 31 : ℚ), (-12 / 31 : ℚ), (-12 / 31 : ℚ), 0, (-14 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 7 : ℚ), (4 / 7 : ℚ), 0, (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-8 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, -1, 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), (-2 / 5 : ℚ), (4 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-8 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 10 : ℚ), (1 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (2 / 3 : ℚ), 0], ![0, (-2 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), 0, (1 / 10 : ℚ), (1 / 10 : ℚ)], ![0, (-1 / 10 : ℚ), 0, (-2 / 5 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (3 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 12 : ℚ)], ![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (2 / 3 : ℚ), (-4 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, (-8 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (2 / 3 : ℚ), (1 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, (-8 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), 0, (-5 / 3 : ℚ), 0, 0], ![(-1 / 9 : ℚ), (-2 / 9 : ℚ), (-28 / 9 : ℚ), (-11 / 9 : ℚ), (-4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 9 : ℚ), 0, (-5 / 3 : ℚ), (2 / 9 : ℚ), (-2 / 3 : ℚ)], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-28 / 9 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 28 : ℚ), (-33 / 28 : ℚ), (-1 / 28 : ℚ), (4 / 7 : ℚ), (11 / 28 : ℚ)], ![(15 / 28 : ℚ), (-5 / 4 : ℚ), 0, (-13 / 7 : ℚ), (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 9 : ℚ), (2 / 9 : ℚ), (-4 / 9 : ℚ)], ![(-2 / 9 : ℚ), 0, (-8 / 3 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 12 : ℚ), (-5 / 4 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)], ![(1 / 2 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), (-5 / 2 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), 0, (-5 / 4 : ℚ), (1 / 12 : ℚ), (-23 / 12 : ℚ)], ![(-1 / 24 : ℚ), (-1 / 12 : ℚ), (-29 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-5 / 4 : ℚ), (-1 / 20 : ℚ), (6 / 5 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 20 : ℚ), (-27 / 20 : ℚ), 0, (-7 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), 0, (-11 / 7 : ℚ), (2 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-4 / 7 : ℚ), 0, (-20 / 7 : ℚ), 0, (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 6 : ℚ)], ![0, (-1 / 12 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (-21 / 20 : ℚ), (-1 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-3 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)], ![(1 / 2 : ℚ), (-3 / 4 : ℚ), -2, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 3 : ℚ), 0, (-4 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), (-4 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 8 : ℚ), (1 / 4 : ℚ), 0, (-1 / 8 : ℚ)], ![0, (-1 / 8 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), 0, 0], ![0, (-1 / 2 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 2, 0, 0], ![0, (-1 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), (-5 / 22 : ℚ), (1 / 11 : ℚ), 0, (-1 / 11 : ℚ)], ![(2 / 11 : ℚ), (-7 / 22 : ℚ), (-8 / 11 : ℚ), (1 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (-7 / 11 : ℚ), (-10 / 11 : ℚ)], ![(-3 / 11 : ℚ), 0, (-2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, (2 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 10 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), (9 / 5 : ℚ), (-1 / 5 : ℚ)], ![(17 / 10 : ℚ), (-9 / 5 : ℚ), (-21 / 5 : ℚ), (9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 5 : ℚ), (4 / 5 : ℚ), (-2 / 5 : ℚ), (-18 / 5 : ℚ)], ![(-4 / 5 : ℚ), (2 / 5 : ℚ), (-8 / 5 : ℚ), (-2 / 5 : ℚ), (6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 3 : ℚ), (-2 / 3 : ℚ), -1], ![(-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-2 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 7 : ℚ), (3 / 7 : ℚ), -1], ![(-3 / 7 : ℚ), (-3 / 7 : ℚ), (-6 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 9 : ℚ), (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (-6 / 17 : ℚ), (8 / 17 : ℚ), (8 / 17 : ℚ), 0], ![(-2 / 17 : ℚ), (-6 / 17 : ℚ), (-28 / 17 : ℚ), (-22 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 37 : ℚ), (-8 / 37 : ℚ), (60 / 37 : ℚ), 0, 0], ![(2 / 37 : ℚ), (-20 / 37 : ℚ), (-100 / 37 : ℚ), (-28 / 37 : ℚ), (6 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), 2, 0, -1], ![(-1 / 4 : ℚ), (-1 / 8 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 2, (-1 / 2 : ℚ), (1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), (-7 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 12 : ℚ), (-1 / 3 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 4 : ℚ), (-7 / 4 : ℚ), (-9 / 8 : ℚ)], ![(-3 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (4 / 11 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ)], ![0, (-6 / 11 : ℚ), (-16 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 3 : ℚ), (-8 / 3 : ℚ), -1], ![(-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), (2 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, -1, (-3 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-4 / 33 : ℚ), (-1 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (-14 / 33 : ℚ), (-3 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 6 : ℚ), 0, (-1 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-1 / 6 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 25 : ℚ), (-2 / 25 : ℚ), (-4 / 25 : ℚ), 0, (-12 / 25 : ℚ)], ![(-4 / 25 : ℚ), (-14 / 25 : ℚ), (-4 / 5 : ℚ), (-16 / 25 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 7 : ℚ), (-5 / 7 : ℚ), (-2 / 7 : ℚ), (-3 / 14 : ℚ), (-6 / 7 : ℚ)], ![0, (-8 / 7 : ℚ), -1, (-9 / 14 : ℚ), (3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, (-3 / 4 : ℚ)], ![-1, 0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0], ![0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 10 : ℚ), (-2 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), 0, (-1 / 2 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0], ![0, (-2 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), 0, (1 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (5 / 8 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-11 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (-7 / 6 : ℚ)], ![(-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0], ![0, (-2 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), 0, (-8 / 5 : ℚ), 0, (-7 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-3 / 10 : ℚ), (-16 / 5 : ℚ), 0, (7 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-7 / 6 : ℚ), 0, (-7 / 6 : ℚ), (5 / 12 : ℚ)], ![(7 / 12 : ℚ), (-5 / 4 : ℚ), 0, (-7 / 3 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-21 / 34 : ℚ), (-19 / 34 : ℚ), (-21 / 34 : ℚ), (3 / 34 : ℚ)], ![(-3 / 34 : ℚ), (-12 / 17 : ℚ), (-19 / 17 : ℚ), (-21 / 17 : ℚ), (-3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 34 : ℚ), (-43 / 34 : ℚ), (1 / 34 : ℚ), (-35 / 17 : ℚ)], ![(-3 / 17 : ℚ), 0, (-43 / 17 : ℚ), (1 / 17 : ℚ), (-4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-19 / 16 : ℚ), 0, (-19 / 16 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 32 : ℚ), (-41 / 32 : ℚ), 0, (-19 / 8 : ℚ), (3 / 32 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), -1, (-1 / 4 : ℚ), (-17 / 8 : ℚ)], ![0, (-1 / 8 : ℚ), -2, (-1 / 2 : ℚ), (-17 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(18 / 17 : ℚ), (18 / 17 : ℚ), (-3 / 17 : ℚ), 0, (-32 / 17 : ℚ)], ![(-18 / 17 : ℚ), (15 / 17 : ℚ), (-43 / 17 : ℚ), (-3 / 17 : ℚ), (32 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 24 : ℚ), (-1 / 24 : ℚ), 0, (-7 / 6 : ℚ)], ![(-7 / 12 : ℚ), (1 / 4 : ℚ), (-17 / 8 : ℚ), (-1 / 24 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-13 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(11 / 6 : ℚ), (23 / 22 : ℚ), (-1 / 22 : ℚ), 0, (-47 / 11 : ℚ)], ![(-62 / 33 : ℚ), 1, (-47 / 22 : ℚ), (-1 / 22 : ℚ), (-15 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-608 / 195 : ℚ), (-326 / 195 : ℚ), (-2 / 39 : ℚ), (-28 / 13 : ℚ), (-2 / 39 : ℚ)], ![(44 / 195 : ℚ), (-112 / 65 : ℚ), 0, (-170 / 39 : ℚ), (88 / 195 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-21 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-11 / 4 : ℚ), (-1 / 4 : ℚ), (-21 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, 0, (-3 / 8 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (-1 / 4 : ℚ), (3 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 8 : ℚ)], ![0, (-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ), 0, (-8 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (1 / 8 : ℚ), 0, (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-5 / 8 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (-7 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-3 / 10 : ℚ), (1 / 10 : ℚ), 0, (1 / 5 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, 0, 0], ![0, (-1 / 2 : ℚ), (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 33 : ℚ), (4 / 33 : ℚ), (1 / 11 : ℚ), (-19 / 33 : ℚ), (-7 / 11 : ℚ)], ![(-7 / 33 : ℚ), (-2 / 33 : ℚ), 0, (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 40 : ℚ), (-3 / 40 : ℚ), (3 / 40 : ℚ), (-19 / 40 : ℚ), (-13 / 20 : ℚ)], ![(-7 / 40 : ℚ), (-9 / 40 : ℚ), 0, (3 / 20 : ℚ), (3 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), (-2 / 5 : ℚ), (1 / 10 : ℚ)], ![0, (-1 / 5 : ℚ), (-1 / 2 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, 0, 0], ![0, (-1 / 6 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (5 / 8 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-11 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (-23 / 13 : ℚ), (-24 / 13 : ℚ), (23 / 13 : ℚ), 0], ![(20 / 13 : ℚ), (-23 / 13 : ℚ), (-54 / 13 : ℚ), (23 / 13 : ℚ), (3 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 13 : ℚ), (-3 / 13 : ℚ), (-4 / 13 : ℚ), (3 / 13 : ℚ), (-40 / 13 : ℚ)], ![0, (-3 / 13 : ℚ), (-14 / 13 : ℚ), (3 / 13 : ℚ), (6 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0, (1 / 6 : ℚ)], ![0, (-1 / 3 : ℚ), (-5 / 6 : ℚ), 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (3 / 7 : ℚ), -1], ![(-3 / 7 : ℚ), (-3 / 7 : ℚ), (-3 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 9 : ℚ), (4 / 27 : ℚ), (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (-4 / 27 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (8 / 17 : ℚ), (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), 0, (-8 / 17 : ℚ), (-16 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, (5 / 6 : ℚ), (-23 / 32 : ℚ)], ![(-11 / 32 : ℚ), 0, (-3 / 32 : ℚ), (-1 / 3 : ℚ), (-5 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(14 / 25 : ℚ), (12 / 25 : ℚ), (6 / 25 : ℚ), (28 / 25 : ℚ), (-76 / 25 : ℚ)], ![(-26 / 25 : ℚ), 0, 0, 0, (12 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (7 / 9 : ℚ), (-2 / 3 : ℚ), 0], ![(-2 / 9 : ℚ), (-2 / 3 : ℚ), (-25 / 9 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 39 : ℚ), 0, (2 / 13 : ℚ), (-4 / 3 : ℚ), (-14 / 13 : ℚ)], ![(-14 / 39 : ℚ), (-4 / 13 : ℚ), 0, (4 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-8 / 33 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ)], ![0, (-6 / 11 : ℚ), (-28 / 33 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 3 : ℚ), -1], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (2 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 8 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 11 : ℚ), (-5 / 22 : ℚ), (-4 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (-3 / 11 : ℚ), (-7 / 22 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 25 : ℚ), (-8 / 25 : ℚ), (-8 / 25 : ℚ), 0, 0], ![(2 / 25 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-44 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-5 / 7 : ℚ), (-8 / 7 : ℚ)], ![0, (-6 / 7 : ℚ), (-6 / 7 : ℚ), -1, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), 0, (1 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 16 : ℚ), (9 / 16 : ℚ), (-9 / 4 : ℚ), (1 / 16 : ℚ), (-5 / 4 : ℚ)], ![(-5 / 16 : ℚ), 0, (-71 / 16 : ℚ), 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 22 : ℚ), (1 / 11 : ℚ), (-41 / 22 : ℚ), (-9 / 22 : ℚ), (-9 / 11 : ℚ)], ![(-3 / 22 : ℚ), 0, (-40 / 11 : ℚ), (-1 / 2 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 3 : ℚ), (1 / 4 : ℚ), (-17 / 8 : ℚ), 0, (1 / 24 : ℚ)], ![(-11 / 8 : ℚ), (5 / 24 : ℚ), (-101 / 24 : ℚ), (-1 / 24 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 24 : ℚ), (7 / 12 : ℚ), (-7 / 3 : ℚ), (1 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-5 / 8 : ℚ), (1 / 2 : ℚ), (-55 / 12 : ℚ), 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 9 : ℚ), (11 / 18 : ℚ), (-22 / 9 : ℚ), (1 / 9 : ℚ), (-43 / 9 : ℚ)], ![(-2 / 3 : ℚ), (1 / 2 : ℚ), (-43 / 9 : ℚ), 0, (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 2 : ℚ), (-1 / 10 : ℚ), 0, (-7 / 5 : ℚ)], ![(-1 / 2 : ℚ), (2 / 5 : ℚ), (-11 / 5 : ℚ), (-1 / 10 : ℚ), (7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), (-7 / 6 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), (11 / 12 : ℚ)], ![(13 / 12 : ℚ), (-7 / 4 : ℚ), 0, (-9 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(59 / 33 : ℚ), 1, (-1 / 22 : ℚ), 0, (-46 / 11 : ℚ)], ![(-11 / 6 : ℚ), (21 / 22 : ℚ), (-23 / 11 : ℚ), (-1 / 22 : ℚ), (-29 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-11 / 9 : ℚ), (-1 / 9 : ℚ), (-20 / 9 : ℚ), (-1 / 9 : ℚ)], ![(1 / 18 : ℚ), (-11 / 6 : ℚ), 0, (-7 / 3 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ), 0, (1 / 4 : ℚ)], ![(1 / 2 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), (-1 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 22 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ), (-7 / 22 : ℚ), (-9 / 22 : ℚ)], ![(-3 / 22 : ℚ), 0, 0, (1 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (-3 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 10 : ℚ)], ![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-3, (-3 / 2 : ℚ), (-7 / 4 : ℚ), (3 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, (-3 / 2 : ℚ), (-7 / 4 : ℚ), (3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, (-7 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 37 : ℚ), 0, 0, (12 / 37 : ℚ), 0], ![(2 / 37 : ℚ), (-28 / 37 : ℚ), (-28 / 37 : ℚ), (-38 / 37 : ℚ), (6 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), 0, (-2 / 9 : ℚ), (4 / 9 : ℚ), (-8 / 9 : ℚ)], ![0, (-8 / 9 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (8 / 17 : ℚ), (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), 0, 0, (-16 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 15 : ℚ), 0, (4 / 15 : ℚ), (4 / 15 : ℚ), (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-4 / 15 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (4 / 7 : ℚ), (4 / 7 : ℚ), (4 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-6 / 7 : ℚ), 0, 0, 0, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ)], ![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), (-9 / 8 : ℚ)], ![(-3 / 4 : ℚ), 0, 0, (-1 / 2 : ℚ), (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ)], ![0, (-6 / 11 : ℚ), (-6 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ), 0], ![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ)], ![0, (-1 / 9 : ℚ), (-1 / 9 : ℚ), (4 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), 0, (1 / 5 : ℚ), 0]] }
]

theorem conicDetC20_checked : conicDetC20.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
