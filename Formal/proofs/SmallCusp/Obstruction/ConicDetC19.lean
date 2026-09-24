import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC19 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, -1, (-1 / 3 : ℚ), 0], ![1, 1, 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![1, 0, 1, (-1 / 3 : ℚ), 0], ![-1, -1, 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-29 / 5 : ℚ)], ![0, 0, 0, 1, (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -5], ![0, 0, 0, 1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, -1, 0, (-11 / 4 : ℚ)], ![1, 1, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-25 / 9 : ℚ), 0, 0], ![0, 2, (-2 / 9 : ℚ), -2, (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, -4], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 11 : ℚ), 0, 0, 0, (-58 / 11 : ℚ)], ![-1, (-7 / 11 : ℚ), (-4 / 11 : ℚ), (7 / 11 : ℚ), (-56 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 12 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, (-17 / 6 : ℚ)], ![(-7 / 12 : ℚ), (7 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-5 / 11 : ℚ), (-7 / 11 : ℚ), (-1 / 11 : ℚ), (-36 / 11 : ℚ)], ![0, (5 / 11 : ℚ), 0, (-3 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-3 / 2 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-17 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-5 / 2 : ℚ), 0, 0], ![0, (7 / 6 : ℚ), (-4 / 3 : ℚ), (1 / 6 : ℚ), (-17 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, 0, (-1 / 4 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, -2, 0, 0], ![(1 / 4 : ℚ), 1, -1, (-11 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 17 : ℚ), 0, (-62 / 17 : ℚ), 0, 0], ![0, (21 / 17 : ℚ), (-33 / 17 : ℚ), (-64 / 17 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 3 : ℚ), 0, (-52 / 9 : ℚ), 0, 0], ![0, (22 / 9 : ℚ), (-26 / 9 : ℚ), (-68 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, -4, 0, 0], ![(1 / 8 : ℚ), 2, -2, (-19 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-8 / 9 : ℚ), (-56 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), (1 / 12 : ℚ), (-4 / 3 : ℚ), 1, (-31 / 12 : ℚ)], ![-1, 0, (-31 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, -2, (-8 / 5 : ℚ), 0], ![1, 1, -1, (-19 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, -2, (-9 / 8 : ℚ), 0], ![(1 / 8 : ℚ), 1, -1, (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-22 / 37 : ℚ), 0, (-35 / 74 : ℚ), (-95 / 74 : ℚ)], ![(-3 / 37 : ℚ), (-59 / 74 : ℚ), (-3 / 74 : ℚ), (-38 / 37 : ℚ), (-89 / 74 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-11 / 12 : ℚ), (-9 / 2 : ℚ), (-15 / 4 : ℚ), 0], ![(-3 / 8 : ℚ), (5 / 3 : ℚ), (-9 / 4 : ℚ), (-31 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, -4, (-5 / 2 : ℚ), 0], ![(1 / 4 : ℚ), 2, -2, (-11 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-21 / 17 : ℚ), 0, (-21 / 17 : ℚ), (-80 / 17 : ℚ)], ![(-4 / 17 : ℚ), (-25 / 17 : ℚ), (-2 / 17 : ℚ), (-46 / 17 : ℚ), (-78 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, -2, (-5 / 4 : ℚ), 0], ![1, 1, -1, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 6 : ℚ)], ![0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-29 / 21 : ℚ), (-30 / 7 : ℚ), (-61 / 21 : ℚ), 0], ![0, (29 / 21 : ℚ), (-15 / 7 : ℚ), (-64 / 21 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 5 : ℚ), 0, -4, (-12 / 5 : ℚ), 0], ![(1 / 5 : ℚ), 2, -2, (-14 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 1], ![0, (-3 / 2 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, 0], ![(-1 / 3 : ℚ), -2, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 8 : ℚ), (-11 / 8 : ℚ), 0, (-1 / 2 : ℚ), (1 / 2 : ℚ)], ![(1 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-6 / 5 : ℚ), 0, 0, 0], ![(-1 / 10 : ℚ), (-13 / 10 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 4 : ℚ), -1], ![0, 0, 0, (-9 / 4 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, (-5 / 2 : ℚ), 0, (1 / 4 : ℚ)], ![1, (5 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, (-27 / 10 : ℚ), 0, 0], ![0, 1, (-3 / 2 : ℚ), (3 / 10 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (-9 / 4 : ℚ), 0, (-7 / 4 : ℚ)], ![1, (9 / 8 : ℚ), (-9 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, -2, (-1 / 3 : ℚ), 0], ![1, 1, -1, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, -2, (-1 / 4 : ℚ), 0], ![(1 / 4 : ℚ), 1, -1, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), 0, -4, (-2 / 3 : ℚ), 0], ![(1 / 3 : ℚ), 2, -2, (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (-7 / 6 : ℚ), 1], ![0, 0, 0, (-1 / 6 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 1, -1], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, 1, -4], ![(-7 / 6 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -5], ![0, 0, 0, 1, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, -2, 0, -2], ![1, 1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-52 / 9 : ℚ)], ![0, 0, 0, 1, (-16 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, -2, 0, (-9 / 4 : ℚ)], ![(1 / 4 : ℚ), 1, -1, 0, (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, -2, 0, (-5 / 2 : ℚ)], ![(1 / 4 : ℚ), 1, -1, 0, (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, -5, 0, 0], ![0, 2, (-5 / 2 : ℚ), -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, -4, 0, 0], ![(1 / 2 : ℚ), 2, -2, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-11 / 2 : ℚ), 0, 0], ![0, 2, -3, -2, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (-1 / 10 : ℚ), (-21 / 5 : ℚ), (-6 / 5 : ℚ), 0], ![(2 / 5 : ℚ), 2, (-21 / 10 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 5 : ℚ), 0, -4, (-6 / 5 : ℚ), 0], ![(1 / 10 : ℚ), 2, -2, (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, 0, 0], ![(3 / 2 : ℚ), (5 / 4 : ℚ), (-13 / 4 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, 0, 0], ![(1 / 2 : ℚ), (5 / 4 : ℚ), (-13 / 4 : ℚ), (-7 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -6], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-3, 0, 0, 0, 0], ![(2 / 3 : ℚ), (7 / 3 : ℚ), (-20 / 3 : ℚ), (-11 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -6], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ)], ![0, (-11 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, (-5 / 3 : ℚ)], ![(4 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ), (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0], ![(5 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 7 : ℚ), 0, 0, (-11 / 7 : ℚ), 0], ![(4 / 7 : ℚ), (9 / 7 : ℚ), (-24 / 7 : ℚ), (-24 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 3 : ℚ)], ![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 5 : ℚ), 0, 0, (-16 / 5 : ℚ), 0], ![(4 / 5 : ℚ), (12 / 5 : ℚ), (-36 / 5 : ℚ), (-36 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-58 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ), (-18 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 6 : ℚ), 0, (4 / 3 : ℚ), (-11 / 3 : ℚ), -3], ![(-5 / 3 : ℚ), 0, 0, 0, -3]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), 0, -2, 0, 0], ![(-26 / 5 : ℚ), (-3 / 5 : ℚ), -4, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0], ![(5 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), 0, 0, (-7 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (6 / 5 : ℚ), -3, (-8 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0], ![0, (4 / 3 : ℚ), (-11 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-20 / 7 : ℚ), 0, 0, (-20 / 7 : ℚ), 0], ![(4 / 7 : ℚ), (16 / 7 : ℚ), (-44 / 7 : ℚ), (-24 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 3 : ℚ), 0, 0, (-10 / 3 : ℚ), 0], ![0, (22 / 9 : ℚ), (-68 / 9 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), (5 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), (4 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (4 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 1, 0, -4], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, -5, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (7 / 12 : ℚ), (25 / 12 : ℚ), (1 / 6 : ℚ), (-14 / 3 : ℚ)], ![(-9 / 4 : ℚ), (5 / 12 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), (13 / 6 : ℚ), (1 / 6 : ℚ), (-29 / 6 : ℚ)], ![(-7 / 3 : ℚ), (1 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, (-5 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(2 / 3 : ℚ), (4 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, -5], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (-11 / 6 : ℚ)], ![0, (7 / 6 : ℚ), (1 / 6 : ℚ), (-17 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, -5], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(5 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(2 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 3 : ℚ), 0, 0, 0, 0], ![(8 / 9 : ℚ), (22 / 9 : ℚ), (4 / 9 : ℚ), (-68 / 9 : ℚ), (8 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![0, 1, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, 0], ![0, 1, (-1 / 3 : ℚ), -4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, (-10 / 3 : ℚ)], ![0, (5 / 9 : ℚ), (-4 / 9 : ℚ), (-40 / 9 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 9 : ℚ), 0, (20 / 9 : ℚ), 0, (-70 / 9 : ℚ)], ![(-8 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, 0], ![0, (20 / 9 : ℚ), (-4 / 9 : ℚ), (-70 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(5 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(5 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (-11 / 6 : ℚ)], ![(4 / 3 : ℚ), (7 / 6 : ℚ), (-17 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (-11 / 6 : ℚ)], ![(4 / 3 : ℚ), (7 / 6 : ℚ), (-17 / 6 : ℚ), 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (-11 / 6 : ℚ)], ![(4 / 3 : ℚ), (7 / 6 : ℚ), (-17 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(2 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (-11 / 6 : ℚ)], ![(1 / 3 : ℚ), (7 / 6 : ℚ), (-17 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-7 / 6 : ℚ), (-25 / 6 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (-11 / 6 : ℚ)], ![(1 / 3 : ℚ), (7 / 6 : ℚ), (-17 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(-5 / 3 : ℚ), 1, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), -5], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (-11 / 6 : ℚ)], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (-17 / 6 : ℚ), (1 / 6 : ℚ), 2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, (-11 / 6 : ℚ)], ![0, (7 / 6 : ℚ), (-17 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![(1 / 2 : ℚ), 2, (-9 / 2 : ℚ), -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 2 : ℚ), (-43 / 10 : ℚ)], ![-1, (-1 / 10 : ℚ), (-73 / 20 : ℚ), (2 / 5 : ℚ), (-21 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 7 : ℚ), 0, 0, (-10 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (15 / 7 : ℚ), (-50 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0], ![0, (20 / 9 : ℚ), (-70 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 3 : ℚ), 0, 0, 0, 0], ![(8 / 9 : ℚ), (22 / 9 : ℚ), (-68 / 9 : ℚ), (8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-20 / 3 : ℚ), (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-25 / 6 : ℚ), (-13 / 6 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 3 : ℚ), 0, 0, 0, 0], ![(8 / 9 : ℚ), (22 / 9 : ℚ), (-68 / 9 : ℚ), (8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-3, 0, 0, 0, (-1 / 3 : ℚ)], ![0, (7 / 3 : ℚ), (-20 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-27 / 10 : ℚ), (-23 / 10 : ℚ)], ![-1, 0, (-1 / 10 : ℚ), (-13 / 10 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, 0, (-11 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (11 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 52 : ℚ), (-19 / 52 : ℚ), (-49 / 26 : ℚ), (-79 / 52 : ℚ), 0], ![(2 / 13 : ℚ), (14 / 13 : ℚ), (-50 / 13 : ℚ), (-83 / 52 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-1 / 5 : ℚ), (-8 / 5 : ℚ), (-7 / 5 : ℚ), 0], ![0, 1, (-17 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 13 : ℚ), 0, 0, (-64 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-6 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ), (-18 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 18 : ℚ), (-13 / 18 : ℚ), (-34 / 9 : ℚ), (-55 / 18 : ℚ), 0], ![(2 / 9 : ℚ), (19 / 9 : ℚ), (-70 / 9 : ℚ), (-59 / 18 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), (-1 / 2 : ℚ), (-13 / 4 : ℚ), (-11 / 4 : ℚ), 0], ![0, (7 / 4 : ℚ), -7, (-11 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-47 / 16 : ℚ), (-25 / 16 : ℚ), (-9 / 4 : ℚ), (-3 / 16 : ℚ), 0], ![(3 / 16 : ℚ), (-13 / 8 : ℚ), (-9 / 8 : ℚ), (-1 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (11 / 20 : ℚ), -4], ![(-1 / 10 : ℚ), 0, 0, (-11 / 20 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (15 / 62 : ℚ), (34 / 31 : ℚ), (-111 / 62 : ℚ)], ![0, (-16 / 31 : ℚ), (-9 / 31 : ℚ), (-34 / 31 : ℚ), (-27 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 13 : ℚ), 0, (1 / 13 : ℚ), (-22 / 13 : ℚ)], ![(-1 / 13 : ℚ), (-37 / 52 : ℚ), (-19 / 52 : ℚ), (-14 / 13 : ℚ), (-21 / 26 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 21 : ℚ), (2 / 21 : ℚ), (4 / 7 : ℚ), (2 / 21 : ℚ), (-74 / 21 : ℚ)], ![(-1 / 7 : ℚ), 0, (-11 / 21 : ℚ), 0, (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-3 / 16 : ℚ), 0, 0, (-3 / 16 : ℚ)], ![0, -1, 0, 0, (-1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), 0, (5 / 6 : ℚ), 0, (-10 / 3 : ℚ)], ![(-5 / 6 : ℚ), 0, (-1 / 6 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 21 : ℚ), (-1 / 21 : ℚ), (3 / 7 : ℚ), 0, (-68 / 21 : ℚ)], ![0, (-1 / 7 : ℚ), (-11 / 21 : ℚ), (-19 / 7 : ℚ), (-11 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 42 : ℚ), (1 / 21 : ℚ), (2 / 7 : ℚ), (1 / 21 : ℚ), (-79 / 21 : ℚ)], ![(-1 / 14 : ℚ), 0, (-16 / 21 : ℚ), (-73 / 21 : ℚ), (-13 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 2, (1 / 14 : ℚ), (-9 / 2 : ℚ)], ![-2, (3 / 7 : ℚ), (-1 / 14 : ℚ), 0, (-31 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-25 / 96 : ℚ), (-13 / 32 : ℚ), (-25 / 32 : ℚ), (-19 / 16 : ℚ)], ![0, (1 / 6 : ℚ), (-13 / 16 : ℚ), (-25 / 16 : ℚ), (19 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-9 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (6 / 5 : ℚ), 0, (-18 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 35 : ℚ), (-13 / 35 : ℚ), 0, (-41 / 35 : ℚ), (-13 / 35 : ℚ)], ![(-1 / 35 : ℚ), (12 / 35 : ℚ), 0, (-82 / 35 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, (-3 / 2 : ℚ), 0], ![0, 1, 0, -3, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 11 : ℚ), (-5 / 11 : ℚ), 0, (-21 / 11 : ℚ), (-32 / 11 : ℚ)], ![(16 / 11 : ℚ), (6 / 11 : ℚ), 0, (-42 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-19 / 8 : ℚ)], ![0, (7 / 8 : ℚ), 0, (-5 / 2 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 43 : ℚ), (-17 / 43 : ℚ), 0, (-55 / 43 : ℚ), (-114 / 43 : ℚ)], ![(-2 / 43 : ℚ), (15 / 43 : ℚ), 0, (-110 / 43 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-20 / 17 : ℚ), (-3 / 34 : ℚ), (-3 / 34 : ℚ), (-33 / 17 : ℚ), 0], ![(20 / 17 : ℚ), (20 / 17 : ℚ), (-11 / 34 : ℚ), (-135 / 34 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 44 : ℚ), (-15 / 44 : ℚ), (-1 / 11 : ℚ), (-41 / 22 : ℚ), 0], ![(2 / 11 : ℚ), (12 / 11 : ℚ), (-9 / 22 : ℚ), (-42 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 21 : ℚ), (-2 / 21 : ℚ), (-11 / 7 : ℚ), (-1 / 7 : ℚ)], ![(-2 / 21 : ℚ), (3 / 7 : ℚ), (-5 / 7 : ℚ), (-68 / 21 : ℚ), (-1 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-68 / 75 : ℚ), (-6 / 25 : ℚ), (-93 / 25 : ℚ), 0], ![(-8 / 25 : ℚ), (5 / 3 : ℚ), 0, (-192 / 25 : ℚ), (3 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 18 : ℚ), (-13 / 18 : ℚ), (-2 / 9 : ℚ), (-34 / 9 : ℚ), 0], ![(2 / 9 : ℚ), (19 / 9 : ℚ), (1 / 9 : ℚ), (-70 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 57 : ℚ), (-62 / 57 : ℚ), (-16 / 57 : ℚ), (-200 / 57 : ℚ), 0], ![(-2 / 57 : ℚ), (20 / 19 : ℚ), (-8 / 57 : ℚ), (-416 / 57 : ℚ), (8 / 57 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 7 : ℚ), 2, (1 / 14 : ℚ), -2], ![-2, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 12 : ℚ), (7 / 6 : ℚ), 0, (-23 / 20 : ℚ)], ![(-17 / 60 : ℚ), (-1 / 5 : ℚ), (-11 / 12 : ℚ), (-47 / 60 : ℚ), (-67 / 60 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 8 : ℚ), (-7 / 30 : ℚ), (-283 / 120 : ℚ), (-153 / 40 : ℚ), 0], ![(119 / 40 : ℚ), (77 / 24 : ℚ), (-16 / 15 : ℚ), (-39 / 5 : ℚ), (3 / 40 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 16 : ℚ), (11 / 8 : ℚ), 0, (-79 / 16 : ℚ)], ![(-17 / 16 : ℚ), (-9 / 16 : ℚ), (-1 / 2 : ℚ), (-15 / 16 : ℚ), (-63 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 17 : ℚ), (-9 / 17 : ℚ), (-23 / 17 : ℚ), (-20 / 17 : ℚ)], ![0, 0, (-21 / 17 : ℚ), (23 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (-17 / 12 : ℚ), 0, (1 / 6 : ℚ)], ![(7 / 6 : ℚ), (7 / 6 : ℚ), (-35 / 12 : ℚ), 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 17 : ℚ), (-3 / 17 : ℚ), (-32 / 17 : ℚ), 0, (-22 / 17 : ℚ)], ![(23 / 17 : ℚ), (23 / 17 : ℚ), (-67 / 17 : ℚ), 0, (55 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-383 / 204 : ℚ), (-13 / 51 : ℚ), (-539 / 204 : ℚ), (143 / 204 : ℚ), 0], ![(383 / 204 : ℚ), (139 / 68 : ℚ), (-274 / 51 : ℚ), (-143 / 204 : ℚ), (3 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 17 : ℚ), (-3 / 17 : ℚ), (-32 / 17 : ℚ), 0, (-19 / 17 : ℚ)], ![(23 / 17 : ℚ), (23 / 17 : ℚ), (-67 / 17 : ℚ), 0, (25 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 13 : ℚ), (-3 / 13 : ℚ), (-23 / 13 : ℚ), 0, (3 / 13 : ℚ)], ![(4 / 13 : ℚ), (15 / 13 : ℚ), (-48 / 13 : ℚ), (2 / 13 : ℚ), (5 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 44 : ℚ), (-15 / 44 : ℚ), (-41 / 22 : ℚ), 0, (-69 / 44 : ℚ)], ![(2 / 11 : ℚ), (12 / 11 : ℚ), (-42 / 11 : ℚ), (1 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-6 / 11 : ℚ), (-13 / 11 : ℚ), (-46 / 11 : ℚ)], ![0, 0, (-14 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-15 / 44 : ℚ), (-17 / 22 : ℚ), (-12 / 11 : ℚ), (-75 / 22 : ℚ)], ![0, 0, (-18 / 11 : ℚ), (1 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-19 / 36 : ℚ), (-59 / 36 : ℚ), 0, 0], ![(-1 / 18 : ℚ), (17 / 36 : ℚ), (-131 / 36 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-11 / 21 : ℚ), (-12 / 7 : ℚ), 0, (-17 / 7 : ℚ)], ![(1 / 21 : ℚ), (4 / 7 : ℚ), (-74 / 21 : ℚ), (2 / 21 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 12 : ℚ), (-2 / 3 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-11 / 21 : ℚ), (-12 / 7 : ℚ), 0, (-40 / 21 : ℚ)], ![(1 / 21 : ℚ), (4 / 7 : ℚ), (-74 / 21 : ℚ), (2 / 21 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), 0, -4], ![(-2 / 3 : ℚ), 0, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-5 / 2 : ℚ), 0, 0], ![(1 / 2 : ℚ), 2, (-11 / 2 : ℚ), -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 11 : ℚ), 0, -4], ![(-4 / 11 : ℚ), 0, (-12 / 11 : ℚ), 0, (-20 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 11 : ℚ), 0, (12 / 11 : ℚ), (-50 / 11 : ℚ)], ![(-85 / 44 : ℚ), (-3 / 11 : ℚ), (-29 / 44 : ℚ), (3 / 4 : ℚ), (-49 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 9 : ℚ), (-11 / 18 : ℚ), (-11 / 3 : ℚ), (-16 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (37 / 18 : ℚ), (-67 / 9 : ℚ), (-17 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 6 : ℚ), (-1 / 3 : ℚ), (-17 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![0, (11 / 6 : ℚ), (-20 / 3 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 18 : ℚ), (-13 / 18 : ℚ), (-34 / 9 : ℚ), 0, (2 / 27 : ℚ)], ![(2 / 9 : ℚ), (19 / 9 : ℚ), (-70 / 9 : ℚ), (2 / 9 : ℚ), (4 / 27 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 15 : ℚ), 0, (-28 / 5 : ℚ), (-16 / 3 : ℚ)], ![(-4 / 15 : ℚ), (-4 / 5 : ℚ), (-4 / 15 : ℚ), 0, (-52 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-48 / 11 : ℚ), (-26 / 11 : ℚ)], ![(-4 / 11 : ℚ), 0, (-28 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 18 : ℚ), (-13 / 18 : ℚ), (-34 / 9 : ℚ), 0, (1 / 3 : ℚ)], ![(2 / 9 : ℚ), (19 / 9 : ℚ), (-70 / 9 : ℚ), (2 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 87 : ℚ), (-92 / 87 : ℚ), (-10 / 3 : ℚ), 0, (-10 / 87 : ℚ)], ![(-2 / 87 : ℚ), (30 / 29 : ℚ), (-596 / 87 : ℚ), (8 / 87 : ℚ), (2 / 29 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (-1 / 5 : ℚ), 0, (1 / 5 : ℚ), (-9 / 5 : ℚ)], ![(-1 / 8 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ), (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 4 : ℚ), (-13 / 12 : ℚ)], ![(-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), (-7 / 24 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-32 / 23 : ℚ), (-64 / 23 : ℚ), (-122 / 23 : ℚ), (-14 / 23 : ℚ)], ![(-6 / 23 : ℚ), (26 / 23 : ℚ), (-70 / 23 : ℚ), (-125 / 23 : ℚ), (-4 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 3 : ℚ), (-40 / 9 : ℚ)], ![0, 0, (-4 / 3 : ℚ), (-14 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (3 / 8 : ℚ), (17 / 15 : ℚ), (-17 / 10 : ℚ)], ![0, (-1 / 4 : ℚ), (-53 / 120 : ℚ), (-17 / 15 : ℚ), (-17 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, (17 / 16 : ℚ), (1 / 16 : ℚ), (-61 / 16 : ℚ)], ![(-5 / 16 : ℚ), 0, (-13 / 16 : ℚ), 0, (-61 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 8 : ℚ), 0, 1, -1, (-17 / 8 : ℚ)], ![-1, 0, 0, 0, (-17 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 3 : ℚ), (5 / 3 : ℚ), (1 / 3 : ℚ), (-20 / 3 : ℚ)], ![-1, (1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 11 : ℚ), 0, (24 / 11 : ℚ), (4 / 11 : ℚ), (-82 / 11 : ℚ)], ![(-13 / 11 : ℚ), 0, (-15 / 11 : ℚ), 0, (-82 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), (-1 / 10 : ℚ), 0, (-23 / 10 : ℚ), (9 / 10 : ℚ)], ![(23 / 10 : ℚ), (21 / 10 : ℚ), (1 / 10 : ℚ), (-12 / 5 : ℚ), (-9 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-9 / 4 : ℚ), 1], ![2, (25 / 12 : ℚ), (1 / 12 : ℚ), (-7 / 3 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, (-19 / 8 : ℚ), 0], ![0, 1, (1 / 8 : ℚ), (-5 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-9 / 4 : ℚ), (-35 / 12 : ℚ)], ![(-19 / 6 : ℚ), (25 / 12 : ℚ), (1 / 12 : ℚ), (-7 / 3 : ℚ), (-17 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 9 : ℚ), (-2 / 9 : ℚ), (-8 / 3 : ℚ), 0, (-64 / 9 : ℚ)], ![(-10 / 3 : ℚ), (-4 / 9 : ℚ), (-46 / 9 : ℚ), (-2 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-19 / 10 : ℚ), 0], ![(6 / 5 : ℚ), (6 / 5 : ℚ), (-3 / 10 : ℚ), -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-19 / 24 : ℚ), (-1 / 24 : ℚ), (-19 / 12 : ℚ), (-7 / 24 : ℚ)], ![(-1 / 24 : ℚ), (3 / 4 : ℚ), (-1 / 2 : ℚ), (-13 / 8 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 23 : ℚ), (-32 / 23 : ℚ), (-6 / 23 : ℚ), (-71 / 23 : ℚ), 0], ![(1 / 23 : ℚ), (33 / 23 : ℚ), 0, (-77 / 23 : ℚ), (3 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 9 : ℚ), (-29 / 18 : ℚ), (-1 / 9 : ℚ), (-34 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (37 / 18 : ℚ), (1 / 18 : ℚ), (-35 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 2, (1 / 6 : ℚ), -2], ![-2, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-11 / 6 : ℚ), (-5 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 2 : ℚ), 0, (11 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 9 : ℚ), (-2 / 9 : ℚ), 0, (-17 / 9 : ℚ), (-13 / 9 : ℚ)], ![(-1 / 9 : ℚ), (-4 / 9 : ℚ), 0, (17 / 9 : ℚ), (-13 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (-7 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(6 / 5 : ℚ), (6 / 5 : ℚ), (-3 / 2 : ℚ), 0, (7 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), -2, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, 2, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 9 : ℚ), (-2 / 9 : ℚ), 0, (-17 / 9 : ℚ), (-14 / 3 : ℚ)], ![(-1 / 9 : ℚ), (-4 / 9 : ℚ), 0, (17 / 9 : ℚ), (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (-4 / 5 : ℚ), (-19 / 10 : ℚ), 0, 0], ![(1 / 10 : ℚ), (21 / 20 : ℚ), (-19 / 10 : ℚ), (1 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 12 : ℚ), (-2 / 3 : ℚ), (-13 / 12 : ℚ), (-7 / 2 : ℚ)], ![(-1 / 12 : ℚ), 0, (-3 / 4 : ℚ), (1 / 12 : ℚ), (-5 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-13 / 12 : ℚ), (-49 / 12 : ℚ)], ![(-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 20 : ℚ), (-3 / 5 : ℚ), (-43 / 20 : ℚ), (7 / 20 : ℚ), 0], ![(11 / 20 : ℚ), (29 / 20 : ℚ), (-43 / 20 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), (-7 / 5 : ℚ), 0, (-12 / 5 : ℚ)], ![0, (3 / 5 : ℚ), (-7 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-1 / 3 : ℚ), (-5 / 3 : ℚ), 0, (-7 / 3 : ℚ)], ![0, 1, (-5 / 3 : ℚ), 0, 2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 9 : ℚ), 0, -4], ![(-2 / 9 : ℚ), 0, (-4 / 9 : ℚ), 0, (-8 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-8 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), 2, (-10 / 3 : ℚ), -2, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, -3, 0, 0], ![0, 2, -3, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-31 / 23 : ℚ), (-62 / 23 : ℚ), (-39 / 23 : ℚ), (-7 / 46 : ℚ)], ![(-3 / 46 : ℚ), (59 / 46 : ℚ), (-127 / 46 : ℚ), (-81 / 46 : ℚ), (-1 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 9 : ℚ), (-4 / 9 : ℚ), (5 / 9 : ℚ), (-38 / 9 : ℚ)], ![(-10 / 9 : ℚ), 0, (-2 / 3 : ℚ), (1 / 3 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-19 / 13 : ℚ), (-21 / 13 : ℚ), (-54 / 13 : ℚ), (-35 / 13 : ℚ)], ![0, 0, (-23 / 13 : ℚ), (2 / 13 : ℚ), (-10 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-29 / 21 : ℚ), (-58 / 21 : ℚ), (-1 / 2 : ℚ), (-9 / 28 : ℚ)], ![(-3 / 14 : ℚ), (7 / 6 : ℚ), (-58 / 21 : ℚ), (-1 / 7 : ℚ), (-9 / 28 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-25 / 6 : ℚ), (-13 / 6 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 23 : ℚ), (-36 / 23 : ℚ), (-52 / 23 : ℚ), (-72 / 23 : ℚ), 0], ![(-1 / 23 : ℚ), (12 / 23 : ℚ), (-52 / 23 : ℚ), (4 / 23 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![0, -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, 0], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 4 : ℚ), 0, 1, -1, (-1 / 4 : ℚ)], ![-1, 0, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![0, -1, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (7 / 6 : ℚ), 2, (1 / 6 : ℚ), -2], ![-2, 1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (4 / 3 : ℚ), 2, (1 / 3 : ℚ), -2], ![-2, 1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (1 / 16 : ℚ), (23 / 16 : ℚ), (1 / 16 : ℚ), (-29 / 16 : ℚ)], ![(-5 / 16 : ℚ), (1 / 16 : ℚ), (-5 / 4 : ℚ), 0, (-29 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 7 : ℚ), 0, (29 / 14 : ℚ), (1 / 7 : ℚ), (-13 / 7 : ℚ)], ![(-11 / 7 : ℚ), 0, (-9 / 14 : ℚ), 0, (-13 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-5 / 2 : ℚ), 0, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![0, 1, (1 / 2 : ℚ), -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-31 / 23 : ℚ), (-5 / 46 : ℚ), (-39 / 23 : ℚ), (-7 / 46 : ℚ)], ![(-3 / 46 : ℚ), (59 / 46 : ℚ), (-7 / 46 : ℚ), (-81 / 46 : ℚ), (-1 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), (-17 / 24 : ℚ), 0, (-5 / 4 : ℚ), (-7 / 6 : ℚ)], ![0, (35 / 24 : ℚ), (1 / 12 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![(1 / 2 : ℚ), 2, (1 / 4 : ℚ), -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 92 : ℚ), (-31 / 23 : ℚ), (-3 / 46 : ℚ), (-163 / 92 : ℚ), 0], ![(1 / 92 : ℚ), (125 / 92 : ℚ), 0, (-169 / 92 : ℚ), (3 / 92 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 18 : ℚ), (-29 / 36 : ℚ), (-1 / 18 : ℚ), (-17 / 9 : ℚ), 0], ![(1 / 18 : ℚ), (73 / 36 : ℚ), (1 / 36 : ℚ), (-35 / 18 : ℚ), (1 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (-1 / 16 : ℚ), (-13 / 16 : ℚ), (-1 / 8 : ℚ), (-1 / 16 : ℚ)], ![0, (-1 / 4 : ℚ), 0, (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 6 : ℚ), -1, 0, 0], ![(1 / 12 : ℚ), (-2 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, 0], ![0, (-5 / 6 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![-1, 0, (-3 / 2 : ℚ), 1, -1], ![1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 24 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-23 / 8 : ℚ)], ![(-1 / 6 : ℚ), (3 / 8 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-19 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-11 / 20 : ℚ), 0, 0, (-33 / 10 : ℚ)], ![(-1 / 10 : ℚ), (9 / 20 : ℚ), 0, 0, (7 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (7 / 9 : ℚ), -4], ![(-14 / 9 : ℚ), 0, 0, (5 / 9 : ℚ), (-17 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, (-7 / 6 : ℚ), 0], ![(1 / 6 : ℚ), 2, -2, (-4 / 3 : ℚ), (1 / 6 : ℚ)]] }
]

theorem conicDetC19_checked : conicDetC19.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
