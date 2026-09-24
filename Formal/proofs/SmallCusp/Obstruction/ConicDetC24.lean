import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC24 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -4], ![0, (1 / 2 : ℚ), -2, (-1 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 0, (1 / 2 : ℚ), (-3 / 4 : ℚ), (-1 / 6 : ℚ)], ![(-2 / 3 : ℚ), 0, (-7 / 12 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 13 : ℚ), (-5 / 13 : ℚ), 0, 0, (-22 / 13 : ℚ)], ![(-14 / 13 : ℚ), (-37 / 52 : ℚ), (-19 / 52 : ℚ), (-193 / 52 : ℚ), (-21 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (-19 / 8 : ℚ)], ![(-5 / 8 : ℚ), 0, (-5 / 8 : ℚ), (-5 / 2 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 1, 0, (7 / 6 : ℚ), (1 / 6 : ℚ)], ![1, 1, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 10 : ℚ), 0, 0, -1], ![0, (1 / 10 : ℚ), -2, (-1 / 5 : ℚ), (6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 4 : ℚ), 0, 0, -1], ![0, (1 / 2 : ℚ), -2, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -1], ![0, (1 / 2 : ℚ), -2, 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (17 / 18 : ℚ), 0, 0, -4], ![0, (8 / 9 : ℚ), -2, (-1 / 18 : ℚ), (-11 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), 0, 0, -4], ![0, (1 / 3 : ℚ), -2, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -4], ![0, (1 / 2 : ℚ), -2, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 3 : ℚ), (5 / 3 : ℚ), 0, -1], ![(1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 13 : ℚ), (-5 / 13 : ℚ), 0, (-5 / 13 : ℚ), (-22 / 13 : ℚ)], ![(-14 / 13 : ℚ), (-37 / 52 : ℚ), (-19 / 52 : ℚ), (-89 / 52 : ℚ), (-21 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (1 / 6 : ℚ), (4 / 3 : ℚ), 0, -4], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 4 : ℚ), 0], ![-1, -1, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 4 : ℚ), 0], ![-1, -1, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-3 / 8 : ℚ)], ![(-7 / 8 : ℚ), (-7 / 8 : ℚ), (-1 / 4 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 4 : ℚ), (-1 / 8 : ℚ)], ![-1, -1, 0, (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (-1 / 2 : ℚ)], ![0, 0, -2, (1 / 4 : ℚ), (13 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 2 : ℚ), (-1 / 4 : ℚ)], ![-1, -1, 0, (1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 1, 0], ![-1, -1, 0, 1, 1]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 1, 0], ![-1, -1, 0, 1, 2]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 4 : ℚ), (-1 / 4 : ℚ)], ![-1, -1, 0, (1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 3 : ℚ), 0], ![-1, -1, 0, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 3 : ℚ), 0], ![-1, -1, 0, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 6 : ℚ), (-1 / 6 : ℚ)], ![-1, -1, 0, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 5 : ℚ), (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (3 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-19 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 4 : ℚ), (-7 / 8 : ℚ), (1 / 8 : ℚ), (-15 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 10 : ℚ), (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (-21 / 20 : ℚ), (1 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 10 : ℚ), 0, (2 / 5 : ℚ), (-1 / 10 : ℚ)], ![(-6 / 5 : ℚ), (-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-19 / 8 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 8 : ℚ), (1 / 8 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, -1, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, -1, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-11 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 2 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (-21 / 20 : ℚ), 0, (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), 0, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0, -3]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 9 : ℚ), (-20 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-1 / 9 : ℚ), (-10 / 9 : ℚ), 0, (-5 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 6 : ℚ), (-7 / 3 : ℚ)], ![(-5 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, -2], ![-1, (-1 / 2 : ℚ), -1, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 24 : ℚ), (-5 / 24 : ℚ), 0, (11 / 8 : ℚ), (-31 / 24 : ℚ)], ![(-25 / 24 : ℚ), (-3 / 4 : ℚ), (-7 / 24 : ℚ), (-4 / 3 : ℚ), (-5 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 17 : ℚ), -1, 0, (29 / 17 : ℚ), (-12 / 17 : ℚ)], ![(-21 / 17 : ℚ), -1, (-4 / 17 : ℚ), (-25 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (1 / 5 : ℚ), (6 / 5 : ℚ), 0, -3], ![0, 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, (4 / 3 : ℚ), 0, -3], ![0, 0, 0, 0, -3]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(9 / 16 : ℚ), (-15 / 16 : ℚ), 0, (15 / 16 : ℚ), (-5 / 4 : ℚ)], ![(-17 / 16 : ℚ), (-15 / 16 : ℚ), (-1 / 16 : ℚ), (15 / 16 : ℚ), (-3 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 1, 0, -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (-23 / 20 : ℚ), (-3 / 20 : ℚ), (9 / 20 : ℚ), 0], ![(-5 / 4 : ℚ), (-23 / 20 : ℚ), (-1 / 10 : ℚ), (9 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 13 : ℚ), (-5 / 13 : ℚ), 0, (1 / 13 : ℚ), (-22 / 13 : ℚ)], ![(-14 / 13 : ℚ), (-37 / 52 : ℚ), (-19 / 52 : ℚ), (-14 / 13 : ℚ), (-21 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, (1 / 2 : ℚ), (1 / 8 : ℚ), (-19 / 8 : ℚ)], ![(-5 / 8 : ℚ), 0, (-5 / 8 : ℚ), (-5 / 8 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-22 / 15 : ℚ)], ![(-16 / 15 : ℚ), (-3 / 4 : ℚ), (-19 / 60 : ℚ), (-3 / 4 : ℚ), (-7 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), 0, -2], ![(-5 / 6 : ℚ), (-1 / 6 : ℚ), (-2 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 2 : ℚ), 0], ![0, 0, -1, (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 8 : ℚ), (-1 / 8 : ℚ)], ![0, 0, -1, (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (2 / 3 : ℚ), -1], ![0, 0, -1, (-2 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 6 : ℚ), (1 / 6 : ℚ)], ![0, 0, -1, (-1 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 2 : ℚ), 1], ![0, 0, -1, (-3 / 2 : ℚ), 1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (2 / 3 : ℚ), -4], ![0, 0, -1, (-2 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (2 / 3 : ℚ), (-8 / 3 : ℚ)], ![0, 0, -1, (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (2 / 3 : ℚ), -4], ![0, 0, -1, (-2 / 3 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 2 : ℚ), 0], ![0, 0, -2, (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 4 : ℚ), (-1 / 8 : ℚ)], ![0, 0, -2, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 2 : ℚ), -1], ![0, 0, -2, (-1 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 4 : ℚ), (1 / 4 : ℚ)], ![0, 0, -2, (-1 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 2 : ℚ), -4], ![0, 0, -2, (-1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 2 : ℚ), (-9 / 4 : ℚ)], ![0, 0, -2, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 2 : ℚ), -4], ![0, 0, -2, (-1 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-7 / 6 : ℚ), (-1 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 14 : ℚ), 0, (1 / 7 : ℚ), (3 / 14 : ℚ)], ![(-17 / 14 : ℚ), 0, (-1 / 7 : ℚ), (-29 / 7 : ℚ), (3 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 8 : ℚ), 0, (1 / 8 : ℚ), (-7 / 4 : ℚ)], ![(-9 / 8 : ℚ), 0, (-1 / 8 : ℚ), (-33 / 8 : ℚ), (-7 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 10 : ℚ), 0, (1 / 10 : ℚ), (-9 / 5 : ℚ)], ![(-11 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-41 / 10 : ℚ), (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), 0, -4], ![0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), 0, -4], ![0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (1 / 2 : ℚ), (3 / 2 : ℚ), 0], ![-2, 0, (-9 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (2 / 3 : ℚ), (5 / 3 : ℚ), 0], ![-2, 0, (-14 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 3 : ℚ), -1, -4], ![0, 0, (-2 / 3 : ℚ), -1, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), -4], ![0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), -4], ![0, 0, (-2 / 5 : ℚ), (3 / 5 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), (5 / 4 : ℚ), -4], ![0, 0, (-1 / 4 : ℚ), (3 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 2, 0, -2], ![-1, 0, (-5 / 2 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 6 : ℚ), 0], ![0, 0, -1, (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (-1 / 3 : ℚ), (1 / 6 : ℚ)], ![-1, 0, 0, (-13 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 6 : ℚ), -1], ![0, 0, -1, (-1 / 6 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 6 : ℚ), (1 / 6 : ℚ)], ![0, 0, -1, (-1 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (-1 / 4 : ℚ), 0], ![-1, 0, 0, (-9 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (-1 / 3 : ℚ), -2], ![-1, 0, 0, (-13 / 6 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![-1, 0, 0, (-13 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 6 : ℚ), -4], ![0, 0, -1, (-1 / 6 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![0, 0, -2, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, (1 / 6 : ℚ)], ![-1, 0, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -1], ![0, 0, -2, 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (1 / 4 : ℚ)], ![0, 0, -2, 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 1, 0, 1, (1 / 8 : ℚ)], ![1, 0, 0, 2, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![0, 0, -2, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, (-1 / 4 : ℚ)], ![-1, 0, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![0, 0, -2, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 16 : ℚ), 0, 0, -1], ![0, (-1 / 16 : ℚ), -2, (-1 / 16 : ℚ), (17 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 0, -1], ![0, 0, -2, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, -2, (-1 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, -2, -1, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 0, -4], ![0, 0, -2, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, -2, (-1 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (11 / 6 : ℚ), (1 / 12 : ℚ), -1], ![0, 0, (-1 / 12 : ℚ), (-1 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (13 / 8 : ℚ), (1 / 8 : ℚ), -4], ![0, 0, (-1 / 8 : ℚ), (-3 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (7 / 5 : ℚ), (2 / 5 : ℚ), -4], ![0, 0, (-2 / 5 : ℚ), (-6 / 5 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (11 / 5 : ℚ), 0], ![-2, 0, (-23 / 5 : ℚ), (-8 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-3 / 14 : ℚ), (9 / 7 : ℚ), 0], ![-2, 0, (-29 / 7 : ℚ), (-8 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (5 / 4 : ℚ), 0], ![-2, 0, (-17 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 2 : ℚ), (4 / 3 : ℚ), 0], ![-2, 0, (-13 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 3 : ℚ), 0, -2], ![-1, 0, (-13 / 6 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), -4], ![0, 0, (-1 / 4 : ℚ), (1 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), -4], ![0, 0, (-2 / 5 : ℚ), (3 / 5 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (-3 / 8 : ℚ), 0], ![-2, 0, (-33 / 8 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 2 : ℚ), -1, 0], ![-2, 0, (-13 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 2, 0, 1], ![0, 0, 0, 0, 1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 2, 0, 4], ![0, 0, 0, 0, 4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![0, 0, -1, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, (1 / 4 : ℚ)], ![-1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (1 / 3 : ℚ)], ![0, 0, -1, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![0, 0, -1, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, (-1 / 2 : ℚ)], ![-1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (7 / 8 : ℚ), (1 / 8 : ℚ), 1, 0], ![(7 / 8 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 8 : ℚ), 0, 0, -1], ![0, (-1 / 8 : ℚ), -2, (-1 / 8 : ℚ), (9 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 0, -1], ![0, 0, -2, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, -2, 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, -2, (-2 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 0, -4], ![0, 0, -2, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, -2, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), 0, -1], ![0, 0, (-1 / 2 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (13 / 8 : ℚ), (1 / 8 : ℚ), -4], ![0, 0, (-1 / 8 : ℚ), (-3 / 8 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), 0, -4], ![0, 0, (-1 / 2 : ℚ), 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, (-5 / 6 : ℚ), (1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, -2, (15 / 7 : ℚ), 0], ![-2, 0, -2, (-11 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-3 / 8 : ℚ), (9 / 8 : ℚ), 0], ![-2, 0, (-17 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, -2, (5 / 3 : ℚ), 0], ![-2, 0, -2, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), -4], ![0, 0, (-1 / 4 : ℚ), (1 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (2 / 5 : ℚ), -4], ![0, 0, 0, (3 / 5 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-3 / 8 : ℚ), (-3 / 8 : ℚ), 0], ![-2, 0, (-17 / 8 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, (5 / 4 : ℚ), 1, 4], ![0, 0, 0, 1, 2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, (3 / 2 : ℚ), 1, (9 / 2 : ℚ)], ![0, 0, 0, 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, (5 / 4 : ℚ), 1, 4], ![0, 0, 0, 1, 4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 1, 1, 0, 2], ![1, 0, 0, 0, 2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![0, 0, -1, (1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 2 : ℚ), (-1 / 4 : ℚ)], ![-1, 0, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![0, 0, -1, (1 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 2 : ℚ), -2], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 4 : ℚ), (-1 / 4 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 4 : ℚ), -2], ![-1, 0, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 6 : ℚ), -4], ![0, 0, -1, (1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 6 : ℚ), (-13 / 6 : ℚ)], ![0, 0, -1, (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 3 : ℚ), -4], ![0, 0, -1, (2 / 3 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 1, -4], ![0, 0, -1, 1, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-1 / 2 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![0, 0, -2, (1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 2 : ℚ), (-1 / 8 : ℚ)], ![-1, 0, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![0, 0, -2, (1 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 4 : ℚ), -2], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 3 : ℚ), (-1 / 6 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (2 / 3 : ℚ), -2], ![-1, 0, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, -1, -4], ![0, 0, -2, -1, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 8 : ℚ), -4], ![0, 0, -2, (3 / 8 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 8 : ℚ), (-33 / 16 : ℚ)], ![0, 0, -2, (3 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 4 : ℚ), -4], ![0, 0, -2, (3 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), -4], ![0, 0, (-9 / 8 : ℚ), (3 / 8 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-19 / 8 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 8 : ℚ), (3 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), -4], ![0, 0, (-9 / 8 : ℚ), (3 / 8 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), -4], ![0, 0, (-7 / 6 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 8 : ℚ), 0, (3 / 8 : ℚ), (-1 / 8 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), -4], ![0, 0, (-7 / 6 : ℚ), 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, 0, (-5 / 4 : ℚ), -1, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-5 / 3 : ℚ), (1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-5 / 3 : ℚ), (1 / 3 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -4], ![0, 0, -2, (2 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, -2], ![-1, 0, -1, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, -2], ![-1, 0, -1, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (21 / 17 : ℚ), (1 / 34 : ℚ), -4], ![0, 0, (-3 / 34 : ℚ), (1 / 17 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (79 / 68 : ℚ), (1 / 68 : ℚ), -4], ![0, 0, (-1 / 17 : ℚ), (3 / 68 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-1 / 4 : ℚ), -4], ![0, 0, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 3 : ℚ), (-1 / 3 : ℚ), -4], ![0, 0, 0, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), -1, -4], ![0, 0, (-1 / 3 : ℚ), -1, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (-8 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, (-1 / 10 : ℚ), (-11 / 10 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-37 / 32 : ℚ), 0, (1 / 16 : ℚ), (-27 / 16 : ℚ)], ![(-37 / 32 : ℚ), 0, (-1 / 16 : ℚ), (-17 / 16 : ℚ), (-27 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (25 / 16 : ℚ), (17 / 16 : ℚ), -4], ![0, 0, (-1 / 16 : ℚ), (9 / 16 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 2 : ℚ), -1, 0], ![-2, 0, (-1 / 2 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), 0], ![(-3 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 12 : ℚ), (1 / 4 : ℚ)], ![-1, -1, 0, -2, (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 2 : ℚ), 0], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 8 : ℚ), (1 / 8 : ℚ)], ![0, 0, -1, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 2 : ℚ), 0], ![-1, -1, 0, (-7 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (2 / 3 : ℚ), (-4 / 3 : ℚ)], ![-1, -1, 0, -2, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 2, 0], ![-1, -1, 0, (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 2 : ℚ), -2], ![-1, -1, 0, -2, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 6 : ℚ), (1 / 6 : ℚ)], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (5 / 4 : ℚ), (1 / 4 : ℚ)], ![-1, -1, 0, (-17 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (2 / 3 : ℚ), 0], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 6 : ℚ), (1 / 6 : ℚ)], ![0, 0, -2, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (2 / 3 : ℚ), (-4 / 9 : ℚ)], ![-1, -1, 0, -2, (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (7 / 6 : ℚ), 0], ![-1, -1, 0, (-3 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (2 / 3 : ℚ), -2], ![-1, -1, 0, -2, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-5 / 4 : ℚ), (-1 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (3 / 14 : ℚ), (1 / 7 : ℚ), 0], ![-1, -1, (-1 / 7 : ℚ), (-26 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), 0, (2 / 5 : ℚ), (1 / 10 : ℚ), (-12 / 5 : ℚ)], ![(-7 / 10 : ℚ), 0, (-7 / 20 : ℚ), (-33 / 10 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (-3 / 5 : ℚ), (2 / 5 : ℚ), 0], ![-2, -2, (-2 / 5 : ℚ), (-28 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (1 / 4 : ℚ), (5 / 4 : ℚ), 0], ![-2, -2, -4, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 3 : ℚ), 0, -4], ![0, 0, 0, (1 / 3 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (1 / 2 : ℚ), 0, -2], ![-1, -1, -2, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 6 : ℚ), (1 / 6 : ℚ), -4], ![0, 0, 0, (1 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (1 / 2 : ℚ), -1, 0], ![-2, -2, -6, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (1 / 6 : ℚ)], ![-1, -1, 0, (-19 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (1 / 2 : ℚ)], ![-1, -1, 0, (-19 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![-1, -1, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (1 / 6 : ℚ)], ![-1, -1, 0, (-19 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-2 / 3 : ℚ)], ![-1, -1, 0, (-5 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (5 / 8 : ℚ), 0], ![-1, -1, 0, (-5 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, -2], ![-1, -1, 0, (-5 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, (1 / 4 : ℚ)], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, (1 / 4 : ℚ)], ![-1, -1, 0, -2, (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, 0], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, (1 / 3 : ℚ)], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 2, 0, 1, (1 / 3 : ℚ)], ![1, 1, 0, 2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, (-1 / 3 : ℚ)], ![-1, -1, 0, -2, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, 0], ![-1, -1, 0, -2, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, -2], ![-1, -1, 0, -2, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 5 : ℚ), 0, 0, -1], ![0, (2 / 5 : ℚ), -2, (-3 / 5 : ℚ), (8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 16 : ℚ), 0, 0, -1], ![0, (3 / 16 : ℚ), -2, (-1 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, -2, (-1 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -4], ![0, (1 / 4 : ℚ), -2, (-1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 5 : ℚ), 0, 0, -4], ![0, (3 / 5 : ℚ), -2, (-2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, -2, (-1 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 3 : ℚ), 0, (-5 / 4 : ℚ), (1 / 3 : ℚ)], ![(-4 / 3 : ℚ), (-4 / 3 : ℚ), (-7 / 12 : ℚ), (-7 / 2 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 20 : ℚ), (-2 / 5 : ℚ), 0, 0, (-9 / 5 : ℚ)], ![(-21 / 20 : ℚ), (-1 / 5 : ℚ), (-17 / 40 : ℚ), (-29 / 8 : ℚ), (-9 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-12 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-6 / 5 : ℚ), (-6 / 5 : ℚ), (-7 / 10 : ℚ), (-7 / 2 : ℚ), (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, 0, (5 / 4 : ℚ), 0], ![-2, -2, (-25 / 8 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (6 / 5 : ℚ), (11 / 5 : ℚ), 0], ![-2, -2, (-13 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, -2], ![-1, -1, (-5 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, 0, (2 / 3 : ℚ), 0], ![-2, -2, (-10 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, -2], ![-1, -1, (-8 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 5, 0, (5 / 2 : ℚ), (-3 / 2 : ℚ)], ![(5 / 2 : ℚ), (5 / 2 : ℚ), (1 / 2 : ℚ), (5 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 5, 0, (5 / 2 : ℚ), -1], ![(5 / 2 : ℚ), (5 / 2 : ℚ), (1 / 2 : ℚ), (5 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, (1 / 2 : ℚ)], ![-1, -1, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, (1 / 2 : ℚ)], ![-1, -1, 0, -1, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, (1 / 2 : ℚ)], ![-1, -1, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-10 / 3 : ℚ), (2 / 3 : ℚ), (-5 / 3 : ℚ), 0], ![(-5 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, -1, 0], ![-1, -1, 0, -1, (2 / 3 : ℚ)]] }
]

theorem conicDetC24_checked : conicDetC24.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
