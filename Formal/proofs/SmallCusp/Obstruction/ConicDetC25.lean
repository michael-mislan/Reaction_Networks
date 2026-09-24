import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC25 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 2, 0, (13 / 12 : ℚ), (1 / 12 : ℚ)], ![1, 1, 0, (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 5 : ℚ), 0, 0, -1], ![0, (2 / 5 : ℚ), -2, (-3 / 5 : ℚ), (8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 4 : ℚ), 0, 0, -1], ![0, (3 / 4 : ℚ), -2, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, -2, 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, 0, -4], ![0, (1 / 6 : ℚ), -2, (-1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 5 : ℚ), 0, 0, -4], ![0, (3 / 5 : ℚ), -2, (-2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, -2, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), 0, -1], ![0, 0, (-1 / 2 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), 0, (2 / 5 : ℚ), 0, (-12 / 5 : ℚ)], ![(-7 / 10 : ℚ), 0, (-7 / 20 : ℚ), (-27 / 20 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -3, 0, (-3 / 2 : ℚ), -1], ![(-3 / 2 : ℚ), (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-3 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, -2, (5 / 4 : ℚ), 0], ![-2, -2, -2, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, -2, (11 / 5 : ℚ), 0], ![-2, -2, -2, (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, -2, (2 / 3 : ℚ), 0], ![-2, -2, -2, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (5 / 2 : ℚ), 0, (-1 / 4 : ℚ), (19 / 12 : ℚ)], ![(5 / 4 : ℚ), (5 / 4 : ℚ), (1 / 12 : ℚ), (-1 / 4 : ℚ), (19 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, (3 / 2 : ℚ), 1, (9 / 2 : ℚ)], ![0, 0, (1 / 6 : ℚ), 1, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (5 / 2 : ℚ), 0, (-1 / 4 : ℚ), (3 / 2 : ℚ)], ![(5 / 4 : ℚ), (5 / 4 : ℚ), (1 / 12 : ℚ), (-1 / 4 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (9 / 2 : ℚ), 0, (5 / 4 : ℚ), (-1 / 2 : ℚ)], ![(9 / 4 : ℚ), (9 / 4 : ℚ), (1 / 4 : ℚ), (5 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (2 / 3 : ℚ), (-4 / 3 : ℚ)], ![-1, -1, 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (2 / 3 : ℚ), 0], ![-1, -1, 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 4 : ℚ), -2], ![-1, -1, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 2 : ℚ), (-1 / 3 : ℚ)], ![-1, -1, 0, (1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (-1 / 2 : ℚ)], ![0, 0, -1, (1 / 6 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 2 : ℚ), -2], ![-1, -1, 0, (1 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 4 : ℚ), (-1 / 2 : ℚ)], ![-1, -1, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 2 : ℚ), 0], ![-1, -1, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 2 : ℚ), -2], ![-1, -1, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-10 / 3 : ℚ), (2 / 3 : ℚ), (-2 / 3 : ℚ), 0], ![(-5 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![-1, -1, 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-2 / 3 : ℚ)], ![(-3 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (2 / 3 : ℚ), 0], ![-1, -1, 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 4 : ℚ), -2], ![-1, -1, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 4 : ℚ), (-1 / 18 : ℚ)], ![-1, -1, 0, (1 / 12 : ℚ), (-1 / 36 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![0, 0, -2, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 2 : ℚ), -2], ![-1, -1, 0, (1 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, -2], ![-1, -1, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 3 : ℚ), (-2 / 9 : ℚ)], ![-1, -1, 0, 0, (-1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 3 : ℚ), 0], ![-1, -1, 0, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (1 / 3 : ℚ), -2], ![-1, -1, 0, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 8 : ℚ), (-13 / 6 : ℚ)], ![(-1 / 24 : ℚ), 0, (-25 / 24 : ℚ), (5 / 24 : ℚ), (-13 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-7 / 3 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-13 / 12 : ℚ), (5 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 10 : ℚ), -4], ![0, 0, (-11 / 10 : ℚ), (1 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), (-22 / 9 : ℚ)], ![(-1 / 9 : ℚ), 0, (-10 / 9 : ℚ), (2 / 9 : ℚ), (-11 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-21 / 10 : ℚ), 0, (2 / 5 : ℚ), (-1 / 10 : ℚ)], ![(-11 / 10 : ℚ), (-11 / 10 : ℚ), 0, (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 6 : ℚ), -4], ![0, 0, (-19 / 18 : ℚ), (1 / 9 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, 0, (-4 / 3 : ℚ), -1, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-5 / 4 : ℚ), (1 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, -2], ![-1, (-1 / 6 : ℚ), -1, (-1 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 5 : ℚ), (-12 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, -2], ![-1, -1, -1, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 17 : ℚ), 0, (14 / 17 : ℚ), (12 / 17 : ℚ), (-46 / 17 : ℚ)], ![(-6 / 17 : ℚ), 0, (-3 / 17 : ℚ), (-9 / 17 : ℚ), (-23 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-45 / 17 : ℚ), 0, (23 / 17 : ℚ), (-23 / 17 : ℚ)], ![(-45 / 34 : ℚ), (-45 / 34 : ℚ), (-2 / 17 : ℚ), (-21 / 17 : ℚ), (-23 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, (4 / 3 : ℚ), 0, (-10 / 3 : ℚ)], ![0, 0, 0, 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 3 : ℚ), (-1 / 3 : ℚ), -4], ![0, 0, 0, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), -1, -4], ![0, 0, (-1 / 3 : ℚ), -1, -4]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), 0, (2 / 5 : ℚ), (1 / 10 : ℚ), (-12 / 5 : ℚ)], ![(-7 / 10 : ℚ), 0, (-7 / 20 : ℚ), (-7 / 10 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (-3 / 16 : ℚ), (1 / 8 : ℚ), 0], ![-2, -2, (-1 / 8 : ℚ), (-21 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (-11 / 13 : ℚ), 0, (-4 / 13 : ℚ), (-19 / 13 : ℚ)], ![(-14 / 13 : ℚ), (-11 / 26 : ℚ), (-17 / 52 : ℚ), (-3 / 4 : ℚ), (-19 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), 1, -4], ![0, 0, (-1 / 2 : ℚ), 1, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 8 : ℚ), 0, (1 / 8 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ)], ![(11 / 8 : ℚ), (1 / 8 : ℚ), (35 / 8 : ℚ), (19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 4 : ℚ)], ![(-13 / 12 : ℚ), (-1 / 12 : ℚ), (-49 / 12 : ℚ), (-25 / 12 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 11 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ), (-14 / 11 : ℚ)], ![(-13 / 11 : ℚ), (-2 / 11 : ℚ), (-46 / 11 : ℚ), (-24 / 11 : ℚ), (-6 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 17 : ℚ), 0, (4 / 17 : ℚ), (4 / 17 : ℚ), (-14 / 17 : ℚ)], ![(-21 / 17 : ℚ), (-4 / 17 : ℚ), (-72 / 17 : ℚ), (-38 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 10 : ℚ), (3 / 10 : ℚ), (2 / 5 : ℚ), (9 / 5 : ℚ), 0], ![1, (3 / 5 : ℚ), (43 / 10 : ℚ), (18 / 5 : ℚ), (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, -1, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 18 : ℚ), 0, (1 / 18 : ℚ), (-23 / 18 : ℚ), (1 / 3 : ℚ)], ![(-11 / 9 : ℚ), (-5 / 9 : ℚ), (-73 / 18 : ℚ), (-7 / 2 : ℚ), (7 / 18 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), 0, (1 / 11 : ℚ), 0, (-18 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-15 / 44 : ℚ), (-45 / 11 : ℚ), (-15 / 4 : ℚ), (-17 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 17 : ℚ), 0, (2 / 17 : ℚ), (-5 / 17 : ℚ), (-24 / 17 : ℚ)], ![(-19 / 17 : ℚ), (-21 / 34 : ℚ), (-70 / 17 : ℚ), (-7 / 2 : ℚ), (-23 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 10 : ℚ), (3 / 10 : ℚ), 0, (17 / 10 : ℚ), 0], ![1, (3 / 5 : ℚ), (17 / 5 : ℚ), (17 / 10 : ℚ), (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-1 / 2 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-1 / 2 : ℚ), 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-4 / 3 : ℚ), (1 / 3 : ℚ)], ![(-7 / 6 : ℚ), (-2 / 3 : ℚ), (-13 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), 0, (1 / 11 : ℚ), (-5 / 11 : ℚ), (-18 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-15 / 44 : ℚ), (-45 / 11 : ℚ), (-7 / 4 : ℚ), (-17 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 0, (1 / 12 : ℚ), (-7 / 6 : ℚ), (-5 / 3 : ℚ)], ![(-13 / 12 : ℚ), (-5 / 6 : ℚ), (-49 / 12 : ℚ), (-7 / 6 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ)], ![(8 / 5 : ℚ), 0, (1 / 5 : ℚ), (23 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, (1 / 2 : ℚ)], ![(5 / 4 : ℚ), 0, (1 / 4 : ℚ), (17 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 1], ![-1, 0, 0, -4, -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (1 / 2 : ℚ)], ![-1, 0, 0, -4, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (1 / 3 : ℚ)], ![-1, 0, 0, -4, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, (1 / 2 : ℚ)], ![1, 0, 0, 4, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![-1, 0, 0, -4, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![-1, 0, 0, -4, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![-1, 0, 0, -4, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (1 / 5 : ℚ), 0, 0, 0], ![(9 / 10 : ℚ), (1 / 2 : ℚ), (3 / 10 : ℚ), (39 / 10 : ℚ), (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 1], ![-1, 0, 0, -4, -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (2 / 3 : ℚ)], ![-1, 0, 0, -4, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (1 / 6 : ℚ)], ![-1, 0, 0, -4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, (1 / 6 : ℚ)], ![1, 0, 0, 4, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![-1, 0, 0, -4, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![-1, 0, 0, -4, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![-1, 0, 0, -4, (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), -1, 1], ![2, 0, 6, 1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), -1, 1], ![(17 / 8 : ℚ), 0, (49 / 8 : ℚ), 0, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)], ![(3 / 2 : ℚ), (2 / 3 : ℚ), (29 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), 0, 1], ![(3 / 2 : ℚ), 0, (9 / 2 : ℚ), 1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 1], ![(-3 / 2 : ℚ), 0, 0, (-9 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (1 / 4 : ℚ)], ![(-9 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-33 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (2 / 5 : ℚ)], ![(-6 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-21 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 10 : ℚ)], ![(-11 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-41 / 10 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-4 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-13 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 13 : ℚ)], ![(-17 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-56 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, (-29 / 7 : ℚ), (-1 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, (-9 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, -1, -5, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), 1, 1], ![(-7 / 6 : ℚ), 0, (-25 / 6 : ℚ), -1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 0, (1 / 12 : ℚ), (5 / 4 : ℚ), (-7 / 12 : ℚ)], ![(-13 / 12 : ℚ), (-1 / 12 : ℚ), (-49 / 12 : ℚ), (-7 / 6 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 35 : ℚ), 0, (8 / 35 : ℚ), (59 / 35 : ℚ), (-4 / 5 : ℚ)], ![(-43 / 35 : ℚ), (-8 / 35 : ℚ), (-148 / 35 : ℚ), (-51 / 35 : ℚ), (-24 / 35 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), 0, (1 / 10 : ℚ), (1 / 5 : ℚ), (3 / 10 : ℚ)], ![(-11 / 10 : ℚ), 0, (-41 / 10 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (15 / 7 : ℚ), (2 / 7 : ℚ), (-5 / 7 : ℚ), (-36 / 7 : ℚ)], ![(6 / 7 : ℚ), 0, 0, 0, (-17 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), 0, (4 / 13 : ℚ), (8 / 13 : ℚ), (-6 / 13 : ℚ)], ![(-17 / 13 : ℚ), 0, (-56 / 13 : ℚ), 0, (-4 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), 0, 1], ![(-7 / 6 : ℚ), 0, (-25 / 6 : ℚ), -1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ)], ![(-7 / 6 : ℚ), (-2 / 3 : ℚ), (-9 / 2 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 15 : ℚ), 0, (2 / 15 : ℚ), (2 / 5 : ℚ), (-22 / 15 : ℚ)], ![(-17 / 15 : ℚ), (-2 / 15 : ℚ), (-62 / 15 : ℚ), (11 / 15 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (25 / 12 : ℚ), (1 / 6 : ℚ), (-5 / 4 : ℚ), (-37 / 6 : ℚ)], ![(13 / 12 : ℚ), 0, 0, (-13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ), (-7 / 12 : ℚ)], ![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (-25 / 6 : ℚ), (2 / 3 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 11 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ), (-14 / 11 : ℚ)], ![(-13 / 11 : ℚ), (-2 / 11 : ℚ), (-46 / 11 : ℚ), (-13 / 11 : ℚ), (-6 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 17 : ℚ), 0, (4 / 17 : ℚ), (4 / 17 : ℚ), (-14 / 17 : ℚ)], ![(-21 / 17 : ℚ), (-4 / 17 : ℚ), (-72 / 17 : ℚ), (-21 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 19 : ℚ), 0, (2 / 19 : ℚ), (-10 / 19 : ℚ), (-14 / 19 : ℚ)], ![(-29 / 19 : ℚ), (-2 / 19 : ℚ), (-96 / 19 : ℚ), -1, (-6 / 19 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ), 0, -2], ![(-5 / 6 : ℚ), (-2 / 3 : ℚ), -4, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (15 / 7 : ℚ), (2 / 7 : ℚ), (-36 / 7 : ℚ), (-36 / 7 : ℚ)], ![(6 / 7 : ℚ), 0, 0, 0, (-17 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 11 : ℚ), 0, (2 / 11 : ℚ), (-14 / 11 : ℚ), (-7 / 11 : ℚ)], ![(-13 / 11 : ℚ), (-2 / 11 : ℚ), (-46 / 11 : ℚ), (-6 / 11 : ℚ), (-6 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (28 / 13 : ℚ), (4 / 13 : ℚ), (-62 / 13 : ℚ), (-62 / 13 : ℚ)], ![(11 / 13 : ℚ), 0, 0, 0, (-60 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-7 / 12 : ℚ), (-1 / 2 : ℚ)], ![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (-25 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 14 : ℚ), 0, (8 / 7 : ℚ), (17 / 14 : ℚ), (3 / 14 : ℚ)], ![(17 / 14 : ℚ), 0, (16 / 7 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-1 / 2 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, -1, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 6 : ℚ), (11 / 12 : ℚ), (-1 / 4 : ℚ), -1, 0], ![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), 0, 0, (-5 / 11 : ℚ), (-18 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-15 / 44 : ℚ), (-15 / 4 : ℚ), (-7 / 4 : ℚ), (-17 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 6 : ℚ), -2, 0], ![(-5 / 3 : ℚ), (-1 / 3 : ℚ), (-14 / 3 : ℚ), -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 8 : ℚ), 0, (1 / 8 : ℚ), (17 / 8 : ℚ), (1 / 4 : ℚ)], ![(5 / 4 : ℚ), 0, (1 / 4 : ℚ), (17 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 2, (1 / 3 : ℚ)], ![(7 / 6 : ℚ), 0, 0, 4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (3 / 4 : ℚ), (-3 / 4 : ℚ), (5 / 4 : ℚ), 0], ![(1 / 4 : ℚ), (3 / 4 : ℚ), 0, (5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (5 / 4 : ℚ), (1 / 4 : ℚ)], ![(9 / 8 : ℚ), 0, (1 / 8 : ℚ), (5 / 2 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (7 / 6 : ℚ), (-7 / 6 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (7 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(2 / 3 : ℚ), 0, 3, -1, 1], ![(5 / 2 : ℚ), 0, 6, 1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 2 : ℚ), 0, 3, -1, 1], ![(9 / 4 : ℚ), 0, 6, 0, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 2 : ℚ), 0, 3, -1, 1], ![(5 / 2 : ℚ), 0, 6, -1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 6 : ℚ), 0, 3, 0, 1], ![(3 / 2 : ℚ), 0, 6, 1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 2, 0, -1], ![0, -2, 0, (-1 / 2 : ℚ), 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), -2, 1], ![-2, 0, 0, (-19 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (21 / 16 : ℚ), 0, -1], ![0, -2, (-9 / 16 : ℚ), (-7 / 8 : ℚ), (-15 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (10 / 9 : ℚ), 0, -4], ![0, -2, (-13 / 36 : ℚ), (-55 / 36 : ℚ), (-35 / 18 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), -2, 0], ![-2, 0, 0, (-19 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (13 / 11 : ℚ), 0, -4], ![0, -2, (-15 / 22 : ℚ), (-25 / 22 : ℚ), (-43 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, -2, (-2 / 3 : ℚ), (5 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, -2, (-1 / 6 : ℚ), (7 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![0, -2, (-1 / 2 : ℚ), (3 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 1], ![0, -2, (-3 / 2 : ℚ), 1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 4 : ℚ), (5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 4 : ℚ), (5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 4 : ℚ), (5 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, -2, (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![0, -2, (-1 / 2 : ℚ), (1 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 1], ![0, -2, (-3 / 2 : ℚ), 0, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-2 / 3 : ℚ), (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 1, 0], ![-2, 0, (-14 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-1 / 6 : ℚ), (7 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 1], ![0, -2, -1, -1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 6 : ℚ), (-1 / 3 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, -1, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-1 / 2 : ℚ), (1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -4], ![0, -2, (-3 / 4 : ℚ), (17 / 28 : ℚ), (-27 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -4], ![0, -2, (-1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -4], ![0, -2, (-5 / 3 : ℚ), 1, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -4], ![0, -2, (-1 / 2 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -4], ![0, -2, (-1 / 4 : ℚ), 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -2], ![0, -2, (-1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -4], ![0, -2, (-1 / 2 : ℚ), (1 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -4, -2], ![0, -2, (-1 / 3 : ℚ), -1, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (-4 / 3 : ℚ), 1, 1], ![(-7 / 6 : ℚ), 0, (-25 / 6 : ℚ), -1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (-1 / 2 : ℚ), 0, 2, (-1 / 6 : ℚ)], ![(-5 / 3 : ℚ), (-1 / 6 : ℚ), -5, (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 35 : ℚ), (-12 / 35 : ℚ), (-32 / 35 : ℚ), (71 / 35 : ℚ), (-4 / 35 : ℚ)], ![(-11 / 7 : ℚ), (-8 / 35 : ℚ), (-164 / 35 : ℚ), (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 16 : ℚ), (65 / 32 : ℚ), (7 / 32 : ℚ), (-37 / 32 : ℚ), (-37 / 32 : ℚ)], ![(9 / 32 : ℚ), 0, 0, 0, (-35 / 32 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (15 / 7 : ℚ), (4 / 7 : ℚ), (-5 / 7 : ℚ), (-36 / 7 : ℚ)], ![(6 / 7 : ℚ), 0, 0, 0, (-17 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (28 / 13 : ℚ), (7 / 13 : ℚ), (-6 / 13 : ℚ), (-62 / 13 : ℚ)], ![(11 / 13 : ℚ), 0, 0, 0, (-60 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (-4 / 3 : ℚ), 0, 1], ![(-7 / 6 : ℚ), 0, (-25 / 6 : ℚ), -1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (5 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 42 : ℚ), 0, (-26 / 21 : ℚ), (29 / 42 : ℚ), (-73 / 42 : ℚ)], ![(-22 / 21 : ℚ), (-3 / 14 : ℚ), (-23 / 6 : ℚ), (31 / 42 : ℚ), (-10 / 21 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 5 : ℚ), (21 / 10 : ℚ), (1 / 10 : ℚ), (-13 / 10 : ℚ), (-31 / 5 : ℚ)], ![(11 / 10 : ℚ), 0, 0, (-11 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 12 : ℚ), (13 / 15 : ℚ), (-29 / 30 : ℚ), (-19 / 60 : ℚ), (-59 / 30 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 15 : ℚ), (-34 / 15 : ℚ), 0, (-29 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), 0, 0, (1 / 11 : ℚ), (-18 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-15 / 44 : ℚ), (-15 / 4 : ℚ), (-12 / 11 : ℚ), (-17 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 17 : ℚ), 0, (-5 / 17 : ℚ), (2 / 17 : ℚ), (-24 / 17 : ℚ)], ![(-19 / 17 : ℚ), (-21 / 34 : ℚ), (-7 / 2 : ℚ), (-19 / 17 : ℚ), (-23 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (-2 / 5 : ℚ), 0, (-16 / 15 : ℚ), (-2 / 15 : ℚ)], ![(-23 / 15 : ℚ), (-2 / 15 : ℚ), (-24 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 6 : ℚ), -1, 0], ![(-5 / 3 : ℚ), (-1 / 3 : ℚ), (-14 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (15 / 7 : ℚ), (4 / 7 : ℚ), (-36 / 7 : ℚ), (-36 / 7 : ℚ)], ![(6 / 7 : ℚ), 0, 0, 0, (-17 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), (-3 / 11 : ℚ), (-1 / 2 : ℚ), (-1 / 11 : ℚ), (5 / 22 : ℚ)], ![(-15 / 11 : ℚ), (-1 / 11 : ℚ), (-50 / 11 : ℚ), 0, (3 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (28 / 13 : ℚ), (7 / 13 : ℚ), (-62 / 13 : ℚ), (-62 / 13 : ℚ)], ![(11 / 13 : ℚ), 0, 0, 0, (-60 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (-1 / 3 : ℚ), (-7 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ)], ![(-3 / 2 : ℚ), (-1 / 6 : ℚ), (-14 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 6 : ℚ), 0, (4 / 3 : ℚ), (8 / 3 : ℚ), (-1 / 3 : ℚ)], ![(3 / 2 : ℚ), (2 / 3 : ℚ), (4 / 3 : ℚ), (8 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 24 : ℚ), 0, (9 / 8 : ℚ), (53 / 24 : ℚ), (1 / 8 : ℚ)], ![(9 / 8 : ℚ), (1 / 24 : ℚ), (1 / 3 : ℚ), (13 / 24 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 12 : ℚ), 0, (7 / 6 : ℚ), (7 / 3 : ℚ), (5 / 3 : ℚ)], ![(5 / 4 : ℚ), (5 / 6 : ℚ), (7 / 6 : ℚ), (7 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-1 / 3 : ℚ), (-1 / 6 : ℚ), (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-4 / 7 : ℚ), (-2 / 7 : ℚ), (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xx, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (5 / 3 : ℚ), 0, 0, -1], ![(1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), 0, (-5 / 11 : ℚ), (-7 / 11 : ℚ), (-18 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-15 / 44 : ℚ), (-7 / 4 : ℚ), (-75 / 22 : ℚ), (-17 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .yy), (.xx, .xy), (.xx, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (5 / 3 : ℚ), 0, 0, -4], ![(1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 1, 0], ![(7 / 6 : ℚ), (1 / 6 : ℚ), (4 / 3 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 5 : ℚ), (2 / 5 : ℚ), (3 / 5 : ℚ), 1, 0], ![1, (2 / 5 : ℚ), (7 / 5 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (11 / 6 : ℚ), (1 / 3 : ℚ)], ![(13 / 6 : ℚ), (-1 / 6 : ℚ), 0, (11 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (3 / 2 : ℚ), (-1 / 2 : ℚ)], ![(3 / 2 : ℚ), 0, (1 / 2 : ℚ), (3 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (5 / 4 : ℚ), (1 / 4 : ℚ)], ![(9 / 8 : ℚ), 0, (1 / 8 : ℚ), (5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 2, 0], ![2, (-1 / 2 : ℚ), 0, 2, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (5 / 4 : ℚ), (1 / 4 : ℚ)], ![1, 0, 0, (5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (5 / 4 : ℚ), (-1 / 4 : ℚ)], ![(5 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (5 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (7 / 6 : ℚ), (1 / 6 : ℚ)], ![(13 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (5 / 4 : ℚ), (3 / 2 : ℚ)], ![(5 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (5 / 4 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (7 / 6 : ℚ), (1 / 6 : ℚ)], ![1, 0, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 6 : ℚ), (1 / 3 : ℚ), 1, 0, 0], ![(7 / 6 : ℚ), (4 / 3 : ℚ), 1, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 12 : ℚ), 0, (7 / 6 : ℚ), (-1 / 6 : ℚ), (5 / 3 : ℚ)], ![(5 / 4 : ℚ), (5 / 6 : ℚ), (7 / 6 : ℚ), (-1 / 6 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 12 : ℚ), 0, (7 / 6 : ℚ), (1 / 6 : ℚ), (5 / 3 : ℚ)], ![(5 / 4 : ℚ), (5 / 6 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(1 / 12 : ℚ), 0, (7 / 6 : ℚ), (5 / 3 : ℚ), (5 / 6 : ℚ)], ![(5 / 4 : ℚ), (5 / 6 : ℚ), (7 / 6 : ℚ), (5 / 3 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 2, 0, -1], ![0, -2, 0, (-1 / 2 : ℚ), 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), -2, 1], ![-2, 0, 0, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), 0, -1], ![0, -2, (-1 / 2 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (10 / 9 : ℚ), 0, -4], ![0, -2, (-13 / 36 : ℚ), (-23 / 36 : ℚ), (-35 / 18 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (9 / 4 : ℚ), (1 / 2 : ℚ), -5], ![(1 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.y, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), 0, -4], ![0, -2, (-1 / 2 : ℚ), 0, -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, -2, (-1 / 3 : ℚ), (4 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, -2, 0, (3 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![0, -2, (-1 / 2 : ℚ), (3 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 1], ![0, -2, (-1 / 2 : ℚ), 1, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-2 / 7 : ℚ), (9 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, 0, (3 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, -2, 0, (1 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![0, -2, (-1 / 3 : ℚ), (1 / 3 : ℚ), (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 1], ![0, -2, (-1 / 2 : ℚ), 0, 1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, 0, (1 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, -2, 0, (3 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, 0, -1, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, -2, 0, -1, 3]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-2 / 7 : ℚ), (1 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, (-1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, -2, 0, (1 / 2 : ℚ), -4]] }
]

theorem conicDetC25_checked : conicDetC25.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
