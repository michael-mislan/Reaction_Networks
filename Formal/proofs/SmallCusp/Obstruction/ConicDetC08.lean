import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC08 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-3 / 2 : ℚ), 0, -2, (-1 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-3 / 2 : ℚ), 0, -4, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (13 / 24 : ℚ), (-1 / 12 : ℚ), 0, (-17 / 12 : ℚ)], ![(-17 / 24 : ℚ), (11 / 24 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (7 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-4 / 3 : ℚ)], ![(-3 / 4 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, (-13 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (12 / 11 : ℚ), (-1 / 11 : ℚ), 0, (-50 / 11 : ℚ)], ![(-14 / 11 : ℚ), 1, (-25 / 11 : ℚ), (-1 / 11 : ℚ), (-19 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (11 / 18 : ℚ), (-1 / 9 : ℚ), 0, (-43 / 9 : ℚ)], ![(-5 / 6 : ℚ), (1 / 2 : ℚ), (-7 / 3 : ℚ), (-1 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, (-21 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, (-11 / 4 : ℚ), (-1 / 4 : ℚ), (-21 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 2 : ℚ), 0], ![0, -1, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 44 : ℚ), (-31 / 22 : ℚ), 0, (-31 / 22 : ℚ), (-7 / 22 : ℚ)], ![(-3 / 22 : ℚ), (-31 / 22 : ℚ), (-13 / 11 : ℚ), (-65 / 22 : ℚ), (-7 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-26 / 27 : ℚ), (28 / 27 : ℚ), 2, (2 / 27 : ℚ), (-136 / 27 : ℚ)], ![(-58 / 27 : ℚ), (8 / 9 : ℚ), (-4 / 27 : ℚ), 0, (-22 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (7 / 12 : ℚ), (25 / 12 : ℚ), (1 / 12 : ℚ), (-14 / 3 : ℚ)], ![(-9 / 4 : ℚ), (5 / 12 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ), (-22 / 5 : ℚ)], ![0, (-6 / 5 : ℚ), (-12 / 5 : ℚ), (-14 / 5 : ℚ), (-22 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), 0, (-5 / 12 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 12 : ℚ), (1 / 2 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-3 / 10 : ℚ), (-1 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (-7 / 10 : ℚ), (3 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -2, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, 0, (-10 / 13 : ℚ), (-12 / 13 : ℚ)], ![(-6 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ), (12 / 13 : ℚ), (-5 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-6 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-6 / 11 : ℚ), (-14 / 11 : ℚ), (6 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), 0, 0, (-5 / 24 : ℚ), (-5 / 24 : ℚ)], ![(-1 / 8 : ℚ), 0, (-1 / 24 : ℚ), (1 / 4 : ℚ), (-5 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-3 / 5 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (9 / 8 : ℚ), (1 / 8 : ℚ), (-47 / 24 : ℚ), (47 / 24 : ℚ)], ![(-47 / 24 : ℚ), (25 / 24 : ℚ), 0, 0, (47 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), 0], ![0, (-1 / 2 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-2 / 3 : ℚ), (-5 / 6 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (3 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ), (4 / 3 : ℚ)], ![-2, 0, (-2 / 3 : ℚ), (-4 / 3 : ℚ), (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -1, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-5 / 2 : ℚ), 0, (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 5 : ℚ), (-12 / 5 : ℚ)], ![(-7 / 5 : ℚ), (1 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-12 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), 0, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (2 / 11 : ℚ), 0, (2 / 11 : ℚ), (-12 / 11 : ℚ)], ![(-6 / 11 : ℚ), 0, (-29 / 22 : ℚ), (-1 / 2 : ℚ), (-5 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (2 / 7 : ℚ), 0, 1, (-24 / 7 : ℚ)], ![(-11 / 7 : ℚ), 0, (-2 / 7 : ℚ), 0, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, 0, 2, -6], ![(-10 / 3 : ℚ), 0, (-2 / 3 : ℚ), 2, -6]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-6 / 7 : ℚ), (-10 / 7 : ℚ), (-4 / 7 : ℚ), 0], ![(-2 / 7 : ℚ), (-6 / 7 : ℚ), (-24 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-8 / 7 : ℚ), (-12 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)], ![0, (-8 / 7 : ℚ), -4, (4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-8 / 5 : ℚ), (-12 / 5 : ℚ), 0, 0], ![0, (-8 / 5 : ℚ), (-28 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .xy), (.xx, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (-5 / 12 : ℚ), (-1 / 12 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 6 : ℚ), (-1 / 4 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, 0, 0, (-8 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (10 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-7 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, 0, (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 3 : ℚ), (-4 / 9 : ℚ)], ![0, (-4 / 3 : ℚ), (-4 / 3 : ℚ), (-14 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, -2], ![(1 / 6 : ℚ), -1, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, 0, -1], ![(-1 / 3 : ℚ), 0, 0, -1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), -1, 1, 0], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0], ![(-1 / 6 : ℚ), 0, (2 / 3 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), 0, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0, (-3 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0], ![0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-8 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, (-8 / 7 : ℚ), 0, (-8 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (-25 / 22 : ℚ), 0, (-47 / 22 : ℚ), (9 / 44 : ℚ)], ![(13 / 44 : ℚ), (-13 / 11 : ℚ), (1 / 22 : ℚ), (-24 / 11 : ℚ), (-7 / 44 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-19 / 12 : ℚ), 0, (-5 / 2 : ℚ), (13 / 12 : ℚ)], ![(5 / 4 : ℚ), (-7 / 4 : ℚ), (1 / 6 : ℚ), (-8 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-19 / 10 : ℚ), 0, (-43 / 20 : ℚ), 0], ![(1 / 20 : ℚ), (-27 / 10 : ℚ), (1 / 20 : ℚ), (-11 / 5 : ℚ), (-19 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 30 : ℚ), (-11 / 10 : ℚ), 0, (-21 / 10 : ℚ), (-1 / 15 : ℚ)], ![(-1 / 30 : ℚ), (-17 / 15 : ℚ), (1 / 30 : ℚ), (-32 / 15 : ℚ), (11 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-55 / 36 : ℚ), (-1 / 18 : ℚ), (-41 / 18 : ℚ), 0], ![(1 / 18 : ℚ), (-17 / 9 : ℚ), 0, (-43 / 18 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (1 / 4 : ℚ), (-1 / 22 : ℚ), 0, (-13 / 11 : ℚ)], ![(-15 / 44 : ℚ), (9 / 44 : ℚ), (-23 / 11 : ℚ), (-1 / 22 : ℚ), (27 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 2 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ)], ![(-2 / 3 : ℚ), (5 / 12 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), 1, (-1 / 11 : ℚ), 0, (-48 / 11 : ℚ)], ![(-13 / 11 : ℚ), (10 / 11 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (-18 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (1 / 2 : ℚ), (-1 / 9 : ℚ), 0, (-41 / 9 : ℚ)], ![(-13 / 18 : ℚ), (7 / 18 : ℚ), (-20 / 9 : ℚ), (-1 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (7 / 6 : ℚ), 2, (1 / 6 : ℚ), -2], ![-2, 1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 12 : ℚ), (7 / 12 : ℚ), 2, (1 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-25 / 12 : ℚ), (1 / 2 : ℚ), (-1 / 12 : ℚ), 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (2 / 3 : ℚ), (13 / 6 : ℚ), (1 / 6 : ℚ), (-29 / 6 : ℚ)], ![(-7 / 3 : ℚ), (1 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-2 / 3 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (5 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, 0, (-8 / 11 : ℚ), (-8 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (10 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-6 / 11 : ℚ), (-6 / 11 : ℚ), (6 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, 0, (-2 / 5 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), 0, 0, (1 / 2 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ)], ![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, (3 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), -1, -1, 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, 0, (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), 0, 0, 0, (-20 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, (-10 / 7 : ℚ), (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ), 0, (4 / 7 : ℚ)], ![0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), (2 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)], ![0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), (4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), 0, (-1 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), (1 / 10 : ℚ), 0, (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0], ![(-1 / 6 : ℚ), 0, (2 / 3 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-3 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![(-2 / 5 : ℚ), 0, (1 / 5 : ℚ), (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), (-5 / 11 : ℚ), (-2 / 11 : ℚ), (1 / 11 : ℚ), 0], ![0, (-5 / 11 : ℚ), (2 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), -1, 0, 0, (1 / 10 : ℚ)], ![(3 / 10 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), -1, 0, 0, (1 / 5 : ℚ)], ![(3 / 10 : ℚ), -1, 0, 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -1, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 4 : ℚ), -1, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, -1], ![(1 / 6 : ℚ), -1, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, 0], ![(1 / 6 : ℚ), -1, 0, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, 0], ![(1 / 6 : ℚ), -1, 0, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, 0], ![(1 / 6 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, -1, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, 0, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), -1, 0, 0, (1 / 5 : ℚ)], ![(3 / 10 : ℚ), -1, 0, 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -1, 0, 0], ![(-1 / 2 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 4 : ℚ), 0, 0, -1, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, 0, 0], ![(-1 / 3 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, 0, (-13 / 6 : ℚ)], ![(-1 / 3 : ℚ), 0, 0, -1, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, (-1 / 6 : ℚ)], ![(1 / 6 : ℚ), -1, 0, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, 0, -2], ![(-1 / 3 : ℚ), 0, 0, -1, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0, 0], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, -1, 1, 0], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, -1, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), -1, 1, (1 / 6 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (1 / 6 : ℚ), -1, 1, (-13 / 6 : ℚ)], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -1, 1, -2], ![-1, 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 8 : ℚ), 0], ![(-1 / 8 : ℚ), 0, (3 / 4 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (5 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-8 / 11 : ℚ), (1 / 11 : ℚ), 0, 0], ![(4 / 11 : ℚ), (-8 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![0, 0, (3 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), 0, -2], ![(-1 / 6 : ℚ), 0, (2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, -1], ![(-1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 3]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), 0, (-1 / 6 : ℚ)], ![(-1 / 6 : ℚ), 0, (2 / 3 : ℚ), 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), 0, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ)], ![0, (-1 / 5 : ℚ), (1 / 10 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (-7 / 6 : ℚ), -1], ![(-1 / 2 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (-7 / 6 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 2 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, (3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-6 / 5 : ℚ), 0, 0, (3 / 10 : ℚ)], ![(1 / 2 : ℚ), (-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-6 / 5 : ℚ), 0, 0, (2 / 5 : ℚ)], ![(1 / 2 : ℚ), (-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, 0], ![(1 / 8 : ℚ), (-5 / 4 : ℚ), 0, (1 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (-13 / 8 : ℚ), (1 / 8 : ℚ), 0, 0], ![0, (-13 / 8 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-4 / 3 : ℚ), 0, 0, 0], ![(1 / 12 : ℚ), (-4 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-6 / 5 : ℚ), (-1 / 10 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-6 / 5 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-6 / 5 : ℚ), (-1 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-6 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, 0], ![(-1 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-9 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 4 : ℚ), -3], ![(-1 / 2 : ℚ), 0, (-3 / 2 : ℚ), (-3 / 2 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-11 / 7 : ℚ), (-2 / 7 : ℚ), (-24 / 7 : ℚ)], ![(-4 / 7 : ℚ), 0, (-11 / 7 : ℚ), (-11 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 1, -1], ![-1, 0, (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), (3 / 2 : ℚ), 0], ![(-3 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-8 / 5 : ℚ), 0, (-3 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-8 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), 0, (3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0], ![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 10 : ℚ), 0, 0], ![(2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (1 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (1 / 2 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), 0, (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 10 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-3 / 5 : ℚ), -1], ![(-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)], ![(1 / 2 : ℚ), (-3 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0], ![0, (-1 / 2 : ℚ), 0, (1 / 2 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), 0, -1], ![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, 0, -1, 0], ![0, -1, 0, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), 0, (-8 / 7 : ℚ), 0, (-20 / 7 : ℚ)], ![(-8 / 7 : ℚ), 0, (-8 / 7 : ℚ), 0, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 4 : ℚ), 0], ![0, (-1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-6 / 5 : ℚ), 0, 0, 0], ![(2 / 5 : ℚ), (-6 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), (-8 / 7 : ℚ), 0], ![(-2 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (-4 / 3 : ℚ), (-1 / 15 : ℚ), (-2 / 15 : ℚ), (8 / 15 : ℚ)], ![(4 / 5 : ℚ), (-22 / 15 : ℚ), 0, (-1 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (-17 / 14 : ℚ), 0, (-1 / 14 : ℚ), (3 / 7 : ℚ)], ![(1 / 2 : ℚ), (-9 / 7 : ℚ), (1 / 14 : ℚ), 0, (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-5 / 2 : ℚ), (-11 / 10 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-19 / 13 : ℚ), 0, (-2 / 13 : ℚ), 0], ![0, (-21 / 13 : ℚ), (2 / 13 : ℚ), 0, (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-8 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0], ![(1 / 10 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-11 / 8 : ℚ), 0, (-1 / 2 : ℚ), (1 / 2 : ℚ)], ![(1 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![0, -2, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 17 : ℚ), (-20 / 17 : ℚ), 0, (-3 / 34 : ℚ), (-4 / 17 : ℚ)], ![0, (-21 / 17 : ℚ), (1 / 17 : ℚ), (-1 / 17 : ℚ), (-3 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-14 / 9 : ℚ), (-1 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, (-16 / 9 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-29 / 24 : ℚ), (-1 / 24 : ℚ), (1 / 3 : ℚ), (11 / 24 : ℚ)], ![(13 / 24 : ℚ), (-31 / 24 : ℚ), 0, (-1 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-6 / 5 : ℚ), 0, (3 / 10 : ℚ), (3 / 10 : ℚ)], ![(1 / 2 : ℚ), (-6 / 5 : ℚ), (1 / 10 : ℚ), (-1 / 5 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 10 : ℚ), (-1 / 4 : ℚ), 0, 0], ![(1 / 20 : ℚ), (-19 / 20 : ℚ), (-9 / 20 : ℚ), (1 / 20 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 1, -1], ![1, (-3 / 2 : ℚ), 0, -1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 26 : ℚ), (-29 / 26 : ℚ), 0, (9 / 52 : ℚ), 0], ![(1 / 4 : ℚ), (-15 / 13 : ℚ), (1 / 26 : ℚ), (-7 / 52 : ℚ), (1 / 52 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (-25 / 22 : ℚ), 0, (9 / 44 : ℚ), 0], ![(13 / 44 : ℚ), (-13 / 11 : ℚ), (1 / 22 : ℚ), (-7 / 44 : ℚ), (1 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-11 / 10 : ℚ), 0, (3 / 20 : ℚ), (1 / 20 : ℚ)], ![(1 / 4 : ℚ), (-11 / 10 : ℚ), (1 / 20 : ℚ), (-1 / 10 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-17 / 20 : ℚ), (-1 / 4 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ)], ![0, (-17 / 20 : ℚ), (-9 / 20 : ℚ), (1 / 20 : ℚ), (-1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-49 / 44 : ℚ), (-1 / 44 : ℚ), (1 / 4 : ℚ), 0], ![(13 / 44 : ℚ), (-51 / 44 : ℚ), 0, (1 / 22 : ℚ), (-7 / 44 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 1, -1], ![1, (-7 / 4 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 13 : ℚ), (-31 / 26 : ℚ), (-1 / 26 : ℚ), (11 / 26 : ℚ), (-1 / 13 : ℚ)], ![(1 / 2 : ℚ), (-33 / 26 : ℚ), 0, (1 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-29 / 24 : ℚ), (-1 / 24 : ℚ), (11 / 24 : ℚ), 0], ![(13 / 24 : ℚ), (-31 / 24 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-11 / 10 : ℚ), 0, (1 / 5 : ℚ), (1 / 20 : ℚ)], ![(1 / 4 : ℚ), (-11 / 10 : ℚ), (1 / 20 : ℚ), (1 / 20 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 8 : ℚ), (-1 / 4 : ℚ), 0, 0], ![(1 / 16 : ℚ), (-7 / 8 : ℚ), (-7 / 16 : ℚ), (1 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-7 / 4 : ℚ), 0, (7 / 4 : ℚ), (-1 / 4 : ℚ)], ![(3 / 2 : ℚ), (-7 / 4 : ℚ), (3 / 4 : ℚ), (7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-9 / 4 : ℚ), 0, (13 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), -1, 0, 0], ![(-1 / 6 : ℚ), (-1 / 2 : ℚ), -2, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-19 / 13 : ℚ), 0, 0, 0], ![(2 / 13 : ℚ), (-21 / 13 : ℚ), (2 / 13 : ℚ), (-8 / 13 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 10 : ℚ), 0, 0, 0], ![(1 / 10 : ℚ), (-7 / 5 : ℚ), (1 / 10 : ℚ), (-2 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (1 / 8 : ℚ)], ![(1 / 8 : ℚ), (-5 / 4 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 30 : ℚ), (-11 / 10 : ℚ), 0, (-11 / 10 : ℚ), (-1 / 15 : ℚ)], ![(-1 / 30 : ℚ), (-17 / 15 : ℚ), (1 / 30 : ℚ), (-17 / 15 : ℚ), (11 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 13 : ℚ), (-77 / 52 : ℚ), 0, (-16 / 13 : ℚ), (-3 / 13 : ℚ)], ![(-1 / 13 : ℚ), (-47 / 26 : ℚ), (1 / 13 : ℚ), (-17 / 13 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-19 / 13 : ℚ), 0, (-2 / 13 : ℚ), 0], ![0, (-21 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-11 / 7 : ℚ), 0, 0, 0], ![0, (-11 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-18 / 13 : ℚ), (-1 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ)], ![0, (-20 / 13 : ℚ), 0, (2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-11 / 7 : ℚ), 0, (-2 / 7 : ℚ), (2 / 7 : ℚ)], ![0, (-11 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ), (3 / 4 : ℚ)], ![(3 / 4 : ℚ), (-7 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 12 : ℚ), (5 / 12 : ℚ), (-41 / 12 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 12 : ℚ), (-7 / 6 : ℚ), (-7 / 12 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-7 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 12 : ℚ), (-1 / 3 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (-7 / 6 : ℚ), (5 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), 0, (-1 / 20 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ)], ![(-1 / 10 : ℚ), 0, (-11 / 10 : ℚ), (1 / 4 : ℚ), (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, (-1 / 2 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), 0, (-1 / 22 : ℚ), (-2 / 11 : ℚ), (-24 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-1 / 22 : ℚ), (-12 / 11 : ℚ), (5 / 22 : ℚ), (-7 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, (-2 / 11 : ℚ), (-8 / 11 : ℚ), (-32 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-15 / 11 : ℚ), (10 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-1 / 5 : ℚ), (-1 / 20 : ℚ), 0, (-7 / 4 : ℚ)], ![(1 / 10 : ℚ), (-1 / 5 : ℚ), (-9 / 10 : ℚ), (1 / 20 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), -1, (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), (1 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), 0, (-1 / 24 : ℚ), (-1 / 8 : ℚ), (-13 / 6 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 24 : ℚ), (-13 / 12 : ℚ), (1 / 24 : ℚ), (-7 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-7 / 6 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (-1 / 12 : ℚ)], ![(1 / 2 : ℚ), (-5 / 4 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-3 / 10 : ℚ), (-23 / 10 : ℚ)], ![(-1 / 5 : ℚ), 0, (-6 / 5 : ℚ), (1 / 10 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 8 : ℚ), (3 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, (-10 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, (-11 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), 0, (-3 / 5 : ℚ)]] }
]

theorem conicDetC08_checked : conicDetC08.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
