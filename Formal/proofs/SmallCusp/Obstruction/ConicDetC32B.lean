import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC32B : List RationalConicRecord := [
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), (1 / 10 : ℚ), (-23 / 10 : ℚ), (-6 / 5 : ℚ)], ![0, (-23 / 10 : ℚ), (1 / 2 : ℚ), (-23 / 10 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 24 : ℚ), (-1 / 24 : ℚ), (-29 / 24 : ℚ), 0, (1 / 2 : ℚ)], ![(-31 / 24 : ℚ), 0, (-31 / 24 : ℚ), (1 / 12 : ℚ), (25 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, (-7 / 6 : ℚ), (5 / 6 : ℚ), (1 / 12 : ℚ)], ![(-7 / 6 : ℚ), (1 / 12 : ℚ), (-7 / 6 : ℚ), (19 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 11 : ℚ), 0, (-32 / 11 : ℚ), (-16 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-32 / 11 : ℚ), (-2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-13 / 5 : ℚ)], ![0, (-13 / 5 : ℚ), 0, (11 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 12 : ℚ), (-1 / 3 : ℚ), (-1 / 4 : ℚ), (-7 / 3 : ℚ)], ![(-1 / 12 : ℚ), (-7 / 6 : ℚ), (5 / 12 : ℚ), (1 / 12 : ℚ), (-7 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-1 / 16 : ℚ), (3 / 8 : ℚ), (5 / 16 : ℚ), (-1 / 16 : ℚ)], ![(-19 / 16 : ℚ), 0, 0, (1 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 10 : ℚ), (-2 / 5 : ℚ), (-3 / 10 : ℚ), (-23 / 10 : ℚ)], ![0, (-6 / 5 : ℚ), (1 / 2 : ℚ), (1 / 10 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 16 : ℚ), (-3 / 16 : ℚ), 0, (-17 / 8 : ℚ)], ![0, (-17 / 16 : ℚ), (1 / 4 : ℚ), 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 16 : ℚ), (-3 / 16 : ℚ), 0, (-35 / 16 : ℚ)], ![0, (-17 / 16 : ℚ), (1 / 4 : ℚ), 0, (29 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 10 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-23 / 10 : ℚ)], ![0, (-6 / 5 : ℚ), (1 / 2 : ℚ), (-1 / 5 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (3 / 10 : ℚ), (3 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-19 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-9 / 8 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-19 / 8 : ℚ)], ![0, (-9 / 8 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 20 : ℚ), (1 / 20 : ℚ), (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (1 / 20 : ℚ), (1 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 7 : ℚ), (2 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, 0, 0, (-8 / 3 : ℚ)], ![(-2 / 3 : ℚ), -1, 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 11 : ℚ), (-4 / 11 : ℚ), (-27 / 11 : ℚ), (-26 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-13 / 11 : ℚ), (5 / 11 : ℚ), (1 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 20 : ℚ), 0, (-9 / 5 : ℚ), (-7 / 4 : ℚ)], ![(-1 / 5 : ℚ), (-9 / 10 : ℚ), (1 / 20 : ℚ), (-1 / 20 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-1 / 8 : ℚ), (3 / 4 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ)], ![(-11 / 8 : ℚ), 0, 0, (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), (-1 / 14 : ℚ), (5 / 14 : ℚ), (-1 / 14 : ℚ), (1 / 14 : ℚ)], ![(-8 / 7 : ℚ), 0, 0, (1 / 14 : ℚ), (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 20 : ℚ), (-1 / 5 : ℚ), (-43 / 20 : ℚ), (-11 / 10 : ℚ)], ![0, (-11 / 10 : ℚ), (1 / 4 : ℚ), (-43 / 20 : ℚ), (-11 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 8 : ℚ), (-1 / 4 : ℚ), 0, (-9 / 4 : ℚ)], ![0, (-9 / 8 : ℚ), (1 / 8 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), (9 / 8 : ℚ), (-13 / 8 : ℚ)], ![(-9 / 8 : ℚ), 0, (1 / 8 : ℚ), (9 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), 0], ![(-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 10 : ℚ), 0, (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (1 / 20 : ℚ), (3 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), 0, (2 / 5 : ℚ), 0, (-1 / 10 : ℚ)], ![(-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-19 / 8 : ℚ)], ![0, (-9 / 8 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 20 : ℚ), (1 / 20 : ℚ), (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-21 / 20 : ℚ), 0, (1 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), 0, 1, -1, (-2 / 7 : ℚ)], ![(-11 / 7 : ℚ), 0, 0, -1, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 1, -1, (-1 / 2 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, -1, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ)], ![(-5 / 4 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ)], ![(-6 / 5 : ℚ), 0, (1 / 10 : ℚ), 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ)], ![(-5 / 4 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ)], ![(-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ), 0, 0], ![(-6 / 5 : ℚ), 0, (1 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![0, -1, (1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![0, -1, (1 / 2 : ℚ), 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-19 / 8 : ℚ)], ![0, (-9 / 8 : ℚ), (3 / 8 : ℚ), (-1 / 4 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-10 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, (-11 / 4 : ℚ)], ![0, (-5 / 4 : ℚ), 0, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-11 / 4 : ℚ), (-5 / 2 : ℚ)], ![0, (-5 / 4 : ℚ), 0, (5 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, (-7 / 3 : ℚ), (-13 / 6 : ℚ)], ![0, (-7 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, (-5 / 2 : ℚ), (-11 / 6 : ℚ)], ![0, (-7 / 6 : ℚ), 0, (3 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-11 / 4 : ℚ), (-9 / 4 : ℚ)], ![0, (-5 / 4 : ℚ), 0, (5 / 4 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 3 : ℚ), (-11 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, (1 / 3 : ℚ), (-11 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-43 / 20 : ℚ), (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-21 / 20 : ℚ), 0, (1 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-9 / 4 : ℚ), (-9 / 4 : ℚ)], ![0, (-13 / 12 : ℚ), 0, (-1 / 3 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![(-7 / 5 : ℚ), 0, (-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-16 / 5 : ℚ), (-16 / 5 : ℚ)], ![0, (-7 / 5 : ℚ), 0, (2 / 5 : ℚ), (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -3, (-5 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), 0, -3, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 11 : ℚ), (-1 / 11 : ℚ), (-13 / 11 : ℚ), (-1 / 11 : ℚ), 0], ![(-14 / 11 : ℚ), 0, (-14 / 11 : ℚ), (1 / 11 : ℚ), (6 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 7 : ℚ), 0, (-18 / 7 : ℚ), (-17 / 7 : ℚ)], ![0, (-9 / 7 : ℚ), 0, (-5 / 7 : ℚ), (-17 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![(-3 / 2 : ℚ), 0, (-3 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 7 : ℚ), 0, (-24 / 7 : ℚ), (-20 / 7 : ℚ)], ![0, (-11 / 7 : ℚ), 0, (2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-45 / 32 : ℚ), (-9 / 4 : ℚ), (-3 / 32 : ℚ), (3 / 16 : ℚ), (31 / 32 : ℚ)], ![(-3 / 16 : ℚ), (-39 / 32 : ℚ), 0, -3, (-25 / 32 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (1 / 8 : ℚ), (-11 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-19 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-86 / 39 : ℚ), (-1 / 13 : ℚ), (2 / 13 : ℚ), (-17 / 39 : ℚ)], ![(-2 / 13 : ℚ), (-46 / 39 : ℚ), 0, (-110 / 39 : ℚ), (-11 / 39 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-14 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (9 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (1 / 4 : ℚ), -5], ![(-1 / 4 : ℚ), 0, (-9 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (1 / 6 : ℚ), (-4 / 3 : ℚ), (1 / 6 : ℚ), (-31 / 12 : ℚ)], ![0, 0, (-5 / 2 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (-50 / 21 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), (-52 / 21 : ℚ)], ![(-2 / 7 : ℚ), (-4 / 3 : ℚ), 0, (-20 / 7 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 20 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-17 / 8 : ℚ), 0, 0, (3 / 8 : ℚ)], ![0, (-5 / 4 : ℚ), 0, (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-1 / 9 : ℚ), (-11 / 9 : ℚ), (-2 / 9 : ℚ), (-14 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-18 / 5 : ℚ), (-92 / 15 : ℚ), 0, 0, 0], ![(-8 / 15 : ℚ), (-46 / 15 : ℚ), (9 / 5 : ℚ), (-116 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-13 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![0, (-4 / 3 : ℚ), 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 5 : ℚ), (-32 / 5 : ℚ), 0, 0, 0], ![(-4 / 5 : ℚ), (-18 / 5 : ℚ), (8 / 5 : ℚ), (-38 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-43 / 17 : ℚ), (-80 / 17 : ℚ), (3 / 17 : ℚ), (35 / 17 : ℚ), 0], ![(-3 / 17 : ℚ), (-40 / 17 : ℚ), (-89 / 17 : ℚ), (-32 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-109 / 280 : ℚ), 0, (2 / 35 : ℚ), (-9 / 140 : ℚ), (-146 / 35 : ℚ)], ![(-121 / 280 : ℚ), (-1 / 35 : ℚ), (-117 / 140 : ℚ), (17 / 140 : ℚ), (-29 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), -5, (3 / 4 : ℚ), (7 / 4 : ℚ), 0], ![0, (-5 / 2 : ℚ), (-19 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 13 : ℚ), (4 / 13 : ℚ), (8 / 13 : ℚ), (-9 / 13 : ℚ), (-68 / 13 : ℚ)], ![0, 0, (6 / 13 : ℚ), 0, (-66 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, (2 / 11 : ℚ), (-17 / 11 : ℚ), (-74 / 11 : ℚ)], ![(-2 / 11 : ℚ), 0, (-6 / 11 : ℚ), (-15 / 11 : ℚ), (-37 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), (-28 / 9 : ℚ), (2 / 9 : ℚ), (-2 / 9 : ℚ), (-17 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-5 / 3 : ℚ), (-28 / 9 : ℚ), 0, (-16 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-26 / 5 : ℚ)], ![(-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ), (-50 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-8 / 11 : ℚ), (6 / 11 : ℚ), (-49 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), (-22 / 5 : ℚ), (4 / 5 : ℚ), (-7 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-11 / 5 : ℚ), (-47 / 10 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), (-44 / 9 : ℚ), 2, (-5 / 3 : ℚ), 0], ![(-4 / 9 : ℚ), (-8 / 3 : ℚ), (-52 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (-13 / 12 : ℚ), 0, 0], ![(-1 / 12 : ℚ), 0, (-13 / 6 : ℚ), 0, (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-29 / 12 : ℚ), 0, (-4 / 3 : ℚ), (5 / 6 : ℚ)], ![0, (-3 / 2 : ℚ), 0, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-7 / 6 : ℚ), 0, (-5 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-7 / 3 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-21 / 10 : ℚ), 0, (-11 / 10 : ℚ), (1 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), 0, (-11 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-11 / 10 : ℚ), (-1 / 5 : ℚ), (-27 / 5 : ℚ)], ![(-3 / 10 : ℚ), 0, (-11 / 5 : ℚ), (-2 / 5 : ℚ), (-27 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 9 : ℚ), (-23 / 9 : ℚ), 0, (-13 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, (-5 / 3 : ℚ), 0, (-26 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), (-13 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-13 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-3 / 2 : ℚ), 0, (-14 / 5 : ℚ), (-12 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (1 / 3 : ℚ)], ![(-1 / 12 : ℚ), (-9 / 8 : ℚ), 0, (-55 / 12 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), (-13 / 5 : ℚ), (4 / 5 : ℚ)], ![0, (-7 / 5 : ℚ), 0, (-27 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), (-43 / 12 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (1 / 2 : ℚ)], ![(-1 / 12 : ℚ), (-11 / 6 : ℚ), 0, (-55 / 12 : ℚ), (7 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-8 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, (-31 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-8 / 3 : ℚ), (-1 / 3 : ℚ), -3, (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, (-19 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (-28 / 11 : ℚ), (-25 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-14 / 11 : ℚ), 0, (-58 / 11 : ℚ), (-24 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-43 / 17 : ℚ), (-80 / 17 : ℚ), 0, (35 / 17 : ℚ), 0], ![(-3 / 17 : ℚ), (-40 / 17 : ℚ), (-86 / 17 : ℚ), (-32 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-79 / 236 : ℚ), (4 / 59 : ℚ), 0, (-13 / 118 : ℚ), (-252 / 59 : ℚ)], ![(-99 / 236 : ℚ), 0, (-75 / 236 : ℚ), (21 / 118 : ℚ), (-250 / 59 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), -5, 0, (7 / 4 : ℚ), 0], ![0, (-5 / 2 : ℚ), (-19 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (4 / 13 : ℚ), (4 / 13 : ℚ), (-9 / 13 : ℚ), (-68 / 13 : ℚ)], ![0, 0, (4 / 13 : ℚ), 0, (-66 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, 0, (-10 / 7 : ℚ), (-46 / 7 : ℚ)], ![(-1 / 7 : ℚ), 0, (-2 / 7 : ℚ), (-9 / 7 : ℚ), (-23 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 7 : ℚ), (1 / 7 : ℚ), (3 / 7 : ℚ), (-11 / 7 : ℚ), (-67 / 14 : ℚ)], ![(-1 / 7 : ℚ), 0, (2 / 7 : ℚ), (-10 / 7 : ℚ), (-33 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), (-22 / 5 : ℚ), 0, (1 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-11 / 5 : ℚ), (-23 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-49 / 11 : ℚ), (-13 / 11 : ℚ), (2 / 11 : ℚ), (-1 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-51 / 22 : ℚ), -5, (-37 / 22 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), (-22 / 5 : ℚ), 0, (-7 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-11 / 5 : ℚ), (-23 / 5 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (4 / 3 : ℚ), 1, -5], ![(-1 / 3 : ℚ), 0, 0, 1, -5]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-45 / 32 : ℚ), (-9 / 4 : ℚ), (-3 / 32 : ℚ), (-79 / 32 : ℚ), (31 / 32 : ℚ)], ![(-3 / 16 : ℚ), (-39 / 32 : ℚ), 0, (-85 / 32 : ℚ), (-25 / 32 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 20 : ℚ), (-43 / 20 : ℚ), (-1 / 20 : ℚ), (-9 / 4 : ℚ), (9 / 20 : ℚ)], ![0, (-23 / 20 : ℚ), 0, (-47 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-133 / 80 : ℚ), (-47 / 20 : ℚ), (-3 / 80 : ℚ), (-35 / 16 : ℚ), (3 / 40 : ℚ)], ![(-3 / 40 : ℚ), (-127 / 80 : ℚ), 0, (-181 / 80 : ℚ), (-59 / 80 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-55 / 17 : ℚ), (-110 / 17 : ℚ), (-3 / 17 : ℚ), (-49 / 17 : ℚ), (-2 / 17 : ℚ)], ![(-6 / 17 : ℚ), (-55 / 17 : ℚ), 0, (-55 / 17 : ℚ), (-1 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 9 : ℚ), (-8 / 3 : ℚ), (-2 / 9 : ℚ), (-28 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, (-5 / 3 : ℚ), 0, (-32 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), (2 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-5 / 4 : ℚ), 0, (-5 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), (-12 / 5 : ℚ), (4 / 5 : ℚ)], ![0, (-7 / 5 : ℚ), 0, (-13 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), (-16 / 7 : ℚ), (-1 / 7 : ℚ), (-16 / 7 : ℚ), (-18 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-8 / 7 : ℚ), 0, (-17 / 7 : ℚ), (-9 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-4 / 3 : ℚ), 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-77 / 34 : ℚ), (-74 / 17 : ℚ), (-21 / 34 : ℚ), (26 / 17 : ℚ), 0], ![(-3 / 34 : ℚ), (-37 / 17 : ℚ), (-77 / 34 : ℚ), (-49 / 34 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-165 / 68 : ℚ), (-72 / 17 : ℚ), (-37 / 17 : ℚ), (69 / 34 : ℚ), 0], ![(-25 / 68 : ℚ), (-37 / 17 : ℚ), (-37 / 17 : ℚ), (-65 / 34 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), -5, (-5 / 4 : ℚ), (7 / 4 : ℚ), 0], ![0, (-5 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), (-14 / 3 : ℚ), (-5 / 2 : ℚ), (11 / 6 : ℚ), 0], ![0, (-5 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-5 / 4 : ℚ), -7], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-5 / 4 : ℚ), (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (-23 / 5 : ℚ)], ![(-1 / 10 : ℚ), (1 / 10 : ℚ), 0, (2 / 5 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-19 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, (3 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-43 / 20 : ℚ), (-21 / 5 : ℚ), (-7 / 20 : ℚ), (-7 / 20 : ℚ), 0], ![(-1 / 20 : ℚ), (-21 / 10 : ℚ), (-43 / 20 : ℚ), (-23 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, (-15 / 13 : ℚ), 0, (-60 / 13 : ℚ)], ![(-2 / 13 : ℚ), 0, (-28 / 13 : ℚ), (7 / 13 : ℚ), (-30 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (1 / 6 : ℚ), (-4 / 3 : ℚ), 0, (-31 / 12 : ℚ)], ![0, 0, (-5 / 2 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 41 : ℚ), (6 / 41 : ℚ), (-51 / 41 : ℚ), 0, (-188 / 41 : ℚ)], ![(-6 / 41 : ℚ), 0, (-96 / 41 : ℚ), (30 / 41 : ℚ), (-185 / 41 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 16 : ℚ), 0, (-21 / 16 : ℚ), (-3 / 16 : ℚ), (-17 / 4 : ℚ)], ![0, 0, (-35 / 16 : ℚ), 0, (-17 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-31 / 12 : ℚ)], ![0, 0, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 13 : ℚ), (4 / 13 : ℚ), (-25 / 13 : ℚ), (-9 / 13 : ℚ), (-68 / 13 : ℚ)], ![0, 0, (-38 / 13 : ℚ), 0, (-66 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-13 / 12 : ℚ), (1 / 12 : ℚ), (-13 / 3 : ℚ)], ![(-1 / 12 : ℚ), 0, (-25 / 12 : ℚ), (5 / 6 : ℚ), (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 5 : ℚ), (1 / 5 : ℚ), (-27 / 10 : ℚ)], ![0, 0, (-13 / 5 : ℚ), 1, 0]] }
]

theorem conicDetC32B_checked : conicDetC32B.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
