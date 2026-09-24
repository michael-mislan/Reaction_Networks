import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC33 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-93 / 80 : ℚ), (-21 / 10 : ℚ), (-3 / 80 : ℚ), (3 / 40 : ℚ), (-17 / 8 : ℚ)], ![(-3 / 40 : ℚ), (-87 / 80 : ℚ), 0, (-19 / 80 : ℚ), (-167 / 80 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 34 : ℚ), 0, (-29 / 17 : ℚ), (15 / 34 : ℚ), (-74 / 17 : ℚ)], ![(-3 / 34 : ℚ), 0, (-113 / 34 : ℚ), (6 / 17 : ℚ), (-37 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 17 : ℚ), (4 / 17 : ℚ), (-25 / 17 : ℚ), (-4 / 17 : ℚ), (-48 / 17 : ℚ)], ![0, 0, (-46 / 17 : ℚ), (-8 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), (-15 / 7 : ℚ), (-1 / 14 : ℚ), (5 / 14 : ℚ), (-15 / 7 : ℚ)], ![(-1 / 14 : ℚ), (-15 / 14 : ℚ), 0, (-2 / 7 : ℚ), (-15 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-11 / 5 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (-6 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 3 : ℚ), (-17 / 8 : ℚ)], ![(-1 / 12 : ℚ), (-9 / 8 : ℚ), 0, (-1 / 4 : ℚ), (-25 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, (-3 / 8 : ℚ), (-3 / 8 : ℚ), (-9 / 2 : ℚ)], ![0, 0, (-5 / 4 : ℚ), 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-9 / 4 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), (-1 / 8 : ℚ)], ![0, (-5 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-19 / 8 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), -2], ![0, (-5 / 4 : ℚ), 0, 0, (-31 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), (-44 / 9 : ℚ), 0, 0, 0], ![(-2 / 9 : ℚ), (-22 / 9 : ℚ), (1 / 9 : ℚ), (-17 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-25 / 12 : ℚ), 0, 0, (-1 / 12 : ℚ)], ![0, (-7 / 6 : ℚ), 0, (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-33 / 13 : ℚ), (-64 / 13 : ℚ), 0, 0, 0], ![(-4 / 13 : ℚ), (-34 / 13 : ℚ), (2 / 13 : ℚ), (-24 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 5 : ℚ), (-17 / 5 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), -1], ![(-1 / 10 : ℚ), (-17 / 10 : ℚ), 0, (-13 / 10 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-5 / 2 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-16 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ), 0], ![(-2 / 13 : ℚ), (-30 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ), (9 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0], ![0, 0, (-12 / 5 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-3 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (9 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-18 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ), (-51 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 11 : ℚ), (-25 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-12 / 5 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-18 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ), (-95 / 22 : ℚ)], ![(-1 / 11 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 11 : ℚ), (-47 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-7 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 2 : ℚ)], ![0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-80 / 13 : ℚ)], ![(-8 / 13 : ℚ), (-21 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-76 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 15 : ℚ), (2 / 15 : ℚ), 0, (-74 / 15 : ℚ)], ![(-2 / 15 : ℚ), (-2 / 15 : ℚ), (-2 / 15 : ℚ), (11 / 15 : ℚ), (-12 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 23 : ℚ), (4 / 23 : ℚ), 0, (-106 / 23 : ℚ)], ![(-4 / 23 : ℚ), (-4 / 23 : ℚ), (-4 / 23 : ℚ), (15 / 23 : ℚ), (-104 / 23 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-19 / 4 : ℚ), (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-30 / 13 : ℚ), (8 / 13 : ℚ), (8 / 13 : ℚ), (20 / 13 : ℚ), (-4 / 13 : ℚ)], ![0, (-68 / 13 : ℚ), (-38 / 13 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (1 / 12 : ℚ), (-7 / 4 : ℚ), (-59 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-7 / 6 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), (-21 / 5 : ℚ)], ![0, (-13 / 5 : ℚ), (-7 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (1 / 12 : ℚ), (-7 / 4 : ℚ), (-103 / 24 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-7 / 6 : ℚ), (-17 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (-58 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (9 / 11 : ℚ), (-28 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 17 : ℚ), (4 / 17 : ℚ), (4 / 17 : ℚ), (-82 / 17 : ℚ)], ![(-4 / 17 : ℚ), (-4 / 17 : ℚ), (-4 / 17 : ℚ), (13 / 17 : ℚ), (-80 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (1 / 12 : ℚ), (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-10 / 3 : ℚ), (-17 / 12 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (13 / 4 : ℚ), (1 / 6 : ℚ), 0, (-7 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 6 : ℚ), -2, 0, (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, (1 / 8 : ℚ), (-9 / 8 : ℚ), (1 / 2 : ℚ)], ![(-1 / 8 : ℚ), 0, (-19 / 8 : ℚ), (-9 / 4 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (2 / 5 : ℚ), (-7 / 5 : ℚ), 0], ![0, 0, (-14 / 5 : ℚ), (-14 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (1 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-13 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 10 : ℚ), (1 / 10 : ℚ), 0, (1 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 5 : ℚ), (-1 / 10 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 6 : ℚ), (1 / 6 : ℚ), 0, (-31 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (2 / 5 : ℚ), (-7 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, (-14 / 5 : ℚ), (-14 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 6 : ℚ), (-10 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, 0, (-11 / 10 : ℚ)], ![(-1 / 20 : ℚ), (-41 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (23 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![0, (-7 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-13 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -7], ![(-3 / 7 : ℚ), (-17 / 7 : ℚ), (-3 / 7 : ℚ), (-3 / 7 : ℚ), (-23 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![0, (-26 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -6], ![(-4 / 7 : ℚ), (-18 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-40 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), (1 / 24 : ℚ), 0, (5 / 4 : ℚ), (-1 / 24 : ℚ)], ![(-1 / 24 : ℚ), (-103 / 24 : ℚ), (-17 / 4 : ℚ), (-29 / 24 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-82 / 35 : ℚ), (8 / 35 : ℚ), (-32 / 35 : ℚ), (71 / 35 : ℚ), (-4 / 35 : ℚ)], ![(-8 / 35 : ℚ), (-172 / 35 : ℚ), (-164 / 35 : ℚ), (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 9 : ℚ), (4 / 9 : ℚ), 0, (8 / 9 : ℚ), (-4 / 9 : ℚ)], ![0, (-16 / 3 : ℚ), (-16 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 5 : ℚ), (2 / 5 : ℚ), (-6 / 5 : ℚ), (3 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-24 / 5 : ℚ), (-24 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 11 : ℚ), (1 / 11 : ℚ), (-25 / 22 : ℚ), (-15 / 44 : ℚ), (-125 / 44 : ℚ)], ![(-1 / 11 : ℚ), (-27 / 11 : ℚ), (-26 / 11 : ℚ), 0, (-12 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 20 : ℚ), (1 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-81 / 20 : ℚ)], ![0, (-43 / 20 : ℚ), (-43 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 11 : ℚ), (1 / 11 : ℚ), (-25 / 22 : ℚ), (-15 / 44 : ℚ), (-43 / 22 : ℚ)], ![(-1 / 11 : ℚ), (-27 / 11 : ℚ), (-26 / 11 : ℚ), 0, (-21 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), 0, (2 / 11 : ℚ), (-58 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (9 / 11 : ℚ), (-28 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 17 : ℚ), 0, (4 / 17 : ℚ), (-82 / 17 : ℚ)], ![(-4 / 17 : ℚ), (-4 / 17 : ℚ), (-4 / 17 : ℚ), (13 / 17 : ℚ), (-80 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (5 / 6 : ℚ), 0, (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-55 / 12 : ℚ), (-9 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 2, (-7 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![(-1 / 3 : ℚ), (-16 / 3 : ℚ), -5, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, 0, -2, (1 / 2 : ℚ)], ![(-1 / 8 : ℚ), 0, -4, -2, (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, 0, -2, (1 / 3 : ℚ)], ![0, 0, -4, -2, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), -2, 0, 0, (-17 / 12 : ℚ)], ![(-1 / 6 : ℚ), -4, 0, 0, (-17 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, (-4 / 5 : ℚ), (1 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-12 / 5 : ℚ), (-8 / 5 : ℚ), (-4 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), -2, 0, 0, (-60 / 11 : ℚ)], ![(-2 / 11 : ℚ), -4, 0, 0, (-29 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, 0, -2, (-1 / 6 : ℚ)], ![0, 0, -4, -2, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), -2, 0, 0, (-20 / 3 : ℚ)], ![(-2 / 3 : ℚ), -4, 0, 0, (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-6 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (13 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, (-9 / 4 : ℚ), (3 / 4 : ℚ)], ![0, 0, (-19 / 4 : ℚ), (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -6], ![(-2 / 7 : ℚ), (-16 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, 0, -6, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-26 / 9 : ℚ), (-8 / 9 : ℚ), 0, (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (1 / 6 : ℚ), (-4 / 3 : ℚ), 2, (-1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-31 / 6 : ℚ), (-5 / 2 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 17 : ℚ), (4 / 17 : ℚ), (-40 / 17 : ℚ), (35 / 17 : ℚ), 0], ![(-4 / 17 : ℚ), (-84 / 17 : ℚ), (-40 / 17 : ℚ), (-31 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), (1 / 10 : ℚ), (-3 / 5 : ℚ), (3 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (-43 / 10 : ℚ), (-11 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), (4 / 3 : ℚ), -3, (5 / 3 : ℚ), 0], ![0, (-16 / 3 : ℚ), -3, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (1 / 8 : ℚ), (-5 / 4 : ℚ), 0, (-13 / 4 : ℚ)], ![(-1 / 8 : ℚ), (-21 / 8 : ℚ), (-5 / 4 : ℚ), 0, (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (2 / 3 : ℚ), (-5 / 3 : ℚ), 0, (-13 / 3 : ℚ)], ![0, -3, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 7 : ℚ), (2 / 7 : ℚ), (-11 / 7 : ℚ), 0, (-12 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-24 / 7 : ℚ), (-11 / 7 : ℚ), 0, (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), 0, (2 / 11 : ℚ), (-58 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (9 / 11 : ℚ), (-28 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-19 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (3 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (5 / 6 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-55 / 12 : ℚ), (-9 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), 2, (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0], ![(-4 / 9 : ℚ), (-52 / 9 : ℚ), (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ)], ![0, 0, (-7 / 3 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)], ![0, 0, (-8 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-29 / 26 : ℚ), (1 / 13 : ℚ), 0, (1 / 13 : ℚ)], ![(-1 / 13 : ℚ), (-28 / 13 : ℚ), (-1 / 13 : ℚ), (9 / 26 : ℚ), (9 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ), (2 / 3 : ℚ), (-17 / 6 : ℚ)], ![(-1 / 6 : ℚ), 0, (-5 / 2 : ℚ), (-1 / 2 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ), (5 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, 0, (-7 / 3 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 9 : ℚ), (2 / 9 : ℚ), (-1 / 3 : ℚ), (-43 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-22 / 9 : ℚ), (-2 / 9 : ℚ), (5 / 9 : ℚ), (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (-20 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 20 : ℚ), (-1 / 20 : ℚ), (1 / 10 : ℚ), (1 / 4 : ℚ), (1 / 10 : ℚ)], ![0, 0, (-11 / 5 : ℚ), 0, (-3 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), 0, (-8 / 3 : ℚ)], ![0, 0, (-8 / 3 : ℚ), 0, (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), 0, (-1 / 6 : ℚ)], ![0, 0, (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), 0, (-13 / 6 : ℚ)], ![0, 0, (-8 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), (1 / 3 : ℚ), 0, -1], ![0, (-7 / 3 : ℚ), (-1 / 3 : ℚ), 1, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 9 : ℚ), (-1 / 18 : ℚ), (1 / 9 : ℚ), (-2 / 9 : ℚ), (-10 / 3 : ℚ)], ![(-1 / 9 : ℚ), 0, (-7 / 3 : ℚ), (-1 / 9 : ℚ), (-11 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-30 / 7 : ℚ)], ![0, 0, (-20 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 9 : ℚ), (1 / 18 : ℚ), (-7 / 6 : ℚ), (-151 / 36 : ℚ)], ![(-1 / 18 : ℚ), (-19 / 9 : ℚ), (-1 / 18 : ℚ), (-10 / 9 : ℚ), (-25 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-18 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ), (-51 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (10 / 11 : ℚ), (-25 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-12 / 5 : ℚ), (-3 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-18 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ), (-95 / 22 : ℚ)], ![(-1 / 11 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (10 / 11 : ℚ), (-47 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), (-8 / 3 : ℚ), (-8 / 3 : ℚ)], ![0, 0, (-8 / 3 : ℚ), 0, (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-12 / 7 : ℚ), (1 / 7 : ℚ), -5, (-9 / 2 : ℚ)], ![(-1 / 7 : ℚ), (-16 / 7 : ℚ), (-1 / 7 : ℚ), (-17 / 7 : ℚ), (-31 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, 0, (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), (-13 / 6 : ℚ), (-13 / 6 : ℚ)], ![0, 0, (-8 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-12 / 7 : ℚ), (1 / 7 : ℚ), (-9 / 2 : ℚ), (-17 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-16 / 7 : ℚ), (-1 / 7 : ℚ), (-31 / 7 : ℚ), (-16 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), 1, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 5 : ℚ), 0], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 0, 0], ![(-1 / 3 : ℚ), -1, -4, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 13 : ℚ), (-59 / 13 : ℚ)], ![(-1 / 13 : ℚ), (-14 / 13 : ℚ), (-1 / 13 : ℚ), (9 / 26 : ℚ), (-29 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-19 / 8 : ℚ)], ![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), (-47 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, -3, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), 0, (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 2 : ℚ), 0, 0, -2, 2], ![0, -3, 0, 0, 2]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), -6], ![0, (-5 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, 0, (-1 / 2 : ℚ)], ![0, 0, (-7 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), -5], ![0, (-5 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), 1, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, 0, 0, 0], ![(-1 / 6 : ℚ), -1, -4, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), (-25 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ), (-13 / 3 : ℚ)], ![0, 0, -3, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), (-39 / 8 : ℚ)], ![(-1 / 4 : ℚ), (-37 / 16 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-17 / 13 : ℚ), (-4 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-5 / 3 : ℚ), (-27 / 8 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, 0, (-23 / 6 : ℚ)], ![(-1 / 9 : ℚ), (-10 / 9 : ℚ), (-37 / 9 : ℚ), 0, (-23 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-124 / 17 : ℚ), (-96 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-25 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ), (-92 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-23 / 4 : ℚ), (-7 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-11 / 2 : ℚ), -3]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (1 / 4 : ℚ), (7 / 4 : ℚ), (7 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-19 / 4 : ℚ), (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 12 : ℚ), (1 / 6 : ℚ), (17 / 12 : ℚ), (17 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, (-13 / 3 : ℚ), (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (1 / 2 : ℚ), 0, 0, -4], ![0, (-5 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (2 / 3 : ℚ), 0, 0, -4], ![0, (-8 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (2 / 3 : ℚ), 0, 0, (-10 / 3 : ℚ)], ![0, (-8 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 15 : ℚ), 0, (2 / 15 : ℚ), (-74 / 15 : ℚ)], ![(-2 / 15 : ℚ), (-2 / 15 : ℚ), (11 / 15 : ℚ), (3 / 5 : ℚ), (-12 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 23 : ℚ), 0, (4 / 23 : ℚ), (-106 / 23 : ℚ)], ![(-4 / 23 : ℚ), (-4 / 23 : ℚ), (15 / 23 : ℚ), (13 / 23 : ℚ), (-104 / 23 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (5 / 6 : ℚ), (3 / 2 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-55 / 12 : ℚ), (-17 / 12 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 17 : ℚ), 2, (35 / 17 : ℚ), (-23 / 17 : ℚ), 0], ![(-4 / 17 : ℚ), (-84 / 17 : ℚ), (-31 / 17 : ℚ), (-23 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), (1 / 3 : ℚ), 2, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, -5, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-55 / 24 : ℚ), (1 / 6 : ℚ), (43 / 24 : ℚ), (-7 / 12 : ℚ), 0], ![(-1 / 6 : ℚ), (-19 / 4 : ℚ), (-13 / 8 : ℚ), (-5 / 24 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-42 / 19 : ℚ), (8 / 19 : ℚ), (39 / 19 : ℚ), (-4 / 19 : ℚ), (-4 / 19 : ℚ)], ![0, (-92 / 19 : ℚ), (-31 / 19 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 11 : ℚ), (2 / 11 : ℚ), (20 / 11 : ℚ), (-1 / 11 : ℚ), (-3 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-52 / 11 : ℚ), (-18 / 11 : ℚ), 0, (-1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), -3], ![0, (-20 / 7 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-30 / 7 : ℚ)], ![0, (-20 / 7 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-13 / 7 : ℚ)], ![0, (-20 / 7 : ℚ), 0, 0, (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), (1 / 8 : ℚ), (11 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ)], ![0, (-35 / 8 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 13 : ℚ), (4 / 13 : ℚ), (23 / 13 : ℚ), (4 / 13 : ℚ), (-2 / 13 : ℚ)], ![0, (-60 / 13 : ℚ), 0, (-19 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 20 : ℚ), (1 / 2 : ℚ), (23 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ)], ![0, (-83 / 20 : ℚ), 0, (-11 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), (8 / 3 : ℚ), (11 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![0, (-14 / 3 : ℚ), 0, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), (2 / 3 : ℚ), (4 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, -6, 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), (1 / 3 : ℚ), (2 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, -5, 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (1 / 2 : ℚ), (3 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, -5, 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-18 / 7 : ℚ), (4 / 7 : ℚ), (8 / 7 : ℚ), (2 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, (-40 / 7 : ℚ), 0, (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, -1, (-17 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), 1, -1, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (2 / 3 : ℚ), 0, 0, -4], ![0, (-8 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), 0, -1, (-16 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 1, -1, (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (3 / 2 : ℚ), 0, 0, (-10 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-5 / 2 : ℚ), 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (3 / 2 : ℚ), 0, 0, -4], ![0, (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-7 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-30 / 7 : ℚ), -3], ![0, (-20 / 7 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), (2 / 9 : ℚ), (-2 / 9 : ℚ), (-29 / 9 : ℚ), (-17 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-28 / 9 : ℚ), 0, (-11 / 9 : ℚ), (-16 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-30 / 7 : ℚ), (-16 / 7 : ℚ)], ![0, (-20 / 7 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-30 / 7 : ℚ), (-13 / 7 : ℚ)], ![0, (-20 / 7 : ℚ), 0, 0, (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), (2 / 9 : ℚ), (-2 / 9 : ℚ), (-17 / 9 : ℚ), (-11 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-28 / 9 : ℚ), 0, (-16 / 9 : ℚ), -1]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (17 / 6 : ℚ), (1 / 12 : ℚ), (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (3 / 8 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ), (-19 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-23 / 8 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, (-34 / 7 : ℚ), (-11 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 11 : ℚ), (1 / 11 : ℚ), (-51 / 11 : ℚ), (-95 / 22 : ℚ)], ![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (9 / 22 : ℚ), (-25 / 11 : ℚ), (-47 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 13 : ℚ), (4 / 13 : ℚ), (4 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ)], ![0, (-60 / 13 : ℚ), (-19 / 13 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (1 / 12 : ℚ), (-67 / 12 : ℚ), (-9 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (11 / 12 : ℚ), (-17 / 4 : ℚ), (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 20 : ℚ), (1 / 2 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ)], ![0, (-83 / 20 : ℚ), (-11 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), 2, (-13 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-47 / 10 : ℚ), (-13 / 10 : ℚ), 0, (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-20 / 9 : ℚ), (26 / 9 : ℚ), (-5 / 3 : ℚ), (-2 / 9 : ℚ), 0], ![0, (-44 / 9 : ℚ), (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 2, (-3 / 2 : ℚ), 0, (-1 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-16 / 3 : ℚ), (-3 / 2 : ℚ), 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, (-9 / 4 : ℚ), (-9 / 4 : ℚ), (1 / 2 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 2 : ℚ), (-19 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 9 : ℚ), 0, (-22 / 9 : ℚ), (-22 / 9 : ℚ), (8 / 9 : ℚ)], ![0, 0, (-44 / 9 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-17 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-5 / 4 : ℚ)], ![(-3 / 8 : ℚ), (-17 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), 0, (-11 / 5 : ℚ), (-11 / 5 : ℚ), (1 / 10 : ℚ)], ![(-1 / 10 : ℚ), 0, (-22 / 5 : ℚ), (-23 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, (-9 / 4 : ℚ), (-9 / 4 : ℚ), (-21 / 8 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 2 : ℚ), (-19 / 8 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 15 : ℚ), 0, (-46 / 15 : ℚ), (-46 / 15 : ℚ), (-4 / 15 : ℚ)], ![0, 0, (-92 / 15 : ℚ), (-18 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-8 / 3 : ℚ), (-2 / 3 : ℚ), 0, -6], ![-2, (-16 / 3 : ℚ), (-4 / 3 : ℚ), 0, -6]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (-13 / 6 : ℚ), (1 / 3 : ℚ)], ![(-1 / 12 : ℚ), 0, (-55 / 12 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 5 : ℚ), (-13 / 5 : ℚ), (-12 / 5 : ℚ), (4 / 5 : ℚ)], ![0, 0, (-27 / 5 : ℚ), (-13 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-13 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-1 / 8 : ℚ), (-19 / 8 : ℚ), (-9 / 4 : ℚ), (-21 / 8 : ℚ)], ![(-1 / 8 : ℚ), 0, (-39 / 8 : ℚ), (-19 / 8 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 5 : ℚ), (-13 / 5 : ℚ), (-12 / 5 : ℚ), (-11 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-27 / 5 : ℚ), (-12 / 5 : ℚ), (-11 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, (-4 / 3 : ℚ), 2, (-1 / 6 : ℚ)], ![(-1 / 6 : ℚ), -5, (-5 / 2 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 17 : ℚ), (-7 / 17 : ℚ), (-37 / 17 : ℚ), (26 / 17 : ℚ), 0], ![(-2 / 17 : ℚ), (-74 / 17 : ℚ), (-37 / 17 : ℚ), (-24 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), 0, (-3 / 5 : ℚ), (3 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (-43 / 10 : ℚ), (-11 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 6 : ℚ), (-5 / 6 : ℚ), (-5 / 2 : ℚ), (5 / 6 : ℚ), 0], ![0, (-14 / 3 : ℚ), (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-5 / 16 : ℚ), (-9 / 8 : ℚ), 0, (-25 / 8 : ℚ)], ![(-1 / 16 : ℚ), (-9 / 4 : ℚ), (-9 / 8 : ℚ), 0, (-17 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-1 / 2 : ℚ), (-5 / 4 : ℚ), 0, (-33 / 8 : ℚ)], ![0, (-19 / 8 : ℚ), (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-5 / 8 : ℚ), (-5 / 4 : ℚ), 0, (-15 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-5 / 2 : ℚ), (-5 / 4 : ℚ), 0, (-15 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 11 : ℚ), 0, (-16 / 11 : ℚ), (2 / 11 : ℚ), (-2 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-56 / 11 : ℚ), (-28 / 11 : ℚ), (-19 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 4 : ℚ), (-19 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (3 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-9 / 2 : ℚ), (-9 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-7 / 6 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(-1 / 3 : ℚ), -5, (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, (-4 / 3 : ℚ), (5 / 6 : ℚ), (5 / 6 : ℚ)], ![0, 0, (-8 / 3 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, (-4 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)], ![0, 0, (-8 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 20 : ℚ), 0, (-21 / 20 : ℚ), (1 / 5 : ℚ), (1 / 20 : ℚ)], ![(-1 / 20 : ℚ), 0, (-21 / 10 : ℚ), (-3 / 20 : ℚ), (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, -3, 1, -1], ![(-1 / 3 : ℚ), 0, -6, -1, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), (-1 / 4 : ℚ), (-5 / 6 : ℚ), (1 / 12 : ℚ), (-35 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 2 : ℚ), (-5 / 3 : ℚ), 0, (-17 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-3 / 10 : ℚ), (-9 / 10 : ℚ), (1 / 5 : ℚ), (-7 / 10 : ℚ)], ![0, (-3 / 5 : ℚ), (-9 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 35 : ℚ), (-24 / 35 : ℚ), (-19 / 35 : ℚ), (8 / 35 : ℚ), (-26 / 7 : ℚ)], ![(-8 / 35 : ℚ), (-48 / 35 : ℚ), (-38 / 35 : ℚ), 0, (-18 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 9 : ℚ), 0, (-4 / 3 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, 0, (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 9 : ℚ), 0, (-11 / 9 : ℚ), (5 / 9 : ℚ), (2 / 9 : ℚ)], ![0, 0, (-22 / 9 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, -3, 1, -1], ![0, 0, -6, 0, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, (-10 / 3 : ℚ)], ![0, 0, (-10 / 3 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![0, 0, (-10 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, (-7 / 3 : ℚ)], ![0, 0, (-10 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), 0, -1], ![0, (-8 / 3 : ℚ), (-2 / 3 : ℚ), 1, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), 0, -3, 1, -1], ![(-1 / 2 : ℚ), 0, -6, 1, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-1 / 5 : ℚ), (-16 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-14 / 5 : ℚ), 0, (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 9 : ℚ), 0, (-4 / 3 : ℚ), (-2 / 9 : ℚ), (-38 / 9 : ℚ)], ![0, 0, (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-2 / 5 : ℚ), (-23 / 10 : ℚ)], ![(-1 / 5 : ℚ), 0, (-12 / 5 : ℚ), (-1 / 5 : ℚ), (-11 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, -3, 0, -1], ![(-1 / 2 : ℚ), 0, -6, -1, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-20 / 17 : ℚ), 0, (4 / 17 : ℚ), (-89 / 17 : ℚ)], ![(-3 / 17 : ℚ), (-40 / 17 : ℚ), 0, (14 / 17 : ℚ), (-43 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 18 : ℚ), 0, (-10 / 9 : ℚ), (1 / 9 : ℚ), (-1 / 18 : ℚ)], ![0, 0, (-20 / 9 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), 0, (-11 / 10 : ℚ), (1 / 10 : ℚ), (-43 / 20 : ℚ)], ![(-1 / 10 : ℚ), 0, (-11 / 5 : ℚ), (-1 / 5 : ℚ), (-21 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 8 : ℚ), 0, (-77 / 24 : ℚ), (-13 / 12 : ℚ), (-37 / 24 : ℚ)], ![(-1 / 24 : ℚ), 0, (-77 / 12 : ℚ), (-9 / 8 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 15 : ℚ), 0, (-53 / 15 : ℚ), (-23 / 15 : ℚ), (-2 / 15 : ℚ)], ![0, 0, (-106 / 15 : ℚ), (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-19 / 6 : ℚ), (-13 / 12 : ℚ), (-19 / 12 : ℚ)], ![(-1 / 12 : ℚ), 0, (-19 / 3 : ℚ), (-13 / 12 : ℚ), (-19 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), 0, (-9 / 5 : ℚ), (-18 / 5 : ℚ), (-18 / 5 : ℚ)], ![0, 0, (-18 / 5 : ℚ), 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-13 / 4 : ℚ), (-19 / 8 : ℚ)], ![(-1 / 4 : ℚ), 0, (-5 / 2 : ℚ), (-3 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, -3, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-9 / 4 : ℚ), (-9 / 4 : ℚ)], ![0, 0, -3, 0, -2]] },
  { network := { reaction := ![(.x, .xy), (.y, .xx), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-23 / 10 : ℚ), (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-12 / 5 : ℚ), (-11 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 13 : ℚ), (-2 / 13 : ℚ), (-32 / 13 : ℚ), (9 / 13 : ℚ), (8 / 13 : ℚ)], ![0, 0, (-66 / 13 : ℚ), (-4 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 7 : ℚ), (-1 / 7 : ℚ), (-17 / 7 : ℚ), (5 / 7 : ℚ), (5 / 7 : ℚ)], ![0, 0, -5, (-5 / 7 : ℚ), (5 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, (-6 / 5 : ℚ), 0], ![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (13 / 10 : ℚ), (13 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, (-13 / 12 : ℚ), (13 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-25 / 12 : ℚ), -1, (13 / 12 : ℚ), (13 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(24 / 19 : ℚ), (-3 / 19 : ℚ), 0, (-34 / 19 : ℚ), (-145 / 19 : ℚ)], ![(-3 / 19 : ℚ), (-47 / 19 : ℚ), (-3 / 19 : ℚ), (37 / 19 : ℚ), (-71 / 19 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (1 / 3 : ℚ), (-17 / 8 : ℚ)], ![(-1 / 12 : ℚ), 0, (-55 / 12 : ℚ), (-1 / 4 : ℚ), (-25 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)], ![0, 0, (-55 / 12 : ℚ), 0, (7 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (-9 / 4 : ℚ), (3 / 4 : ℚ), 0], ![0, 0, (-19 / 4 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-7 / 3 : ℚ), 1, -1], ![0, 0, (-17 / 3 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 5 : ℚ), (-13 / 5 : ℚ), (4 / 5 : ℚ), (-11 / 5 : ℚ)], ![0, 0, (-27 / 5 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 5 : ℚ), (-13 / 5 : ℚ), (4 / 5 : ℚ), (-19 / 10 : ℚ)], ![0, 0, (-27 / 5 : ℚ), 0, (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, 0, (-5 / 4 : ℚ)], ![0, (-17 / 8 : ℚ), (-1 / 8 : ℚ), (5 / 4 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (7 / 6 : ℚ), (-7 / 6 : ℚ)], ![(-1 / 6 : ℚ), 0, (-17 / 3 : ℚ), (7 / 6 : ℚ), (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (1 / 2 : ℚ), (-23 / 12 : ℚ)], ![(-1 / 12 : ℚ), 0, (-55 / 12 : ℚ), (7 / 12 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-1 / 27 : ℚ), (-19 / 9 : ℚ), (2 / 9 : ℚ), (-79 / 54 : ℚ)], ![(-1 / 27 : ℚ), 0, (-115 / 27 : ℚ), (7 / 27 : ℚ), (-13 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-30 / 13 : ℚ), (-4 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 24 : ℚ), (-1 / 24 : ℚ), (-17 / 8 : ℚ), (-13 / 12 : ℚ), (-41 / 24 : ℚ)], ![(-1 / 24 : ℚ), 0, (-21 / 4 : ℚ), (-13 / 12 : ℚ), (-41 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.y, .xy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, (-17 / 3 : ℚ), -3], ![(-1 / 3 : ℚ), -3, (-1 / 3 : ℚ), (-11 / 2 : ℚ), (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), 0, (11 / 8 : ℚ), (11 / 8 : ℚ), (-1 / 8 : ℚ)], ![0, (-35 / 8 : ℚ), (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 12 : ℚ), (-1 / 2 : ℚ), (17 / 12 : ℚ), (17 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, (-13 / 3 : ℚ), (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-1 / 4 : ℚ), 0, 0, (-13 / 4 : ℚ)], ![0, (-17 / 8 : ℚ), 0, 0, (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-1 / 2 : ℚ), 0, 0, -4], ![0, (-9 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-1 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![0, (-9 / 4 : ℚ), 0, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (2 / 15 : ℚ), (-74 / 15 : ℚ)], ![(-2 / 15 : ℚ), (-2 / 15 : ℚ), (11 / 15 : ℚ), (3 / 5 : ℚ), (-12 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-82 / 35 : ℚ), (-32 / 35 : ℚ), (71 / 35 : ℚ), (8 / 35 : ℚ), (-4 / 35 : ℚ)], ![(-8 / 35 : ℚ), (-164 / 35 : ℚ), (-9 / 5 : ℚ), (-11 / 7 : ℚ), 0]] }
]

theorem conicDetC33_checked : conicDetC33.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
