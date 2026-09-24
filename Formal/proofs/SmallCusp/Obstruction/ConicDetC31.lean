import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC31 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 9 : ℚ), 0, 0, (-20 / 3 : ℚ)], ![0, 0, (-17 / 9 : ℚ), (-8 / 9 : ℚ), (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, (4 / 3 : ℚ), 0, (-44 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (4 / 9 : ℚ), (10 / 9 : ℚ), (-44 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (1 / 5 : ℚ), 0, (-23 / 5 : ℚ)], ![0, 0, 0, (2 / 5 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-13 / 3 : ℚ), (1 / 2 : ℚ), (11 / 12 : ℚ), 0], ![(-9 / 4 : ℚ), (-9 / 4 : ℚ), (-25 / 6 : ℚ), (11 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-13 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 0], ![(-9 / 4 : ℚ), (-9 / 4 : ℚ), (-9 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-14 / 9 : ℚ), (4 / 9 : ℚ), 0, (-10 / 3 : ℚ)], ![-1, -1, -4, 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (-19 / 16 : ℚ), 0, (-3 / 16 : ℚ)], ![(-1 / 16 : ℚ), (-1 / 16 : ℚ), (-19 / 16 : ℚ), (-3 / 16 : ℚ), (5 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-43 / 20 : ℚ), 0, (-19 / 20 : ℚ), (1 / 4 : ℚ)], ![(-11 / 10 : ℚ), (-11 / 10 : ℚ), 0, (-21 / 10 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), (-5 / 4 : ℚ), 0, (-5 / 4 : ℚ)], ![0, 0, (-5 / 4 : ℚ), (-1 / 8 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), (-5 / 4 : ℚ), 0, (1 / 8 : ℚ)], ![0, 0, (-5 / 4 : ℚ), (-1 / 8 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 4 : ℚ), (-7 / 4 : ℚ), 0, (7 / 4 : ℚ)], ![0, 0, (-7 / 4 : ℚ), (-1 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 16 : ℚ), (-1 / 8 : ℚ), (-17 / 16 : ℚ), (5 / 16 : ℚ), (-19 / 8 : ℚ)], ![(-3 / 16 : ℚ), (-1 / 16 : ℚ), (-17 / 16 : ℚ), 0, (-19 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (-19 / 16 : ℚ), (3 / 16 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 16 : ℚ), (-1 / 16 : ℚ), (-19 / 16 : ℚ), 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-19 / 4 : ℚ)], ![0, 0, (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (-15 / 7 : ℚ), 0, (-9 / 7 : ℚ), (1 / 2 : ℚ)], ![(-10 / 7 : ℚ), (-8 / 7 : ℚ), 0, (-18 / 7 : ℚ), (-5 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 11 : ℚ), (-45 / 22 : ℚ), 0, (-12 / 11 : ℚ), (3 / 11 : ℚ)], ![(-25 / 22 : ℚ), (-23 / 22 : ℚ), 0, (-24 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-17 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 8 : ℚ)], ![(-9 / 8 : ℚ), (-9 / 8 : ℚ), 0, (-5 / 2 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-21 / 10 : ℚ), 0, (-6 / 5 : ℚ), (1 / 10 : ℚ)], ![(-13 / 10 : ℚ), (-11 / 10 : ℚ), 0, (-12 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-65 / 48 : ℚ), (-33 / 16 : ℚ), 0, (-19 / 16 : ℚ), (-1 / 16 : ℚ)], ![(-155 / 96 : ℚ), (-33 / 32 : ℚ), 0, (-19 / 8 : ℚ), (-1 / 32 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-17 / 8 : ℚ), 0, (-5 / 4 : ℚ), 0], ![(-11 / 8 : ℚ), (-9 / 8 : ℚ), 0, (-5 / 2 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-3, (-16 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ), 0], ![-3, -3, (2 / 3 : ℚ), (-22 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 12 : ℚ), (37 / 18 : ℚ), (-1 / 6 : ℚ), 0, (-11 / 6 : ℚ)], ![(11 / 12 : ℚ), (17 / 18 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), 2]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (11 / 12 : ℚ)], ![(-5 / 4 : ℚ), (-5 / 3 : ℚ), 0, (-55 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-23 / 10 : ℚ), (-1 / 10 : ℚ), (-9 / 5 : ℚ), 0], ![(-6 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 2 : ℚ), (-37 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(6 / 5 : ℚ), 2, (-1 / 5 : ℚ), 0, (-26 / 5 : ℚ)], ![1, 1, (-13 / 5 : ℚ), (-1 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 9 : ℚ), (-19 / 9 : ℚ), (-1 / 18 : ℚ), (-13 / 6 : ℚ), (-1 / 18 : ℚ)], ![(-7 / 6 : ℚ), (-17 / 9 : ℚ), 0, (-79 / 18 : ℚ), (1 / 18 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 8 : ℚ), (-9 / 2 : ℚ), (-1 / 4 : ℚ), (-29 / 8 : ℚ), 0], ![(-19 / 8 : ℚ), (-19 / 8 : ℚ), (7 / 8 : ℚ), (-15 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 9 : ℚ), 0, (-5 / 18 : ℚ), (-14 / 3 : ℚ)], ![0, 0, (-2 / 9 : ℚ), (1 / 2 : ℚ), (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-35 / 16 : ℚ), (-17 / 4 : ℚ), (-29 / 16 : ℚ), (25 / 16 : ℚ), 0], ![(-35 / 16 : ℚ), (-35 / 16 : ℚ), (-33 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-1 / 8 : ℚ), (-11 / 8 : ℚ), (-9 / 2 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 2 : ℚ), (-11 / 8 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-14 / 3 : ℚ), 0, (1 / 3 : ℚ), 0], ![(-5 / 2 : ℚ), (-5 / 2 : ℚ), (-43 / 12 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-5 / 6 : ℚ), 0, 0, (-7 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-13 / 6 : ℚ), 0, (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 12 : ℚ), (-11 / 12 : ℚ), (-1 / 4 : ℚ), (1 / 12 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-11 / 12 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-13 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-13 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-19 / 8 : ℚ), 0, (-5 / 4 : ℚ), (1 / 8 : ℚ)], ![(-5 / 4 : ℚ), (-5 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-7 / 2 : ℚ)], ![0, (1 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, (-10 / 7 : ℚ), (-1 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-10 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-269 / 192 : ℚ), (-15 / 4 : ℚ), (-3 / 64 : ℚ), (-143 / 64 : ℚ), (63 / 64 : ℚ)], ![(-319 / 192 : ℚ), (-123 / 64 : ℚ), 0, (-149 / 64 : ℚ), (-57 / 64 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 11 : ℚ), (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-16 / 11 : ℚ), 0], ![(-7 / 11 : ℚ), (-5 / 11 : ℚ), -2, (-18 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-73 / 58 : ℚ), (-62 / 29 : ℚ), (-3 / 58 : ℚ), (-131 / 58 : ℚ), (14 / 29 : ℚ)], ![(-79 / 58 : ℚ), (-65 / 58 : ℚ), 0, (-137 / 58 : ℚ), (7 / 58 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 17 : ℚ), (1 / 2 : ℚ), (-37 / 17 : ℚ), (3 / 68 : ℚ), (-147 / 34 : ℚ)], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-293 / 68 : ℚ), 0, (-147 / 68 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 9 : ℚ), (-62 / 27 : ℚ), (-1 / 9 : ℚ), (-23 / 9 : ℚ), 0], ![(-16 / 9 : ℚ), (-34 / 27 : ℚ), 0, (-25 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (31 / 66 : ℚ), (-1 / 22 : ℚ), 0, (-13 / 11 : ℚ)], ![(9 / 44 : ℚ), (7 / 33 : ℚ), (-23 / 11 : ℚ), (-1 / 22 : ℚ), (27 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-39 / 16 : ℚ), (-1 / 16 : ℚ), (-17 / 8 : ℚ), (7 / 16 : ℚ)], ![(-19 / 16 : ℚ), (-5 / 4 : ℚ), 0, (-35 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, (19 / 10 : ℚ), (-1 / 20 : ℚ), 0, (-57 / 10 : ℚ)], ![(19 / 20 : ℚ), (19 / 20 : ℚ), (-21 / 10 : ℚ), (-1 / 20 : ℚ), (-57 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), (-22 / 9 : ℚ), (-2 / 9 : ℚ), (-22 / 9 : ℚ), (-2 / 9 : ℚ)], ![(-5 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-8 / 3 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-14 / 9 : ℚ), -1, (4 / 9 : ℚ), (-10 / 3 : ℚ)], ![-1, -1, -1, 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-19 / 4 : ℚ)], ![0, 0, 0, (1 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (1 / 3 : ℚ), (-14 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (5 / 6 : ℚ), (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (-1 / 2 : ℚ), (-7 / 8 : ℚ), (1 / 8 : ℚ), -2], ![(-3 / 8 : ℚ), (-1 / 4 : ℚ), (-7 / 8 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 7 : ℚ), (-20 / 7 : ℚ), 0, (8 / 7 : ℚ), 0], ![(-11 / 7 : ℚ), (-11 / 7 : ℚ), 0, (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 2 : ℚ), -1, 0, (-23 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), -1, (1 / 6 : ℚ), (-23 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-9 / 4 : ℚ), 0, (1 / 2 : ℚ), (-1 / 4 : ℚ)], ![(-5 / 4 : ℚ), (-9 / 8 : ℚ), 0, (1 / 8 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), 0, (-23 / 20 : ℚ), (-3 / 20 : ℚ), (-23 / 10 : ℚ)], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (-23 / 20 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), (-22 / 5 : ℚ), (9 / 10 : ℚ), (19 / 10 : ℚ), 0], ![(-23 / 10 : ℚ), (-23 / 10 : ℚ), (9 / 10 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 8 : ℚ), (-5 / 2 : ℚ), (1 / 8 : ℚ), (3 / 8 : ℚ), 0], ![(-11 / 8 : ℚ), (-5 / 4 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (-19 / 16 : ℚ), (1 / 8 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 16 : ℚ), (-1 / 16 : ℚ), (-19 / 16 : ℚ), (7 / 16 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 8 : ℚ), (-9 / 2 : ℚ), (7 / 8 : ℚ), (1 / 2 : ℚ), 0], ![(-19 / 8 : ℚ), (-19 / 8 : ℚ), (7 / 8 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0, -3], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 7 : ℚ), (-20 / 7 : ℚ), 0, (-4 / 7 : ℚ), 0], ![(-11 / 7 : ℚ), (-11 / 7 : ℚ), 0, (-4 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-43 / 34 : ℚ), (-37 / 17 : ℚ), 0, (12 / 17 : ℚ), (-16 / 17 : ℚ)], ![(-23 / 17 : ℚ), (-37 / 34 : ℚ), (3 / 34 : ℚ), 0, (-8 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 65 : ℚ), (12 / 65 : ℚ), (-17 / 13 : ℚ), (-16 / 65 : ℚ), (-136 / 65 : ℚ)], ![(-28 / 65 : ℚ), 0, (-158 / 65 : ℚ), (28 / 65 : ℚ), (56 / 65 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-9 / 4 : ℚ), 0, (1 / 3 : ℚ), (-23 / 12 : ℚ)], ![(-7 / 6 : ℚ), (-7 / 6 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ), (-23 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-57 / 52 : ℚ), (-53 / 26 : ℚ), (-1 / 52 : ℚ), (15 / 52 : ℚ), (-1 / 78 : ℚ)], ![(-59 / 52 : ℚ), (-53 / 52 : ℚ), 0, (3 / 26 : ℚ), (-1 / 156 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 44 : ℚ), (-68 / 33 : ℚ), (-1 / 44 : ℚ), (1 / 4 : ℚ), 0], ![(-51 / 44 : ℚ), (-139 / 132 : ℚ), 0, (1 / 22 : ℚ), (1 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (-29 / 18 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 2 : ℚ)], ![(-8 / 9 : ℚ), (-5 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 18 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-11 / 10 : ℚ), (1 / 2 : ℚ), (-32 / 15 : ℚ)], ![(-3 / 10 : ℚ), 0, (-21 / 10 : ℚ), (6 / 5 : ℚ), (-16 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (1 / 6 : ℚ), (-23 / 18 : ℚ), (1 / 6 : ℚ), (-109 / 54 : ℚ)], ![(-7 / 18 : ℚ), 0, (-43 / 18 : ℚ), (7 / 9 : ℚ), (49 / 54 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-67 / 60 : ℚ), (1 / 10 : ℚ), (-21 / 5 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 20 : ℚ), (-32 / 15 : ℚ), (11 / 12 : ℚ), (-21 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-117 / 68 : ℚ), (-123 / 34 : ℚ), (-3 / 68 : ℚ), (-83 / 68 : ℚ), (-1 / 34 : ℚ)], ![(-123 / 68 : ℚ), (-123 / 68 : ℚ), 0, (-89 / 68 : ℚ), (-1 / 68 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 9 : ℚ), (-32 / 9 : ℚ), (-1 / 18 : ℚ), (-23 / 18 : ℚ), 0], ![(-17 / 9 : ℚ), (-11 / 6 : ℚ), 0, (-25 / 18 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 11 : ℚ), (-2 / 11 : ℚ), (-8 / 11 : ℚ), (-30 / 11 : ℚ)], ![(-2 / 11 : ℚ), (2 / 11 : ℚ), (-15 / 11 : ℚ), (10 / 11 : ℚ), (-15 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 8 : ℚ), (3 / 4 : ℚ), (-1 / 8 : ℚ)], ![(-11 / 8 : ℚ), (-19 / 16 : ℚ), 0, 0, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 16 : ℚ), (-3 / 4 : ℚ), (-73 / 16 : ℚ)], ![0, (-3 / 16 : ℚ), (-11 / 8 : ℚ), (15 / 16 : ℚ), (-73 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), (-15 / 7 : ℚ), (-1 / 14 : ℚ), (3 / 7 : ℚ), 0], ![(-17 / 14 : ℚ), (-15 / 14 : ℚ), 0, (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (-1 / 12 : ℚ)], ![(-5 / 4 : ℚ), (-9 / 8 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (-23 / 12 : ℚ)], ![(-7 / 6 : ℚ), (-7 / 6 : ℚ), 0, (1 / 12 : ℚ), (-23 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 3 : ℚ)], ![(-13 / 36 : ℚ), 0, (-10 / 9 : ℚ), 0, (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 7 : ℚ), 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), 0, (-9 / 7 : ℚ), 0, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, 0, (-9 / 2 : ℚ)], ![0, 0, (-7 / 6 : ℚ), (1 / 3 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-14 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 9 : ℚ), (-34 / 9 : ℚ), (-1 / 18 : ℚ), (-41 / 36 : ℚ), 0], ![(-35 / 18 : ℚ), (-23 / 12 : ℚ), (1 / 36 : ℚ), (-43 / 36 : ℚ), (1 / 18 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), 0], ![(-1 / 12 : ℚ), (-29 / 12 : ℚ), 0, 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), 0], ![(-1 / 8 : ℚ), (-21 / 8 : ℚ), 0, 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (-1 / 5 : ℚ)], ![0, (-23 / 10 : ℚ), 0, 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-29 / 12 : ℚ), 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 8 : ℚ), (1 / 24 : ℚ), (1 / 24 : ℚ), (-35 / 24 : ℚ)], ![(-1 / 24 : ℚ), (-53 / 24 : ℚ), 0, 0, (5 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 24 : ℚ), (-1 / 24 : ℚ), (1 / 12 : ℚ), (7 / 12 : ℚ), 0], ![(-31 / 24 : ℚ), 0, (-29 / 12 : ℚ), (-17 / 24 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-13 / 5 : ℚ)], ![0, (-13 / 5 : ℚ), 0, 0, (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 2 : ℚ)], ![0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0], ![0, (-16 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), 2]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), 0, (17 / 10 : ℚ), (-11 / 10 : ℚ), (1 / 4 : ℚ)], ![(-23 / 20 : ℚ), 0, (-11 / 20 : ℚ), (-11 / 5 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), 0, (5 / 3 : ℚ), (-7 / 6 : ℚ), 0], ![(-13 / 12 : ℚ), 0, (-7 / 12 : ℚ), (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (-6 / 5 : ℚ), (1 / 10 : ℚ)], ![(-13 / 10 : ℚ), 0, (-12 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-20 / 17 : ℚ), (3 / 34 : ℚ), 0, (-32 / 17 : ℚ)], ![(-3 / 34 : ℚ), (-40 / 17 : ℚ), 0, 0, (-5 / 34 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, (13 / 8 : ℚ), (-9 / 8 : ℚ), 0], ![(-19 / 16 : ℚ), 0, (-11 / 16 : ℚ), (-9 / 4 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), 0, (5 / 3 : ℚ), (-7 / 6 : ℚ), (-1 / 12 : ℚ)], ![(-13 / 12 : ℚ), 0, (-7 / 12 : ℚ), (-7 / 3 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-9 / 7 : ℚ)], ![(5 / 14 : ℚ), (-15 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (10 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-6 / 5 : ℚ)], ![(2 / 5 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![0, (-9 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, 0, 0, (-43 / 10 : ℚ)], ![(9 / 10 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-31 / 7 : ℚ)], ![(5 / 14 : ℚ), (-15 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -6], ![0, (-8 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), -6]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), 0, 0, -2, (1 / 2 : ℚ)], ![(-10 / 7 : ℚ), 0, -4, -2, (-5 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), 0, 0, -2, (1 / 4 : ℚ)], ![(-23 / 20 : ℚ), 0, -4, -2, (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), -2, 0, 0, (-4 / 3 : ℚ)], ![(1 / 6 : ℚ), -4, 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (-13 / 10 : ℚ), 0, (-7 / 10 : ℚ), (1 / 10 : ℚ)], ![0, (-13 / 5 : ℚ), (-7 / 5 : ℚ), (-7 / 10 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, 0, -2, 0], ![(-5 / 4 : ℚ), 0, -4, -2, (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, -2, 0], ![(-7 / 4 : ℚ), 0, -4, -2, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, -2, (-2 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, -4, -2, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-9 / 7 : ℚ)], ![(5 / 14 : ℚ), (-15 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (10 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-6 / 5 : ℚ)], ![(2 / 5 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![0, (-7 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, 0, 0, (-83 / 20 : ℚ)], ![(19 / 20 : ℚ), (-41 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (-13 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-31 / 7 : ℚ)], ![(5 / 14 : ℚ), (-15 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![0, (-26 / 9 : ℚ), (-8 / 9 : ℚ), 0, (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, (-4 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-28 / 9 : ℚ), (-11 / 9 : ℚ), (-2 / 9 : ℚ), (10 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-17 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, 0], ![(-5 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 10 : ℚ), 0, 0, 0], ![(-1 / 10 : ℚ), (-5 / 2 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 13 : ℚ), 0, 0, 0, 0], ![(-21 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ), (-40 / 13 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 5 : ℚ), 0, 0, 0, 0], ![(-9 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-17 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, -3], ![0, -3, (-4 / 3 : ℚ), (-1 / 3 : ℚ), -3]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 44 : ℚ), (-1 / 44 : ℚ), (18 / 11 : ℚ), (7 / 22 : ℚ), (1 / 4 : ℚ)], ![(-51 / 44 : ℚ), 0, (-7 / 11 : ℚ), 0, (1 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 7 : ℚ), (-3 / 7 : ℚ), (1 / 7 : ℚ), 0, 0], ![(-6 / 7 : ℚ), (-5 / 7 : ℚ), (-12 / 7 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (1 / 12 : ℚ), (3 / 8 : ℚ), (1 / 12 : ℚ)], ![(-4 / 3 : ℚ), (1 / 12 : ℚ), (-5 / 2 : ℚ), (-7 / 24 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 13 : ℚ), 0, (18 / 13 : ℚ), (9 / 26 : ℚ), 0], ![(-17 / 13 : ℚ), (1 / 13 : ℚ), (-15 / 13 : ℚ), (-7 / 26 : ℚ), (1 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 36 : ℚ), (-1 / 36 : ℚ), (14 / 9 : ℚ), (2 / 9 : ℚ), 0], ![(-43 / 36 : ℚ), 0, (-7 / 9 : ℚ), (-1 / 6 : ℚ), (1 / 18 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), (5 / 7 : ℚ), 0], ![(-10 / 7 : ℚ), 0, (-20 / 7 : ℚ), (-3 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (5 / 4 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-5 / 4 : ℚ), (1 / 8 : ℚ), (-11 / 8 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-19 / 16 : ℚ), (1 / 16 : ℚ), 0, (1 / 16 : ℚ)], ![(-1 / 16 : ℚ), (-37 / 16 : ℚ), 0, (3 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 28 : ℚ), 0, (12 / 7 : ℚ), (3 / 14 : ℚ), (-1 / 28 : ℚ)], ![(-8 / 7 : ℚ), (1 / 28 : ℚ), (-15 / 28 : ℚ), (1 / 28 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 44 : ℚ), (-1 / 44 : ℚ), (18 / 11 : ℚ), (1 / 4 : ℚ), 0], ![(-51 / 44 : ℚ), 0, (-7 / 11 : ℚ), (1 / 22 : ℚ), (1 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 28 : ℚ), (-1 / 28 : ℚ), (11 / 7 : ℚ), (1 / 4 : ℚ), 0], ![(-31 / 28 : ℚ), 0, (-5 / 7 : ℚ), (1 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (1 / 10 : ℚ), (2 / 5 : ℚ)], ![(-6 / 5 : ℚ), (1 / 10 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), (2 / 5 : ℚ), 0, (-9 / 5 : ℚ)], ![0, (-12 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), 0, (8 / 5 : ℚ), (11 / 10 : ℚ), 0], ![(-11 / 10 : ℚ), (1 / 10 : ℚ), (-7 / 10 : ℚ), (11 / 10 : ℚ), (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 7 : ℚ), (2 / 7 : ℚ), (-4 / 7 : ℚ), (-20 / 7 : ℚ)], ![0, (-20 / 7 : ℚ), 0, (-4 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), (-23 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-29 / 12 : ℚ), 0, (1 / 2 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), (-7 / 6 : ℚ)], ![(-1 / 12 : ℚ), (-29 / 12 : ℚ), 0, (1 / 2 : ℚ), (31 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (-23 / 10 : ℚ)], ![0, (-23 / 10 : ℚ), 0, (1 / 2 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-18 / 13 : ℚ), (-1 / 13 : ℚ), (10 / 13 : ℚ), 0, (-2 / 13 : ℚ)], ![(-20 / 13 : ℚ), 0, (-28 / 13 : ℚ), (2 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), 0, 0], ![(-10 / 7 : ℚ), 0, (-20 / 7 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-27 / 22 : ℚ), (-1 / 22 : ℚ), (14 / 11 : ℚ), 0, 0], ![(-29 / 22 : ℚ), 0, (-14 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 28 : ℚ), (-1 / 28 : ℚ), (11 / 7 : ℚ), 0, 0], ![(-31 / 28 : ℚ), 0, (-5 / 7 : ℚ), (1 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, 0], ![(-11 / 7 : ℚ), (2 / 7 : ℚ), (-22 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 4 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(-1 / 8 : ℚ), (-9 / 8 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, 0, 0], ![(-1 / 2 : ℚ), -1, -4, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 5 : ℚ), (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (6 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 6 : ℚ), (-9 / 4 : ℚ)], ![0, (-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 4 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), (1 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-10 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 5 : ℚ), (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), 0, 0, (2 / 5 : ℚ), (-1 / 10 : ℚ)], ![(-6 / 5 : ℚ), 0, (-23 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-19 / 8 : ℚ)], ![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![(-1 / 2 : ℚ), -1, -4, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![0, -1, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![0, -1, (-1 / 2 : ℚ), 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), -4], ![0, (-5 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ), -4]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), 0, (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), 0, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 2 : ℚ)], ![0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-41 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (-30 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-10 / 3 : ℚ)], ![0, (-13 / 9 : ℚ), (-40 / 9 : ℚ), 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-23 / 10 : ℚ), (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-9 / 4 : ℚ), (-9 / 4 : ℚ)], ![0, (-13 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 3 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![(-7 / 5 : ℚ), 0, (-13 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-16 / 5 : ℚ), (-16 / 5 : ℚ)], ![0, (-7 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 2 : ℚ), -2], ![0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), (-7 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 13 : ℚ), 0, (-32 / 13 : ℚ), (-32 / 13 : ℚ), (18 / 13 : ℚ)], ![(-22 / 13 : ℚ), 0, (-64 / 13 : ℚ), (-35 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), 0, (-12 / 5 : ℚ), (-12 / 5 : ℚ), 1], ![(-8 / 5 : ℚ), 0, (-24 / 5 : ℚ), (-13 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 8 : ℚ), (-3 / 16 : ℚ), (-31 / 16 : ℚ), (-15 / 8 : ℚ), 0], ![(-7 / 8 : ℚ), (-3 / 8 : ℚ), (-31 / 8 : ℚ), (-15 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 20 : ℚ), 0, (-21 / 10 : ℚ), (-21 / 10 : ℚ), (1 / 20 : ℚ)], ![(-53 / 20 : ℚ), 0, (-21 / 5 : ℚ), (-43 / 20 : ℚ), (-17 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-13 / 6 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ)], ![(-19 / 12 : ℚ), 0, (-13 / 3 : ℚ), (-9 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 8 : ℚ), (-19 / 8 : ℚ), 0, (1 / 8 : ℚ), (-19 / 4 : ℚ)], ![(1 / 2 : ℚ), (-19 / 4 : ℚ), 0, 0, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (1 / 3 : ℚ), (-11 / 3 : ℚ), -3, 0], ![-2, (2 / 3 : ℚ), (-22 / 3 : ℚ), -3, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-1 / 13 : ℚ), 0, 0, (-18 / 13 : ℚ)], ![(11 / 26 : ℚ), (-29 / 13 : ℚ), (-1 / 13 : ℚ), (-1 / 13 : ℚ), (19 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-1 / 14 : ℚ), 0, 0, (-9 / 7 : ℚ)], ![(3 / 7 : ℚ), (-31 / 14 : ℚ), (-1 / 14 : ℚ), (-1 / 14 : ℚ), (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)], ![0, (-13 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(23 / 22 : ℚ), (-1 / 22 : ℚ), 0, (1 / 22 : ℚ), (-47 / 11 : ℚ)], ![1, (-47 / 22 : ℚ), (-1 / 22 : ℚ), 0, (-15 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(11 / 18 : ℚ), (-1 / 9 : ℚ), 0, (1 / 9 : ℚ), (-43 / 9 : ℚ)], ![(1 / 2 : ℚ), (-7 / 3 : ℚ), (-1 / 9 : ℚ), 0, (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-13 / 2 : ℚ)], ![0, (-7 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-13 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 13 : ℚ), 0, (-1 / 13 : ℚ), (-28 / 13 : ℚ), (7 / 26 : ℚ)], ![(-16 / 13 : ℚ), 0, (-1 / 13 : ℚ), (-56 / 13 : ℚ), (-5 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-1 / 6 : ℚ), (-5 / 2 : ℚ), (5 / 6 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, -5, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-5 / 2 : ℚ), (3 / 4 : ℚ)], ![(-5 / 4 : ℚ), 0, (-1 / 4 : ℚ), -5, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-9 / 4 : ℚ), 0], ![(-3 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-9 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-1 / 6 : ℚ), (-5 / 2 : ℚ), 0], ![(-3 / 2 : ℚ), 0, 0, -5, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), 0, (-2 / 9 : ℚ), (-8 / 3 : ℚ), (-2 / 9 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, (-16 / 3 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (-10 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-22 / 3 : ℚ)], ![(2 / 3 : ℚ), (-20 / 3 : ℚ), -4, 0, (-22 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ)], ![0, (-16 / 5 : ℚ), (2 / 5 : ℚ), (4 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), 0, (-7 / 6 : ℚ), (1 / 4 : ℚ), (1 / 6 : ℚ)], ![(-13 / 12 : ℚ), 0, (-7 / 3 : ℚ), 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 20 : ℚ), (-23 / 20 : ℚ), (1 / 20 : ℚ), 0, (1 / 20 : ℚ)], ![0, (-23 / 10 : ℚ), (1 / 10 : ℚ), (1 / 2 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, -3, 1, -1], ![-2, 0, -6, -1, -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-39 / 34 : ℚ), (-1 / 34 : ℚ), (-39 / 34 : ℚ), (19 / 68 : ℚ), (-3 / 34 : ℚ)], ![(-21 / 17 : ℚ), (-1 / 17 : ℚ), (-39 / 17 : ℚ), (-13 / 68 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 13 : ℚ), 0, (-19 / 13 : ℚ), (18 / 13 : ℚ), 0], ![(-22 / 13 : ℚ), 0, (-38 / 13 : ℚ), 0, (3 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 16 : ℚ), (-1 / 8 : ℚ), -1, 0, (-5 / 16 : ℚ)], ![(-15 / 16 : ℚ), (-1 / 4 : ℚ), -2, (1 / 16 : ℚ), (-5 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (-3 / 2 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ)], ![(-5 / 4 : ℚ), 0, -3, (1 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), 0, (-8 / 7 : ℚ), (5 / 14 : ℚ), (3 / 14 : ℚ)], ![(-17 / 14 : ℚ), 0, (-16 / 7 : ℚ), (1 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, -3, 1, -1], ![(-7 / 4 : ℚ), 0, -6, 0, -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, (-7 / 6 : ℚ), (5 / 12 : ℚ), (-1 / 12 : ℚ)], ![(-5 / 4 : ℚ), 0, (-7 / 3 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (-6 / 5 : ℚ), (1 / 2 : ℚ), 0], ![(-13 / 10 : ℚ), 0, (-12 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), 0, (-7 / 6 : ℚ), (1 / 4 : ℚ), (-1 / 12 : ℚ)], ![(-13 / 12 : ℚ), 0, (-7 / 3 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), 0, (-6 / 5 : ℚ), (1 / 5 : ℚ), (3 / 10 : ℚ)], ![(-11 / 10 : ℚ), 0, (-12 / 5 : ℚ), 0, (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -1, -2, 0, 0], ![(-1 / 4 : ℚ), -2, -4, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 4 : ℚ), 0, -2], ![0, -2, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, -2, (-1 / 2 : ℚ), 0, (15 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, (-10 / 3 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, -3, 0, -1], ![(-3 / 2 : ℚ), 0, -6, -1, -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), 0, (-8 / 7 : ℚ), (3 / 14 : ℚ), 0], ![(-17 / 14 : ℚ), 0, (-16 / 7 : ℚ), 0, (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), 0, (-9 / 7 : ℚ), (3 / 7 : ℚ), 0], ![(-10 / 7 : ℚ), 0, (-18 / 7 : ℚ), 0, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (-19 / 8 : ℚ)], ![0, (-9 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-67 / 51 : ℚ), (-1 / 34 : ℚ), (-107 / 34 : ℚ), (-39 / 34 : ℚ), (-3 / 34 : ℚ)], ![(-80 / 51 : ℚ), (-1 / 17 : ℚ), (-107 / 17 : ℚ), (-21 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, (-7 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(-7 / 4 : ℚ), 0, -7, (-7 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-11 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, (-22 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 17 : ℚ), 0, (-23 / 17 : ℚ), 0, (-1 / 17 : ℚ)], ![(-26 / 17 : ℚ), 0, (-46 / 17 : ℚ), (3 / 17 : ℚ), (1 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, (-10 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), 0, (-7 / 5 : ℚ), 0, 0], ![(-8 / 5 : ℚ), 0, (-14 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), 0, (-17 / 9 : ℚ), (-2 / 9 : ℚ), (-4 / 9 : ℚ)], ![(-13 / 9 : ℚ), 0, (-34 / 9 : ℚ), (4 / 9 : ℚ), (-4 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, (-5 / 2 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-7 / 4 : ℚ), 0, -5, (-3 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-17 / 12 : ℚ), (-4 / 3 : ℚ)], ![(1 / 2 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (3 / 2 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-1 / 12 : ℚ), 0, (-17 / 12 : ℚ), (-5 / 4 : ℚ)], ![(1 / 2 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (3 / 2 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, (-9 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (-33 / 16 : ℚ), (-1 / 16 : ℚ), (19 / 16 : ℚ), (19 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, (-5 / 4 : ℚ), (5 / 4 : ℚ)], ![(1 / 4 : ℚ), (-9 / 4 : ℚ), -2, (5 / 4 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-11 / 6 : ℚ), -5], ![1, (-5 / 2 : ℚ), (-1 / 6 : ℚ), 2, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 24 : ℚ), (-1 / 12 : ℚ), 0, (-17 / 12 : ℚ), (-55 / 12 : ℚ)], ![(11 / 24 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (3 / 2 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (-1 / 24 : ℚ), 0, (-29 / 24 : ℚ), (-101 / 24 : ℚ)], ![(1 / 4 : ℚ), (-17 / 8 : ℚ), (-1 / 24 : ℚ), (5 / 4 : ℚ), (-101 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 11 : ℚ), (-12 / 11 : ℚ), (-7 / 11 : ℚ), (-5 / 11 : ℚ)], ![0, (-16 / 11 : ℚ), (-26 / 11 : ℚ), (2 / 11 : ℚ), (-5 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, (-6 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), (13 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 4 : ℚ), 0, (1 / 4 : ℚ), (-23 / 12 : ℚ), (23 / 12 : ℚ)], ![(19 / 12 : ℚ), (-35 / 12 : ℚ), 0, 0, (23 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 3 : ℚ), -5], ![1, (-5 / 2 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (5 / 6 : ℚ), (-1 / 6 : ℚ)], ![(-3 / 2 : ℚ), 0, (-31 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 11 : ℚ), (-2 / 11 : ℚ), (-28 / 11 : ℚ), (9 / 11 : ℚ), 0], ![(-15 / 11 : ℚ), 0, (-58 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-5 / 4 : ℚ)], ![(1 / 2 : ℚ), (-17 / 8 : ℚ), (-1 / 8 : ℚ), (11 / 8 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-11 / 6 : ℚ), (11 / 6 : ℚ)], ![(1 / 6 : ℚ), (-19 / 6 : ℚ), 0, (-11 / 6 : ℚ), (11 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 4 : ℚ), (-1 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-19 / 4 : ℚ)], ![(5 / 4 : ℚ), (-19 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-23 / 4 : ℚ)], ![(3 / 2 : ℚ), (-11 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), -5], ![0, (-13 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ), -5]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, 0, 0, (-43 / 10 : ℚ)], ![(9 / 10 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-31 / 7 : ℚ)], ![(5 / 14 : ℚ), (-15 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -5], ![0, (-7 / 3 : ℚ), (-1 / 3 : ℚ), (2 / 3 : ℚ), -5]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(23 / 22 : ℚ), (-1 / 22 : ℚ), 0, (13 / 44 : ℚ), (-47 / 11 : ℚ)], ![1, (-47 / 22 : ℚ), (-75 / 44 : ℚ), (1 / 4 : ℚ), (-93 / 44 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 9 : ℚ), (-1 / 9 : ℚ), (-7 / 3 : ℚ), (-11 / 9 : ℚ), (-1 / 9 : ℚ)], ![(-11 / 6 : ℚ), 0, (-50 / 9 : ℚ), (-4 / 3 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, -3], ![0, (-5 / 3 : ℚ), (-11 / 3 : ℚ), 0, -3]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), (-1 / 14 : ℚ), (-31 / 14 : ℚ), (-1 / 14 : ℚ), (-3 / 14 : ℚ)], ![(-41 / 28 : ℚ), 0, (-9 / 2 : ℚ), (1 / 14 : ℚ), (-1 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(9 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-40 / 7 : ℚ), (-38 / 7 : ℚ)], ![(9 / 7 : ℚ), (-20 / 7 : ℚ), (-2 / 7 : ℚ), (-19 / 7 : ℚ), (-38 / 7 : ℚ)]] }
]

theorem conicDetC31_checked : conicDetC31.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
