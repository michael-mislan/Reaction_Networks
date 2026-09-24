import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC01 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), 0, 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), -1, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (2 / 5 : ℚ), 0, (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0], ![(4 / 5 : ℚ), (4 / 5 : ℚ), 0, (-8 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(2 / 3 : ℚ), (2 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, -1, 0], ![0, 0, 0, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-5 / 4 : ℚ), 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-6 / 25 : ℚ), 0, (-68 / 25 : ℚ), (27 / 25 : ℚ)], ![(39 / 25 : ℚ), (66 / 25 : ℚ), (6 / 25 : ℚ), (-74 / 25 : ℚ), (-21 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 22 : ℚ), (-49 / 22 : ℚ), (1 / 2 : ℚ)], ![(13 / 22 : ℚ), (12 / 11 : ℚ), 0, (-51 / 22 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), -5, (-1 / 5 : ℚ), (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), (-4 / 13 : ℚ), 0, (-38 / 13 : ℚ), 0], ![0, 0, (4 / 13 : ℚ), (-42 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-13 / 5 : ℚ), 0], ![(1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (21 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 11 : ℚ), 0, (-48 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), 0, (-56 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-26 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), 0], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 6 : ℚ), (-31 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), -1, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), -1], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, (-16 / 11 : ℚ), (-16 / 11 : ℚ)], ![(-8 / 11 : ℚ), (-16 / 11 : ℚ), (-4 / 11 : ℚ), (20 / 11 : ℚ), (-6 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, (-16 / 11 : ℚ), (-20 / 11 : ℚ)], ![(-8 / 11 : ℚ), (-8 / 11 : ℚ), (-4 / 11 : ℚ), (20 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-8 / 5 : ℚ), 0, 0], ![(4 / 5 : ℚ), (4 / 5 : ℚ), (-8 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), -1, 0, 0], ![(1 / 3 : ℚ), (1 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-5 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), 0, (2 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, 0, 0], ![0, 0, -1, 0, (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-10 / 3 : ℚ)], ![(-4 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ), 4]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, 0, (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), 0, 0, (-20 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-5 / 12 : ℚ), 0], ![(1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 6 : ℚ), (-7 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 10 : ℚ), 0, (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ), 0, (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, -1, 0], ![0, 0, 0, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-8 / 7 : ℚ), 0, (-20 / 7 : ℚ)], ![(-8 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ), 0, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), 0, (-19 / 13 : ℚ), 0], ![0, 0, (2 / 13 : ℚ), (-21 / 13 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0], ![(1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 11 : ℚ), 0, (-26 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-13 / 11 : ℚ), (-1 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ), 0, (-28 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-13 / 9 : ℚ), (-2 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-17 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), 0, (-41 / 12 : ℚ)], ![(-1 / 2 : ℚ), (-11 / 12 : ℚ), (-7 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ), (-17 / 6 : ℚ)], ![(-4 / 3 : ℚ), (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-1 / 5 : ℚ), (-4 / 5 : ℚ), (-7 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-28 / 13 : ℚ)], ![(-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-24 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), 0, (-5 / 8 : ℚ), (1 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), 0], ![0, 0, (-2 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-1 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 10 : ℚ), 0, (-7 / 10 : ℚ), 0], ![(1 / 2 : ℚ), (-1 / 5 : ℚ), (-9 / 10 : ℚ), (-8 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), 0, (2 / 3 : ℚ), (-10 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-28 / 13 : ℚ)], ![(-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-24 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 6 : ℚ), 0], ![0, 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), 0, (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-9 / 5 : ℚ), (-7 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), 0], ![0, 0, (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (1 / 6 : ℚ)], ![(1 / 3 : ℚ), 0, -1, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, (-1 / 4 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(1 / 5 : ℚ), (-1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), (-7 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), 0], ![0, 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(1 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-3 / 4 : ℚ)], ![(1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 16 : ℚ), 0, (-3 / 16 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 16 : ℚ), 0, (-3 / 16 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 16 : ℚ), 0, (-1 / 16 : ℚ), 0], ![(3 / 16 : ℚ), (-1 / 4 : ℚ), (-11 / 16 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 13 : ℚ), 0, 0, 0], ![(4 / 13 : ℚ), (-8 / 13 : ℚ), (-22 / 13 : ℚ), (4 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 1, -1], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 8 : ℚ), 0, 0, 0], ![0, (-1 / 8 : ℚ), -1, (-1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-17 / 13 : ℚ), (-4 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 8 : ℚ), 0, (3 / 8 : ℚ), 0], ![(3 / 8 : ℚ), 0, (-7 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0], ![(1 / 8 : ℚ), 0, (-5 / 8 : ℚ), 0, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 14 : ℚ), 0, 0, 0], ![(1 / 28 : ℚ), (-1 / 28 : ℚ), (-27 / 28 : ℚ), (17 / 28 : ℚ), (23 / 28 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 3 : ℚ), -4], ![(-1 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), (-7 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-28 / 13 : ℚ)], ![(-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-24 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), 0, (4 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-10 / 3 : ℚ), 0, 0, 0], ![(4 / 9 : ℚ), 0, (22 / 9 : ℚ), (-68 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 24 : ℚ), (-1 / 4 : ℚ), (-1 / 24 : ℚ), (-77 / 24 : ℚ)], ![0, (-1 / 24 : ℚ), (-7 / 24 : ℚ), (-19 / 24 : ℚ), (-19 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-7 / 5 : ℚ), (-1 / 5 : ℚ), (-9 / 5 : ℚ), 0], ![(1 / 5 : ℚ), 0, (6 / 5 : ℚ), (-19 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), 0, (-19 / 24 : ℚ), (-19 / 12 : ℚ), (-7 / 24 : ℚ)], ![(-1 / 24 : ℚ), (-5 / 24 : ℚ), (-1 / 24 : ℚ), (-77 / 24 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), 0, (-68 / 75 : ℚ), (-136 / 75 : ℚ), (-286 / 75 : ℚ)], ![(-6 / 25 : ℚ), (-6 / 25 : ℚ), (-6 / 25 : ℚ), (-58 / 15 : ℚ), (-134 / 75 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (-46 / 17 : ℚ), (-8 / 17 : ℚ), (-62 / 17 : ℚ), 0], ![(4 / 17 : ℚ), 0, (38 / 17 : ℚ), (-132 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 17 : ℚ), 0, (-21 / 17 : ℚ), (-42 / 17 : ℚ), (-38 / 17 : ℚ)], ![(-4 / 17 : ℚ), (-4 / 17 : ℚ), (-4 / 17 : ℚ), (-88 / 17 : ℚ), (-36 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-7 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ), 0], ![(1 / 5 : ℚ), 0, (6 / 5 : ℚ), (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), 0, (-34 / 11 : ℚ), (-34 / 11 : ℚ), (-13 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-5 / 22 : ℚ), (-1 / 11 : ℚ), (-35 / 11 : ℚ), (-6 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-19 / 8 : ℚ), (-1 / 4 : ℚ), (-21 / 8 : ℚ), 0], ![(1 / 8 : ℚ), 0, (17 / 8 : ℚ), (-23 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, (-1 / 10 : ℚ), (-3 / 10 : ℚ), 0], ![0, 0, (-4 / 5 : ℚ), (-1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), 0, 0, (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 2 : ℚ), 0, 2, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, -1, 0, 0, -3]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), 0, (-17 / 11 : ℚ), (-6 / 11 : ℚ), (-57 / 22 : ℚ)], ![(-1 / 22 : ℚ), (-1 / 22 : ℚ), (-1 / 22 : ℚ), (-13 / 22 : ℚ), (-14 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, (-1 / 6 : ℚ), (-4 / 3 : ℚ), 0], ![(1 / 12 : ℚ), 0, 2, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-7 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), -2, (1 / 4 : ℚ), (-15 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![0, 0, -1, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), -1], ![0, (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0], ![0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, (-3 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), -1, (-1 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-7 / 8 : ℚ), (-9 / 8 : ℚ), (-11 / 8 : ℚ), 0], ![(5 / 8 : ℚ), (-1 / 4 : ℚ), (-11 / 8 : ℚ), -3, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-3 / 4 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 2 : ℚ), (-3 / 4 : ℚ), -3, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, (-3 / 5 : ℚ), (-3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, 0, -2], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, -1, (-1 / 2 : ℚ)], ![0, 0, (-3 / 2 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-4 / 3 : ℚ), 0, (2 / 3 : ℚ)], ![(2 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 8 : ℚ), 0, (-11 / 8 : ℚ), (-3 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), (-21 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (17 / 20 : ℚ), (1 / 20 : ℚ), (-6 / 5 : ℚ), (-19 / 20 : ℚ)], ![(-9 / 10 : ℚ), 0, 0, (-47 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-13 / 10 : ℚ), 0, 0], ![(1 / 10 : ℚ), (-1 / 10 : ℚ), (-7 / 5 : ℚ), (1 / 10 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (1 / 12 : ℚ), (-4 / 3 : ℚ), (-25 / 12 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 12 : ℚ), 0, (-31 / 12 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (3 / 2 : ℚ), (1 / 6 : ℚ), (-5 / 3 : ℚ), (-23 / 6 : ℚ)], ![(-11 / 6 : ℚ), 0, 0, (-19 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 5 : ℚ), 0, (-1 / 10 : ℚ), (-2 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-1 / 10 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (-1 / 10 : ℚ), (-2 / 5 : ℚ)], ![(-3 / 10 : ℚ), 0, 0, (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), 0, 0, (-1 / 11 : ℚ), (-26 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 11 : ℚ), (-13 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), (-13 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, -1], ![0, 0, (-2 / 3 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![0, 0, (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, (-3 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (-7 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 8 : ℚ), (-3 / 8 : ℚ), (-3 / 8 : ℚ), 0], ![(-1 / 8 : ℚ), 0, (-3 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -4], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, -1, 0, 0], ![(5 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), (-9 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (-7 / 3 : ℚ)], ![-1, (-1 / 3 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-3 / 4 : ℚ), (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ), 0], ![(-3 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-16 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, 0], ![0, 0, (-1 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (-5 / 3 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 17 : ℚ), (4 / 17 : ℚ), 0, (-132 / 17 : ℚ)], ![(-12 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), 0, (-62 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, -2], ![(-3 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-32 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0], ![0, 0, (-1 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ)], ![(-7 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-2 / 11 : ℚ), (-13 / 11 : ℚ), (-7 / 11 : ℚ), (-1 / 11 : ℚ)], ![0, (-1 / 11 : ℚ), (-1 / 11 : ℚ), (-26 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -1, -3, -1, (-1 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), -6, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 17 : ℚ), (-16 / 17 : ℚ), (-16 / 17 : ℚ), (-48 / 17 : ℚ), (-16 / 17 : ℚ)], ![0, 0, 0, (-112 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 2 : ℚ), (-5 / 2 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), -5, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0], ![0, 0, (-1 / 6 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, 0, (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 2 : ℚ), (-5 / 2 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, 0, (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 7 : ℚ), -1, 0], ![0, 0, (-2 / 7 : ℚ), (-12 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 16 : ℚ), 0, (-19 / 16 : ℚ), 0], ![(-9 / 16 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 4 : ℚ), (5 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-3 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-11 / 10 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-32 / 17 : ℚ), (-43 / 17 : ℚ), (32 / 17 : ℚ), (-3 / 17 : ℚ)], ![(32 / 17 : ℚ), 0, (-3 / 17 : ℚ), (-32 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-59 / 31 : ℚ), (-74 / 31 : ℚ), (59 / 31 : ℚ), (-4 / 31 : ℚ)], ![(59 / 31 : ℚ), 0, (-8 / 31 : ℚ), (-59 / 31 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-47 / 10 : ℚ)], ![(-3 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![0, 0, 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 13 : ℚ), (-17 / 13 : ℚ), 0, (-32 / 13 : ℚ)], ![0, (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-8 / 13 : ℚ), (-30 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-9 / 4 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, 0, (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-24 / 23 : ℚ), (-74 / 23 : ℚ), 0, 0], ![(12 / 23 : ℚ), (-24 / 23 : ℚ), (-43 / 23 : ℚ), (12 / 23 : ℚ), (-80 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-12 / 17 : ℚ), (-62 / 17 : ℚ), 0, 0], ![(4 / 17 : ℚ), (-4 / 17 : ℚ), (-33 / 17 : ℚ), (-64 / 17 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-4 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 8 : ℚ), (-11 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), -3, (-23 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 17 : ℚ), 0, 0, (-4 / 17 : ℚ), (-24 / 17 : ℚ)], ![(-2 / 17 : ℚ), (-2 / 17 : ℚ), (-1 / 17 : ℚ), (-10 / 17 : ℚ), (-22 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 4 : ℚ), -1, (-3 / 4 : ℚ), 0], ![0, (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ), (2 / 9 : ℚ), (-32 / 9 : ℚ)], ![(-14 / 9 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 21 : ℚ), 0, 0, (-16 / 21 : ℚ), (-36 / 7 : ℚ)], ![(-8 / 21 : ℚ), (-8 / 21 : ℚ), (-4 / 21 : ℚ), (-40 / 21 : ℚ), (-104 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![0, 0, (-1 / 2 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ), (-16 / 7 : ℚ)], ![0, (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-12 / 7 : ℚ), (-8 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (-7 / 2 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 20 : ℚ), 0, (-27 / 20 : ℚ), (-7 / 20 : ℚ)], ![(-7 / 20 : ℚ), 0, (-3 / 20 : ℚ), (-12 / 5 : ℚ), (7 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-29 / 24 : ℚ), (-7 / 8 : ℚ)], ![(-3 / 4 : ℚ), 0, 0, (-55 / 24 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 4 : ℚ), 0, (-3 / 4 : ℚ), -3], ![(-3 / 4 : ℚ), 0, 0, (3 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, 0, (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-31 / 17 : ℚ), (-88 / 17 : ℚ), (31 / 17 : ℚ), (-4 / 17 : ℚ)], ![(31 / 17 : ℚ), 0, (-48 / 17 : ℚ), (-31 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), -1, (-1 / 4 : ℚ), 0], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-7 / 8 : ℚ), (-9 / 2 : ℚ)], ![(-3 / 4 : ℚ), 0, 0, 0, (-71 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 9 : ℚ), 0, 0, (-16 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-4 / 9 : ℚ), 0, (-8 / 9 : ℚ), (-8 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 10 : ℚ), (-26 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-14 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, -1, (-1 / 2 : ℚ)], ![0, 0, -1, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0], ![(1 / 4 : ℚ), 0, -1, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-8 / 3 : ℚ)], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-8 / 3 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (-1 / 3 : ℚ), 0], ![(1 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-20 / 11 : ℚ), 0, 0, 0], ![(2 / 11 : ℚ), (-2 / 11 : ℚ), (-42 / 11 : ℚ), (5 / 11 : ℚ), (14 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-14 / 3 : ℚ)], ![0, 0, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), (-7 / 4 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-28 / 13 : ℚ)], ![(-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-24 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-30 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] }
]

theorem conicDetC01_checked : conicDetC01.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
