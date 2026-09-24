import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC11 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 19 : ℚ)], ![(-6 / 19 : ℚ), (-3 / 19 : ℚ), (-6 / 19 : ℚ), (-6 / 19 : ℚ), (18 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, (-4 / 3 : ℚ), 0], ![(1 / 6 : ℚ), (-4 / 3 : ℚ), (-17 / 6 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), 0, (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, -1, 0], ![(1 / 3 : ℚ), -1, (-8 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-52 / 9 : ℚ), 0, (-10 / 3 : ℚ), 0], ![(4 / 9 : ℚ), (-10 / 3 : ℚ), (-68 / 9 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 3 : ℚ), -1, 0, 0, (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 3 : ℚ), -1, 0, 0, (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 3 : ℚ), 0, 0, -1, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, -1, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 10 : ℚ), 0, (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 10 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (-1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, (-1 / 4 : ℚ), (1 / 4 : ℚ), -4, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, (-4 / 9 : ℚ)], ![(-1 / 9 : ℚ), 0, (2 / 9 : ℚ), (-1 / 9 : ℚ), (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 10 : ℚ), 0, (-2 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-62 / 17 : ℚ), 0, 0, 0], ![(4 / 17 : ℚ), (-33 / 17 : ℚ), (4 / 17 : ℚ), (4 / 17 : ℚ), (-64 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-31 / 17 : ℚ), 0, 0], ![(-2 / 17 : ℚ), (-2 / 17 : ℚ), (-27 / 17 : ℚ), (-19 / 17 : ℚ), (-2 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-20 / 7 : ℚ), 0, 0, 0], ![0, (-11 / 7 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-54 / 17 : ℚ), (-4 / 17 : ℚ), 0, (44 / 51 : ℚ)], ![(56 / 51 : ℚ), (-29 / 17 : ℚ), 0, (-56 / 17 : ℚ), (-32 / 51 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-31 / 12 : ℚ), 0, 0, (7 / 12 : ℚ)], ![(2 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), (-21 / 8 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-62 / 17 : ℚ), 0, 0, 0], ![(4 / 17 : ℚ), (-33 / 17 : ℚ), (4 / 17 : ℚ), (-64 / 17 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-17 / 10 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 2 : ℚ), (-1 / 10 : ℚ), (9 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -3, 0, 0, 0], ![0, -2, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-18 / 5 : ℚ), 0, 0, (8 / 15 : ℚ)], ![(2 / 5 : ℚ), (-9 / 5 : ℚ), (4 / 15 : ℚ), (-56 / 15 : ℚ), (4 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-36 / 11 : ℚ), 0, 0, 0], ![(2 / 11 : ℚ), (-19 / 11 : ℚ), (2 / 11 : ℚ), (-37 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-62 / 17 : ℚ), 0, 0, (-18 / 17 : ℚ)], ![(4 / 17 : ℚ), (-33 / 17 : ℚ), (4 / 17 : ℚ), (-64 / 17 : ℚ), (-16 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, 0], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-26 / 9 : ℚ), (-11 / 9 : ℚ), (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, 0], ![0, (-3 / 2 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-39 / 16 : ℚ), 0, 0, (7 / 16 : ℚ)], ![(5 / 8 : ℚ), (-21 / 16 : ℚ), (3 / 16 : ℚ), (-81 / 32 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-67 / 30 : ℚ), 0, 0, (7 / 15 : ℚ)], ![(17 / 30 : ℚ), (-7 / 6 : ℚ), (1 / 10 : ℚ), (-137 / 60 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-130 / 51 : ℚ), 0, 0, (-28 / 51 : ℚ)], ![(4 / 17 : ℚ), (-71 / 51 : ℚ), (4 / 17 : ℚ), (-8 / 3 : ℚ), (-16 / 51 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-23 / 16 : ℚ), 0, 0], ![(-3 / 16 : ℚ), (-3 / 16 : ℚ), (-5 / 2 : ℚ), (-3 / 16 : ℚ), (13 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-22 / 7 : ℚ), 0, 0, (8 / 21 : ℚ)], ![(4 / 7 : ℚ), (-11 / 7 : ℚ), (4 / 7 : ℚ), (-24 / 7 : ℚ), (4 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-52 / 19 : ℚ), 0, 0, 0], ![(6 / 19 : ℚ), (-29 / 19 : ℚ), (6 / 19 : ℚ), (-55 / 19 : ℚ), (6 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-74 / 23 : ℚ), 0, 0, (-54 / 23 : ℚ)], ![(12 / 23 : ℚ), (-43 / 23 : ℚ), (12 / 23 : ℚ), (-80 / 23 : ℚ), (-48 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-9 / 16 : ℚ)], ![(-3 / 16 : ℚ), (-3 / 16 : ℚ), (-19 / 16 : ℚ), (-3 / 16 : ℚ), (15 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-31 / 17 : ℚ)], ![(-2 / 17 : ℚ), (-2 / 17 : ℚ), (-19 / 17 : ℚ), (-2 / 17 : ℚ), (-27 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-11 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-21 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, -1, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-44 / 15 : ℚ), 0, 0, 0], ![0, (-23 / 15 : ℚ), (-2 / 15 : ℚ), -4, (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-38 / 11 : ℚ)], ![(-4 / 11 : ℚ), 0, (-15 / 22 : ℚ), (-48 / 11 : ℚ), (-19 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-13 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-32 / 5 : ℚ), (-7 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (-18 / 5 : ℚ), (-4 / 5 : ℚ), (-38 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 2 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (5 / 6 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-7 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, 0], ![(2 / 5 : ℚ), (-3 / 5 : ℚ), (-7 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, (-3 / 16 : ℚ), 0], ![(3 / 16 : ℚ), (-9 / 16 : ℚ), (-15 / 16 : ℚ), (9 / 16 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-73 / 16 : ℚ), 0, (3 / 2 : ℚ), 0], ![(27 / 16 : ℚ), (-19 / 8 : ℚ), (-149 / 32 : ℚ), (-21 / 16 : ℚ), (3 / 32 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 3 : ℚ), -1, (-13 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-7 / 10 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, (-1 / 2 : ℚ), -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 9 : ℚ), 0, (-1 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (-2 / 9 : ℚ), (-5 / 9 : ℚ), (2 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-7 / 10 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 4 : ℚ), 0, (59 / 40 : ℚ), (-1 / 20 : ℚ)], ![(63 / 40 : ℚ), (-87 / 40 : ℚ), (-43 / 10 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -3, 0, 0, 0], ![0, -2, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-18 / 5 : ℚ), 0, 0, (-52 / 15 : ℚ)], ![(4 / 15 : ℚ), (-9 / 5 : ℚ), (-56 / 15 : ℚ), (4 / 15 : ℚ), (-26 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-62 / 17 : ℚ), 0, 0, (-18 / 17 : ℚ)], ![(4 / 17 : ℚ), (-33 / 17 : ℚ), (-64 / 17 : ℚ), (4 / 17 : ℚ), (-16 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-26 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), -5]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, 0, (-4 / 3 : ℚ)], ![(-4 / 9 : ℚ), (2 / 9 : ℚ), (-40 / 9 : ℚ), (-4 / 9 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-32 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-44 / 9 : ℚ), 0, (-5 / 3 : ℚ), 0], ![(2 / 9 : ℚ), (-8 / 3 : ℚ), (-70 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), (4 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -5, 0, 0, 0], ![(1 / 4 : ℚ), (-5 / 2 : ℚ), (-21 / 4 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, -1, (-7 / 10 : ℚ)], ![(-3 / 10 : ℚ), (-1 / 10 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, 0, 0, 0], ![(1 / 4 : ℚ), -2, (-17 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-92 / 17 : ℚ), 0, 0, (-16 / 17 : ℚ)], ![(4 / 17 : ℚ), (-50 / 17 : ℚ), (-96 / 17 : ℚ), (4 / 17 : ℚ), (-8 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-6 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (2 / 11 : ℚ), (-14 / 11 : ℚ), (-6 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-35 / 16 : ℚ), 0, (-3 / 16 : ℚ), (-9 / 8 : ℚ)], ![0, (-9 / 8 : ℚ), 0, (-7 / 4 : ℚ), (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (12 / 25 : ℚ), (-6 / 25 : ℚ), 0, (-24 / 25 : ℚ)], ![(-12 / 25 : ℚ), (3 / 25 : ℚ), (-18 / 25 : ℚ), (-6 / 25 : ℚ), (6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-6 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (-14 / 11 : ℚ), (-6 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-35 / 16 : ℚ), (-3 / 16 : ℚ), (-9 / 8 : ℚ), 0], ![0, (-9 / 8 : ℚ), (-7 / 4 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-8 / 5 : ℚ), (-12 / 5 : ℚ), (-8 / 5 : ℚ), 0], ![0, (-4 / 5 : ℚ), (-28 / 5 : ℚ), (-12 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (-14 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-9 / 2 : ℚ), (-5 / 8 : ℚ), (-19 / 8 : ℚ), 0], ![(-1 / 8 : ℚ), (-19 / 8 : ℚ), (-15 / 4 : ℚ), (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 26 : ℚ), -2, 0, 0, (-6 / 13 : ℚ)], ![(3 / 26 : ℚ), -1, 0, 0, (-93 / 52 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 22 : ℚ), -2, 0, 0, (-23 / 22 : ℚ)], ![(3 / 22 : ℚ), -1, 0, 0, (-23 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -1, 0, -1], ![(-1 / 4 : ℚ), 0, 0, -1, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), -1, 1, 0], ![-1, 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-12 / 13 : ℚ), 0, (-10 / 13 : ℚ), 0], ![(4 / 13 : ℚ), (-7 / 13 : ℚ), (2 / 13 : ℚ), (-22 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (2 / 11 : ℚ), (-5 / 11 : ℚ), (-3 / 11 : ℚ), (-5 / 11 : ℚ)], ![(-3 / 11 : ℚ), 0, (2 / 11 : ℚ), (-8 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), 0, 0], ![(-3 / 14 : ℚ), (3 / 28 : ℚ), (1 / 14 : ℚ), (-3 / 2 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (2 / 15 : ℚ), (-3 / 5 : ℚ), (1 / 15 : ℚ), (-16 / 15 : ℚ)], ![(-7 / 15 : ℚ), 0, (2 / 15 : ℚ), 0, (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-55 / 17 : ℚ), 0, 0, (-28 / 17 : ℚ)], ![0, (-29 / 17 : ℚ), (3 / 17 : ℚ), 0, (-56 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), (-19 / 5 : ℚ), 0, 0, -2], ![0, (-11 / 5 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .yy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-19 / 8 : ℚ), 0, 0, -2], ![(-1 / 8 : ℚ), (-5 / 4 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 40 : ℚ), (-101 / 40 : ℚ), 0, (-29 / 40 : ℚ), (7 / 20 : ℚ)], ![(1 / 2 : ℚ), (-13 / 10 : ℚ), (3 / 40 : ℚ), (-91 / 40 : ℚ), (-11 / 40 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 32 : ℚ), (-69 / 32 : ℚ), (-1 / 32 : ℚ), (-5 / 16 : ℚ), (3 / 16 : ℚ)], ![(7 / 32 : ℚ), (-35 / 32 : ℚ), 0, (-57 / 32 : ℚ), (1 / 32 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-31 / 12 : ℚ), 0, (-1 / 4 : ℚ), 0], ![0, (-4 / 3 : ℚ), (1 / 12 : ℚ), (-25 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-59 / 26 : ℚ), 0, (-1 / 13 : ℚ), 0], ![(1 / 26 : ℚ), (-15 / 13 : ℚ), (1 / 26 : ℚ), (-7 / 4 : ℚ), (-2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-7 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-28 / 11 : ℚ), 0, (-3 / 11 : ℚ), 0], ![0, (-14 / 11 : ℚ), (1 / 11 : ℚ), (-23 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-31 / 12 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 12 : ℚ)], ![0, (-4 / 3 : ℚ), (1 / 12 : ℚ), (-25 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-31 / 12 : ℚ), 0, (-1 / 4 : ℚ), (-5 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), (1 / 12 : ℚ), (-25 / 12 : ℚ), (-13 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-25 / 12 : ℚ), 0, (-19 / 18 : ℚ), (5 / 36 : ℚ)], ![(11 / 36 : ℚ), (-13 / 12 : ℚ), 0, (-19 / 9 : ℚ), (-1 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 44 : ℚ), (-91 / 44 : ℚ), 0, (-23 / 22 : ℚ), (3 / 11 : ℚ)], ![(15 / 44 : ℚ), (-47 / 44 : ℚ), 0, (-23 / 11 : ℚ), (3 / 44 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-37 / 17 : ℚ), 0, (-19 / 17 : ℚ), (-9 / 17 : ℚ)], ![0, (-20 / 17 : ℚ), 0, (-38 / 17 : ℚ), (-6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, (-4 / 3 : ℚ), 0], ![(1 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-8 / 3 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (-9 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-3 / 8 : ℚ), (-9 / 8 : ℚ), 0, (-5 / 2 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-9 / 4 : ℚ), 0, (-7 / 6 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, (-7 / 3 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 7 : ℚ), (-17 / 7 : ℚ), 0, (-9 / 7 : ℚ), (-20 / 7 : ℚ)], ![0, (-10 / 7 : ℚ), 0, (-18 / 7 : ℚ), (-37 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (37 / 18 : ℚ), (-1 / 6 : ℚ), 0, (-11 / 6 : ℚ)], ![(-43 / 36 : ℚ), (17 / 18 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), 2]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (15 / 22 : ℚ), (-1 / 22 : ℚ), 0, (-13 / 11 : ℚ)], ![(-17 / 44 : ℚ), (7 / 22 : ℚ), (-47 / 22 : ℚ), (-1 / 22 : ℚ), (1 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, (-2 / 13 : ℚ), 0, (-20 / 13 : ℚ)], ![(-6 / 13 : ℚ), (-1 / 13 : ℚ), (-32 / 13 : ℚ), (-2 / 13 : ℚ), (-18 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, (-11 / 2 : ℚ)], ![(-3 / 4 : ℚ), 0, (-11 / 4 : ℚ), (-1 / 4 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (11 / 7 : ℚ), (-1 / 7 : ℚ), 0, -5], ![(-13 / 14 : ℚ), (5 / 7 : ℚ), (-17 / 7 : ℚ), (-1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 19 : ℚ), 0, (-8 / 19 : ℚ), 0, (-116 / 19 : ℚ)], ![(-24 / 19 : ℚ), (-4 / 19 : ℚ), (-62 / 19 : ℚ), (-8 / 19 : ℚ), (-104 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-6 / 7 : ℚ), 0], ![0, -1, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (1 / 18 : ℚ), (2 / 3 : ℚ), (-11 / 18 : ℚ), (-11 / 9 : ℚ)], ![(-13 / 18 : ℚ), 0, (-13 / 9 : ℚ), (-23 / 18 : ℚ), (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 21 : ℚ), (-68 / 21 : ℚ), 0, (-32 / 21 : ℚ), (-92 / 21 : ℚ)], ![(-2 / 7 : ℚ), (-34 / 21 : ℚ), (-20 / 21 : ℚ), (-10 / 3 : ℚ), (-46 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 2, (13 / 6 : ℚ), (1 / 6 : ℚ), (-16 / 3 : ℚ)], ![(-5 / 2 : ℚ), (5 / 6 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 23 : ℚ), (4 / 23 : ℚ), (2 / 23 : ℚ), (-8 / 23 : ℚ), (-154 / 23 : ℚ)], ![(-6 / 23 : ℚ), 0, (-72 / 23 : ℚ), (-20 / 23 : ℚ), (-152 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-6 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (-14 / 11 : ℚ), (6 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 32 : ℚ), -2, (-15 / 32 : ℚ), 0, 0], ![(3 / 16 : ℚ), -1, (-57 / 32 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (-1 / 3 : ℚ), 0], ![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, -2, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (-1 / 8 : ℚ), (-3 / 16 : ℚ), (-1 / 8 : ℚ)], ![(-1 / 16 : ℚ), 0, (-5 / 16 : ℚ), (1 / 4 : ℚ), (-1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 37 : ℚ), 0, 0, (-30 / 37 : ℚ), (-42 / 37 : ℚ)], ![(-18 / 37 : ℚ), (-3 / 37 : ℚ), (-6 / 37 : ℚ), (36 / 37 : ℚ), (6 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 40 : ℚ), (-67 / 16 : ℚ), (-249 / 160 : ℚ), (189 / 160 : ℚ), (-3 / 80 : ℚ)], ![(213 / 160 : ℚ), (-341 / 160 : ℚ), (-63 / 16 : ℚ), (-177 / 160 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 26 : ℚ), -2, (-6 / 13 : ℚ), 0, 0], ![(3 / 26 : ℚ), -1, (-93 / 52 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), -1, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (9 / 4 : ℚ), (3 / 16 : ℚ), (-31 / 16 : ℚ), (31 / 16 : ℚ)], ![(-31 / 16 : ℚ), (17 / 16 : ℚ), 0, 0, (31 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (-7 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-6 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (-14 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 32 : ℚ), (-131 / 32 : ℚ), (-41 / 32 : ℚ), (37 / 32 : ℚ), 0], ![(19 / 16 : ℚ), (-33 / 16 : ℚ), (-119 / 32 : ℚ), (1 / 32 : ℚ), (1 / 64 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-3 / 7 : ℚ), 0, 0], ![(3 / 14 : ℚ), -1, (-51 / 28 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-7 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-28 / 11 : ℚ), (-3 / 11 : ℚ), 0, (-42 / 11 : ℚ)], ![0, (-14 / 11 : ℚ), (-23 / 11 : ℚ), (1 / 11 : ℚ), (-21 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-31 / 12 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), (-25 / 12 : ℚ), (1 / 12 : ℚ), (-13 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-26 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-14 / 5 : ℚ), (-43 / 10 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (4 / 5 : ℚ), 0, (1 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-3 / 5 : ℚ), (2 / 5 : ℚ), (-13 / 10 : ℚ), (-1 / 2 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (10 / 9 : ℚ), (1 / 18 : ℚ), (4 / 9 : ℚ), (-13 / 9 : ℚ)], ![(-2 / 3 : ℚ), (1 / 2 : ℚ), 0, (-7 / 6 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-25 / 6 : ℚ), (-5 / 24 : ℚ), (-9 / 8 : ℚ), 0], ![(-1 / 24 : ℚ), (-17 / 8 : ℚ), (-41 / 12 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), -2, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, (-10 / 3 : ℚ), (2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-16 / 3 : ℚ), (-5 / 3 : ℚ), (-2 / 3 : ℚ), 0], ![(-1 / 3 : ℚ), (-8 / 3 : ℚ), (-31 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-8 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-6 / 11 : ℚ), (-28 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 23 : ℚ), -4, (-21 / 23 : ℚ), 0, 0], ![(3 / 23 : ℚ), -2, (-165 / 46 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 21 : ℚ), (-32 / 7 : ℚ), (-10 / 21 : ℚ), 0, (-8 / 21 : ℚ)], ![(-2 / 21 : ℚ), (-50 / 21 : ℚ), (-26 / 7 : ℚ), (2 / 21 : ℚ), (-4 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .xy), (.xx, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-8 / 13 : ℚ), (-2 / 13 : ℚ), (-4 / 13 : ℚ), (-6 / 13 : ℚ)], ![0, (-5 / 13 : ℚ), (2 / 13 : ℚ), (-6 / 13 : ℚ), (-7 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 31 : ℚ), 0, 0, (6 / 31 : ℚ), (-24 / 31 : ℚ)], ![(-12 / 31 : ℚ), (-3 / 31 : ℚ), (-6 / 31 : ℚ), (3 / 31 : ℚ), (30 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-3 / 8 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 8 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ), (-5 / 16 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), 0, 0, 0, (-16 / 5 : ℚ)], ![(-8 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-2 / 5 : ℚ), (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-16 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 3 : ℚ), (-4 / 9 : ℚ)], ![0, (-10 / 9 : ℚ), (-4 / 3 : ℚ), (-14 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, (-5 / 4 : ℚ)], ![(1 / 4 : ℚ), -1, 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 2, -2, -2, 0], ![(-7 / 4 : ℚ), 1, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -1, 0, -1], ![(-1 / 4 : ℚ), 0, 0, -1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), -1, 1, 0], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), 0, (-8 / 15 : ℚ), (2 / 15 : ℚ), (-2 / 3 : ℚ)], ![(-2 / 5 : ℚ), (-1 / 15 : ℚ), (2 / 15 : ℚ), 0, (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (2 / 11 : ℚ), (-6 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-7 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (2 / 11 : ℚ), (-6 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 28 : ℚ), (-65 / 28 : ℚ), 0, (-17 / 14 : ℚ), (2 / 7 : ℚ)], ![(1 / 2 : ℚ), (-17 / 14 : ℚ), 0, (-17 / 14 : ℚ), (-5 / 28 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), 0, (-7 / 6 : ℚ), (5 / 12 : ℚ)], ![(1 / 2 : ℚ), (-7 / 6 : ℚ), 0, (-7 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, (-4 / 3 : ℚ), 0], ![(1 / 6 : ℚ), (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 4 : ℚ), (-7 / 2 : ℚ), 0, (-5 / 2 : ℚ), (-3 / 2 : ℚ)], ![0, (-7 / 4 : ℚ), 0, (-5 / 2 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-11 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, (-3 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 77 : ℚ), (188 / 77 : ℚ), (-178 / 77 : ℚ), (6 / 77 : ℚ), (-16 / 11 : ℚ)], ![(-100 / 77 : ℚ), (13 / 11 : ℚ), (-50 / 11 : ℚ), 0, (28 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 21 : ℚ), (2 / 3 : ℚ), (-46 / 21 : ℚ), (1 / 21 : ℚ), (-7 / 6 : ℚ)], ![(-13 / 21 : ℚ), (13 / 42 : ℚ), (-13 / 3 : ℚ), 0, (1 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-37 / 15 : ℚ), 0, (-13 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-4 / 3 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (-12 / 17 : ℚ), (-52 / 17 : ℚ), 0, (-100 / 17 : ℚ)], ![(-12 / 17 : ℚ), (-6 / 17 : ℚ), (-98 / 17 : ℚ), (-6 / 17 : ℚ), (-50 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 28 : ℚ), (-5 / 2 : ℚ), 0, (-65 / 28 : ℚ), (-9 / 28 : ℚ)], ![(-3 / 28 : ℚ), (-47 / 28 : ℚ), (3 / 28 : ℚ), (-17 / 7 : ℚ), (3 / 28 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (62 / 33 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ)], ![(-37 / 33 : ℚ), (28 / 33 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (21 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (13 / 24 : ℚ), (-1 / 24 : ℚ), 0, (-9 / 8 : ℚ)], ![(-5 / 16 : ℚ), (1 / 4 : ℚ), (-25 / 12 : ℚ), (-1 / 24 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0, (-28 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, (-14 / 5 : ℚ), (-2 / 5 : ℚ), (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (9 / 7 : ℚ), (-1 / 7 : ℚ), 0, (-33 / 7 : ℚ)], ![(-11 / 14 : ℚ), (4 / 7 : ℚ), (-16 / 7 : ℚ), (-1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0], ![0, -1, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (1 / 2 : ℚ), (1 / 10 : ℚ), (-38 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0, (-19 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, 0, (-8 / 13 : ℚ), (-6 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-1 / 13 : ℚ), (-2 / 13 : ℚ), (10 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, (-7 / 6 : ℚ), 0, 0], ![(1 / 3 : ℚ), -1, (-7 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 12 : ℚ), (-1 / 4 : ℚ), 0], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 4 : ℚ), (5 / 12 : ℚ), (5 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0], ![0, (-1 / 2 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![0, (-1 / 4 : ℚ), (-3 / 4 : ℚ), (3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 31 : ℚ), 0, 0, (-24 / 31 : ℚ), (-30 / 31 : ℚ)], ![(-12 / 31 : ℚ), (-3 / 31 : ℚ), (-6 / 31 : ℚ), (30 / 31 : ℚ), (6 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 28 : ℚ), (-59 / 14 : ℚ), (-121 / 56 : ℚ), (69 / 56 : ℚ), 0], ![(81 / 56 : ℚ), (-121 / 56 : ℚ), (-121 / 56 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, (-5 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), -1, (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 10 : ℚ), (-1 / 5 : ℚ), 0, 0], ![(1 / 10 : ℚ), (-1 / 5 : ℚ), (-3 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0], ![0, (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-3 / 7 : ℚ), (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (1 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (-6 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-25 / 6 : ℚ), (-17 / 8 : ℚ), (11 / 8 : ℚ), 0], ![(35 / 24 : ℚ), (-17 / 8 : ℚ), (-17 / 8 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-5 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), -1, (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-9 / 2 : ℚ)], ![0, (-5 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), 0, (-8 / 9 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), 0, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -5, (-11 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-11 / 4 : ℚ), (-11 / 4 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (-6 / 5 : ℚ), (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (-2 / 3 : ℚ), 0], ![0, (-2 / 3 : ℚ), -2, (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-14 / 3 : ℚ), -3, (-2 / 3 : ℚ), 0], ![0, (-7 / 3 : ℚ), -3, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (3 / 8 : ℚ), -2, (-9 / 8 : ℚ)], ![(-7 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -4, (-5 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), -2, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, 0, (1 / 8 : ℚ)], ![(3 / 8 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), -2, 0, 0, (3 / 10 : ℚ)], ![(2 / 5 : ℚ), -1, 0, 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 3 : ℚ), -1, 0, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, 0, (-3 / 8 : ℚ)], ![(1 / 8 : ℚ), -1, 0, 0, (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, 0], ![(1 / 4 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, 0], ![(1 / 4 : ℚ), -1, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, 0, (1 / 8 : ℚ)], ![(3 / 8 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), -2, 0, 0, (3 / 10 : ℚ)], ![(2 / 5 : ℚ), -1, 0, 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 3 : ℚ), -1, 0, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), -2, 0, 0, -1], ![(1 / 6 : ℚ), -1, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, 0], ![(1 / 4 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, 0], ![(1 / 4 : ℚ), -1, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, -1, 0, (-3 / 8 : ℚ)], ![(-1 / 8 : ℚ), 0, 0, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), -2, 0, 0, (3 / 10 : ℚ)], ![(2 / 5 : ℚ), -1, 0, 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 12 : ℚ), 0, 0, -1, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, 0, 0], ![(-1 / 3 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -1, 0, -2], ![(-1 / 4 : ℚ), 0, 0, -1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, (-1 / 4 : ℚ)], ![(1 / 4 : ℚ), -1, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, 0], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, -1, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, -1, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -1, 1, -2], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (2 / 11 : ℚ), (-5 / 11 : ℚ), (-7 / 11 : ℚ), (-5 / 11 : ℚ)], ![(-3 / 11 : ℚ), 0, (2 / 11 : ℚ), (9 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 10 : ℚ), 0, 0, 0], ![(1 / 10 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (2 / 11 : ℚ), (-5 / 11 : ℚ), (-7 / 11 : ℚ), (-8 / 11 : ℚ)], ![(-3 / 11 : ℚ), 0, (2 / 11 : ℚ), (9 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 11 : ℚ), 0, 0], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(2 / 9 : ℚ), (-1 / 3 : ℚ), (2 / 9 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 20 : ℚ), 0, (-1 / 5 : ℚ)], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (1 / 10 : ℚ), 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), 0], ![0, (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 50 : ℚ), (-107 / 50 : ℚ), (-7 / 50 : ℚ), 0, (7 / 50 : ℚ)], ![(13 / 50 : ℚ), (-11 / 10 : ℚ), (-2 / 25 : ℚ), (3 / 50 : ℚ), (-2 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-29 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 24 : ℚ), (1 / 2 : ℚ)], ![(7 / 12 : ℚ), (-5 / 4 : ℚ), 0, 0, (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-36 / 11 : ℚ), 0, (-1 / 11 : ℚ), 0], ![(1 / 11 : ℚ), (-19 / 11 : ℚ), (2 / 11 : ℚ), 0, (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 40 : ℚ), (-101 / 40 : ℚ), 0, (-3 / 40 : ℚ), (7 / 20 : ℚ)], ![(1 / 2 : ℚ), (-13 / 10 : ℚ), (3 / 40 : ℚ), 0, (-11 / 40 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-31 / 12 : ℚ), 0, (-1 / 12 : ℚ), (7 / 12 : ℚ)], ![(2 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), (5 / 24 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-17 / 10 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 2 : ℚ), (-11 / 10 : ℚ), (9 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-36 / 11 : ℚ), 0, (-2 / 11 : ℚ), (8 / 11 : ℚ)], ![(5 / 11 : ℚ), (-19 / 11 : ℚ), (2 / 11 : ℚ), (5 / 11 : ℚ), (6 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-13 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ), (3 / 4 : ℚ)], ![(3 / 4 : ℚ), (-7 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 4 : ℚ), 0, 0, 0], ![0, (-3 / 2 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-13 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-7 / 4 : ℚ), 0, 0, 0]] }
]

theorem conicDetC11_checked : conicDetC11.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
