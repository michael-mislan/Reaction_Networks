import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC06 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-31 / 17 : ℚ)], ![(-2 / 17 : ℚ), (-2 / 17 : ℚ), (-2 / 17 : ℚ), (-2 / 17 : ℚ), (-27 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -5, 0, 0], ![(1 / 4 : ℚ), (9 / 4 : ℚ), (-5 / 2 : ℚ), (-21 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -4, 0, 0], ![(1 / 4 : ℚ), 2, -2, (-17 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-11 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-21 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -2, 0, (-7 / 6 : ℚ)], ![(1 / 6 : ℚ), 1, -1, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 17 : ℚ), (-2 / 17 : ℚ), (-48 / 17 : ℚ), 0, (-28 / 17 : ℚ)], ![0, (22 / 17 : ℚ), (-25 / 17 : ℚ), (2 / 17 : ℚ), (-58 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, -2, (-17 / 16 : ℚ), 0], ![(1 / 8 : ℚ), 1, -1, (-35 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -2, (-7 / 6 : ℚ), 0], ![(1 / 6 : ℚ), 1, -1, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 17 : ℚ), (-12 / 17 : ℚ), 0, (-21 / 34 : ℚ), (-41 / 34 : ℚ)], ![(-1 / 17 : ℚ), (-29 / 34 : ℚ), (-1 / 34 : ℚ), (-22 / 17 : ℚ), (-39 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -5, (-7 / 2 : ℚ), 0], ![0, 2, (-5 / 2 : ℚ), (-15 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, -4, (-21 / 10 : ℚ), 0], ![(1 / 20 : ℚ), 2, -2, (-43 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 21 : ℚ), (-29 / 21 : ℚ), 0, (-29 / 21 : ℚ), (-32 / 7 : ℚ)], ![(-4 / 21 : ℚ), (-11 / 7 : ℚ), (-2 / 21 : ℚ), (-62 / 21 : ℚ), (-94 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -2, 0, (-7 / 6 : ℚ)], ![(1 / 6 : ℚ), 1, -1, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -2, (-7 / 6 : ℚ), 0], ![(1 / 3 : ℚ), 1, -1, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -2, (-7 / 6 : ℚ), 0], ![(1 / 6 : ℚ), 1, -1, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-24 / 5 : ℚ), (-14 / 5 : ℚ), 0], ![0, 2, (-12 / 5 : ℚ), (-16 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, -4, (-12 / 5 : ℚ), 0], ![(1 / 5 : ℚ), 2, -2, (-14 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -2, 0, 0], ![(1 / 3 : ℚ), 1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -2, 0, 0], ![(1 / 4 : ℚ), 1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(1 / 3 : ℚ), 1, -1, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, -2, 0, (-3 / 10 : ℚ)], ![(1 / 10 : ℚ), 1, -1, 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -2, 0, -2], ![(1 / 4 : ℚ), 1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -3, 0, (1 / 2 : ℚ)], ![(5 / 6 : ℚ), (3 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, -2, -1], ![(-1 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-17 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 2 : ℚ), (9 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ), -4], ![(-1 / 5 : ℚ), 0, 0, (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-13 / 6 : ℚ), 0, (1 / 12 : ℚ)], ![(1 / 4 : ℚ), (13 / 12 : ℚ), (-13 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-9 / 4 : ℚ), 0, (1 / 8 : ℚ)], ![(1 / 4 : ℚ), (9 / 8 : ℚ), (-9 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ), -4], ![(-1 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -2, (-1 / 6 : ℚ), 0], ![(1 / 3 : ℚ), 1, -1, (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -2, (-1 / 4 : ℚ), 0], ![(1 / 4 : ℚ), 1, -1, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, -4, (-2 / 3 : ℚ), 0], ![(1 / 3 : ℚ), 2, -2, (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -2, 0, 0], ![0, 1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, -4, -1, 0], ![(1 / 6 : ℚ), 2, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, -2, 0, (-25 / 12 : ℚ)], ![(1 / 6 : ℚ), 1, -1, 0, (-25 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -2, 0, -2], ![(1 / 3 : ℚ), 1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -2, 0, (-7 / 3 : ℚ)], ![(1 / 3 : ℚ), 1, -1, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -2, 0, (-9 / 4 : ℚ)], ![(1 / 4 : ℚ), 1, -1, 0, (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -2, 0, -2], ![(1 / 4 : ℚ), 1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -2, 0, (-5 / 2 : ℚ)], ![(1 / 4 : ℚ), 1, -1, 0, (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -5, 0, 0], ![(1 / 4 : ℚ), (9 / 4 : ℚ), (-5 / 2 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -4, 0, 0], ![(1 / 4 : ℚ), 2, -2, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-26 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), -5]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-22 / 5 : ℚ), (-7 / 5 : ℚ), 0], ![0, 2, (-11 / 5 : ℚ), (-8 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, -4, (-7 / 5 : ℚ), 0], ![(1 / 5 : ℚ), 2, -2, (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-11 / 7 : ℚ)], ![(2 / 7 : ℚ), (9 / 7 : ℚ), (2 / 7 : ℚ), (-24 / 7 : ℚ), (-24 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), -3, -3]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(1 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ), (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(1 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), (-11 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-11 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (9 / 7 : ℚ), (-24 / 7 : ℚ), (-24 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), -3, -3, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-25 / 8 : ℚ), 0], ![(3 / 8 : ℚ), (19 / 8 : ℚ), -7, -7, (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-16 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (12 / 5 : ℚ), (-36 / 5 : ℚ), (-36 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-38 / 13 : ℚ), 0], ![(4 / 13 : ℚ), (30 / 13 : ℚ), (-84 / 13 : ℚ), (-84 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), -3, (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(1 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-11 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (9 / 7 : ℚ), (-24 / 7 : ℚ), (-13 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), -3, (-8 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(1 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (11 / 5 : ℚ), (-28 / 5 : ℚ), -3, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-20 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (16 / 7 : ℚ), (-44 / 7 : ℚ), (-24 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-10 / 3 : ℚ), 0], ![(4 / 9 : ℚ), (22 / 9 : ℚ), (-68 / 9 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, (1 / 3 : ℚ), -4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (1 / 3 : ℚ), 4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (-1 / 3 : ℚ), 4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, (-1 / 3 : ℚ), -4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-10 / 3 : ℚ)], ![(-4 / 9 : ℚ), (5 / 9 : ℚ), (-4 / 9 : ℚ), (-40 / 9 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, 0], ![(2 / 9 : ℚ), (20 / 9 : ℚ), 0, (-70 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-10 / 3 : ℚ)], ![(-4 / 9 : ℚ), (5 / 9 : ℚ), (-4 / 9 : ℚ), (-40 / 9 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(1 / 10 : ℚ), (21 / 10 : ℚ), (-34 / 5 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-10 / 7 : ℚ), 0], ![(1 / 7 : ℚ), (15 / 7 : ℚ), (-50 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(2 / 9 : ℚ), (20 / 9 : ℚ), (-70 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 3 : ℚ), (-3 / 2 : ℚ)], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ), (-7 / 2 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-7 / 5 : ℚ)], ![0, 1, 0, (-17 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-11 / 6 : ℚ), (-5 / 3 : ℚ), 0], ![(1 / 3 : ℚ), (4 / 3 : ℚ), (-23 / 6 : ℚ), (-11 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 3 : ℚ), (-3 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (-7 / 2 : ℚ), (-5 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ), (-7 / 5 : ℚ), 0], ![0, 1, (-17 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-34 / 11 : ℚ), (-30 / 11 : ℚ), 0], ![0, 2, (-72 / 11 : ℚ), (-34 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-32 / 9 : ℚ), (-28 / 9 : ℚ), 0], ![(2 / 9 : ℚ), (20 / 9 : ℚ), (-68 / 9 : ℚ), (-32 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-13 / 4 : ℚ), (-11 / 4 : ℚ), 0], ![0, (7 / 4 : ℚ), -7, (-11 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), 0, 0, (-11 / 7 : ℚ)], ![(1 / 7 : ℚ), (8 / 7 : ℚ), (1 / 7 : ℚ), (1 / 7 : ℚ), (-23 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (-9 / 5 : ℚ)], ![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), 0, (-18 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .xy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, 0, -2], ![(1 / 8 : ℚ), (9 / 8 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .yy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), -2, 2, (1 / 14 : ℚ)], ![-2, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 3 : ℚ), (-1 / 6 : ℚ)], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ), (-7 / 2 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-20 / 11 : ℚ), (1 / 11 : ℚ), (-20 / 11 : ℚ)], ![(-7 / 11 : ℚ), (-7 / 11 : ℚ), (2 / 11 : ℚ), 0, (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), 0, (-15 / 11 : ℚ), (-1 / 11 : ℚ)], ![(1 / 11 : ℚ), (12 / 11 : ℚ), (12 / 11 : ℚ), (-31 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-11 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (9 / 7 : ℚ), (2 / 7 : ℚ), (-24 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-1 / 9 : ℚ), 0, (-13 / 9 : ℚ), (-1 / 3 : ℚ)], ![(1 / 9 : ℚ), (10 / 9 : ℚ), (1 / 9 : ℚ), (-34 / 9 : ℚ), (-4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ), (-18 / 11 : ℚ)], ![(2 / 11 : ℚ), (13 / 11 : ℚ), (2 / 11 : ℚ), (-40 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ), (-20 / 11 : ℚ)], ![(2 / 11 : ℚ), (13 / 11 : ℚ), (2 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ), (-16 / 11 : ℚ)], ![(2 / 11 : ℚ), (13 / 11 : ℚ), (2 / 11 : ℚ), (-40 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)], ![0, 1, (1 / 5 : ℚ), 0, (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.y, .xy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, -2], ![0, 1, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.y, .yy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, -2], ![(-1 / 8 : ℚ), (7 / 8 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-13 / 8 : ℚ), 0], ![(1 / 4 : ℚ), (5 / 4 : ℚ), (1 / 8 : ℚ), (-27 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 6 : ℚ)], ![0, 1, (1 / 6 : ℚ), (-19 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), 0], ![0, 1, (1 / 6 : ℚ), (-19 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), -3, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-4 / 3 : ℚ), 0], ![(-1 / 6 : ℚ), (5 / 6 : ℚ), 0, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), -2], ![0, 1, (1 / 6 : ℚ), (-19 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-13 / 6 : ℚ)], ![0, 1, (1 / 6 : ℚ), (-19 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-11 / 6 : ℚ)], ![0, 1, (1 / 6 : ℚ), (-19 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-3 / 17 : ℚ), 0, (-32 / 17 : ℚ), 0], ![(6 / 17 : ℚ), (23 / 17 : ℚ), 0, (-64 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-9 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), 0, (-18 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0], ![0, 1, 0, (-16 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(1 / 3 : ℚ), (4 / 3 : ℚ), 0, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 11 : ℚ), (-5 / 11 : ℚ), 0, (-21 / 11 : ℚ), (-32 / 11 : ℚ)], ![0, (6 / 11 : ℚ), 0, (-42 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-11 / 4 : ℚ)], ![0, (3 / 4 : ℚ), 0, -3, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-11 / 7 : ℚ), (-16 / 7 : ℚ)], ![(-2 / 7 : ℚ), (5 / 7 : ℚ), 0, (-22 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-11 / 6 : ℚ), 0], ![(1 / 3 : ℚ), (4 / 3 : ℚ), (-2 / 3 : ℚ), (-23 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0], ![(2 / 11 : ℚ), (13 / 11 : ℚ), (-9 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![0, 1, -1, (-19 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 25 : ℚ), (-12 / 25 : ℚ), (-12 / 25 : ℚ), (-86 / 25 : ℚ), 0], ![0, 2, 0, (-184 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (-32 / 9 : ℚ), 0], ![(2 / 9 : ℚ), (20 / 9 : ℚ), (2 / 9 : ℚ), (-68 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-54 / 17 : ℚ), 0], ![0, (30 / 17 : ℚ), (-4 / 17 : ℚ), (-116 / 17 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), 0, (-10 / 7 : ℚ), 0], ![0, 1, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-21 / 16 : ℚ), 0], ![(-1 / 16 : ℚ), (15 / 16 : ℚ), (-7 / 8 : ℚ), (-51 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 20 : ℚ), (-16 / 15 : ℚ), 0, (-47 / 15 : ℚ), (-83 / 60 : ℚ)], ![(-3 / 20 : ℚ), (17 / 20 : ℚ), (-3 / 20 : ℚ), (-77 / 12 : ℚ), (-37 / 60 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-5 / 3 : ℚ), (-32 / 9 : ℚ), 0], ![(2 / 9 : ℚ), (20 / 9 : ℚ), 0, (-70 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-11 / 12 : ℚ), 0, (-17 / 6 : ℚ), (-7 / 6 : ℚ)], ![(-1 / 3 : ℚ), (2 / 3 : ℚ), (-1 / 3 : ℚ), -6, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-23 / 13 : ℚ), 0, 0], ![(4 / 13 : ℚ), (17 / 13 : ℚ), (-48 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-13 / 8 : ℚ), 0, 0], ![(1 / 4 : ℚ), (5 / 4 : ℚ), (-27 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (5 / 4 : ℚ), (-13 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![0, 1, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-17 / 12 : ℚ), 0, (-5 / 3 : ℚ)], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (-35 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-11 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(1 / 3 : ℚ), (4 / 3 : ℚ), (-23 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 24 : ℚ), (-29 / 24 : ℚ), 0, (-43 / 24 : ℚ)], ![(1 / 12 : ℚ), (13 / 12 : ℚ), (-59 / 24 : ℚ), (1 / 24 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-3 / 2 : ℚ), 0, (-1 / 8 : ℚ)], ![(1 / 8 : ℚ), (9 / 8 : ℚ), (-25 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (5 / 4 : ℚ), (-13 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![0, 1, (-11 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-18 / 11 : ℚ)], ![(2 / 11 : ℚ), (13 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-20 / 11 : ℚ)], ![(2 / 11 : ℚ), (13 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-16 / 11 : ℚ)], ![(2 / 11 : ℚ), (13 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), -3, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (5 / 6 : ℚ), (-10 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), 0, -2], ![0, 1, (-19 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), 0, (-13 / 6 : ℚ)], ![0, 1, (-19 / 6 : ℚ), (1 / 6 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 4 : ℚ), 0, (-23 / 12 : ℚ)], ![0, 1, (-31 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, 0], ![(1 / 3 : ℚ), (7 / 3 : ℚ), (-20 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, 0], ![(1 / 3 : ℚ), (7 / 3 : ℚ), (-20 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-38 / 13 : ℚ), 0, 0], ![(4 / 13 : ℚ), (30 / 13 : ℚ), (-84 / 13 : ℚ), (-20 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-28 / 11 : ℚ), (-15 / 11 : ℚ), 0], ![0, 2, (-65 / 11 : ℚ), (-17 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-25 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (19 / 9 : ℚ), (-19 / 3 : ℚ), (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-17 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![0, (11 / 6 : ℚ), (-20 / 3 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-32 / 9 : ℚ), 0, (4 / 9 : ℚ)], ![(2 / 9 : ℚ), (20 / 9 : ℚ), (-68 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ), 0, (8 / 17 : ℚ)], ![0, 2, (-124 / 17 : ℚ), (4 / 17 : ℚ), (12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-36 / 11 : ℚ), 0, (-2 / 11 : ℚ)], ![(2 / 11 : ℚ), (24 / 11 : ℚ), (-76 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 21 : ℚ), (-8 / 21 : ℚ), (-10 / 3 : ℚ), 0, 0], ![(4 / 21 : ℚ), (46 / 21 : ℚ), (-148 / 21 : ℚ), (8 / 21 : ℚ), (4 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-17 / 6 : ℚ), 0, (-1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (11 / 6 : ℚ), -6, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .xy), (.xx, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-17 / 6 : ℚ)], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 3 : ℚ), (-35 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), (-36 / 11 : ℚ), 0], ![(4 / 11 : ℚ), (15 / 11 : ℚ), (-21 / 11 : ℚ), (-37 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), (-17 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (-5 / 3 : ℚ), (-35 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (-24 / 11 : ℚ), (-47 / 11 : ℚ), 0], ![0, 2, (-25 / 11 : ℚ), (-95 / 22 : ℚ), (17 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-28 / 9 : ℚ), (-52 / 9 : ℚ), 0], ![(2 / 9 : ℚ), (20 / 9 : ℚ), (-32 / 9 : ℚ), -6, (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)], ![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), 0, (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .xx), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0, -2], ![(1 / 6 : ℚ), (7 / 6 : ℚ), 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .xy), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0, -2], ![(1 / 6 : ℚ), (7 / 6 : ℚ), 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .yy), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), -2, 2, (1 / 6 : ℚ)], ![-2, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), 0, (-11 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (9 / 7 : ℚ), (1 / 7 : ℚ), (-12 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-4 / 3 : ℚ), (1 / 3 : ℚ)], ![(1 / 3 : ℚ), (7 / 6 : ℚ), (2 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), (-8 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 4 : ℚ)], ![(1 / 12 : ℚ), (13 / 12 : ℚ), (1 / 12 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ), (-11 / 6 : ℚ)], ![(1 / 12 : ℚ), (13 / 12 : ℚ), (1 / 12 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 3 : ℚ), (-25 / 6 : ℚ)], ![0, 0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-7 / 6 : ℚ), (-5 / 3 : ℚ)], ![(1 / 12 : ℚ), (13 / 12 : ℚ), (5 / 6 : ℚ), (-7 / 6 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-9 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (7 / 5 : ℚ), 0, (-9 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), 0, (-8 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(1 / 3 : ℚ), (4 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), -2], ![0, 1, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-15 / 7 : ℚ), (-18 / 7 : ℚ)], ![0, 1, 0, (-15 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (-1 / 22 : ℚ), 0, (-47 / 22 : ℚ), (9 / 44 : ℚ)], ![(13 / 44 : ℚ), (57 / 44 : ℚ), (1 / 22 : ℚ), (-24 / 11 : ℚ), (-7 / 44 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 24 : ℚ), 0, (-17 / 8 : ℚ), (1 / 4 : ℚ)], ![(7 / 24 : ℚ), (31 / 24 : ℚ), (1 / 24 : ℚ), (-13 / 6 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), -5, (-1 / 5 : ℚ), (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 30 : ℚ), (-1 / 30 : ℚ), (-21 / 10 : ℚ), 0, (-94 / 15 : ℚ)], ![(-1 / 15 : ℚ), (-17 / 15 : ℚ), (-25 / 6 : ℚ), (-1 / 30 : ℚ), (-71 / 30 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), 0, (-32 / 13 : ℚ), (-32 / 13 : ℚ)], ![0, (11 / 13 : ℚ), (2 / 13 : ℚ), (-34 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0], ![(4 / 11 : ℚ), (15 / 11 : ℚ), (-7 / 11 : ℚ), (-21 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (-5 / 6 : ℚ), (-5 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-30 / 11 : ℚ), 0], ![0, 2, 0, (-34 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (-28 / 9 : ℚ), 0], ![(2 / 9 : ℚ), (20 / 9 : ℚ), (2 / 9 : ℚ), (-32 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0], ![0, 1, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-4 / 3 : ℚ), 0, (-7 / 3 : ℚ), (-7 / 6 : ℚ)], ![(-1 / 6 : ℚ), (5 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-3 / 2 : ℚ), (-17 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (13 / 6 : ℚ), 0, (-23 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 3 : ℚ), 0, (1 / 6 : ℚ)], ![(1 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-9 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (7 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (5 / 4 : ℚ), (-7 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![0, 1, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-14 / 11 : ℚ)], ![(4 / 11 : ℚ), (15 / 11 : ℚ), (-21 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-16 / 11 : ℚ)], ![(4 / 11 : ℚ), (15 / 11 : ℚ), (-21 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-9 / 5 : ℚ), 0, -1], ![(2 / 5 : ℚ), (7 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![0, 1, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 4 : ℚ), 0, (-11 / 6 : ℚ)], ![(1 / 12 : ℚ), (13 / 12 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 4 : ℚ), 0, (-23 / 12 : ℚ)], ![(1 / 12 : ℚ), (13 / 12 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-13 / 10 : ℚ), 0, (-17 / 10 : ℚ)], ![(1 / 10 : ℚ), (11 / 10 : ℚ), (-13 / 10 : ℚ), (1 / 10 : ℚ), (-17 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (5 / 4 : ℚ), (-3 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), 0, -2], ![0, 1, (-3 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 3 : ℚ), 0, (-7 / 3 : ℚ)], ![0, 1, (-5 / 3 : ℚ), 0, 2]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (11 / 5 : ℚ), -3, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-17 / 7 : ℚ), 0, 0], ![(1 / 7 : ℚ), (15 / 7 : ℚ), (-19 / 7 : ℚ), (-5 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, 0], ![(1 / 3 : ℚ), (7 / 3 : ℚ), -3, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-26 / 11 : ℚ), (-15 / 11 : ℚ), 0], ![0, 2, (-28 / 11 : ℚ), (-17 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-23 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (19 / 9 : ℚ), (-25 / 9 : ℚ), (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-32 / 11 : ℚ), 0, (4 / 11 : ℚ)], ![(2 / 11 : ℚ), (24 / 11 : ℚ), (-36 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-22 / 7 : ℚ), 0, 0], ![0, 2, (-22 / 7 : ℚ), (2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-29 / 12 : ℚ), 0, (-1 / 12 : ℚ)], ![(1 / 12 : ℚ), (25 / 12 : ℚ), (-31 / 12 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-24 / 7 : ℚ), 0, 0], ![(2 / 7 : ℚ), (16 / 7 : ℚ), (-24 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 10 : ℚ), (-1 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (4 / 5 : ℚ), (1 / 10 : ℚ), (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0, -1], ![(1 / 6 : ℚ), (7 / 6 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0, -1], ![(1 / 6 : ℚ), (7 / 6 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 1, -1, (1 / 6 : ℚ)], ![1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.y, .yy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), -1, 1, (1 / 6 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, 0], ![0, 1, (1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 3 : ℚ), (-1 / 3 : ℚ)], ![(1 / 3 : ℚ), (4 / 3 : ℚ), (1 / 3 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (1 / 3 : ℚ), (-1 / 3 : ℚ)], ![(1 / 6 : ℚ), (7 / 6 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (9 / 10 : ℚ), (1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-1 / 18 : ℚ), (5 / 18 : ℚ), (-10 / 9 : ℚ), 0], ![(1 / 3 : ℚ), 2, (1 / 18 : ℚ), (-7 / 6 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (11 / 24 : ℚ), (-29 / 24 : ℚ), 0], ![(13 / 24 : ℚ), (49 / 24 : ℚ), (1 / 12 : ℚ), (-31 / 24 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), -1, 0], ![(1 / 4 : ℚ), (15 / 8 : ℚ), (1 / 8 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, -1], ![(-1 / 8 : ℚ), (-9 / 8 : ℚ), 0, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (2 / 3 : ℚ), (-2 / 3 : ℚ)], ![(2 / 3 : ℚ), (5 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![0, 1, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(1 / 4 : ℚ), (5 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 2 : ℚ), 0], ![0, 2, 0, (-3 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-12 / 7 : ℚ), 0], ![(1 / 7 : ℚ), (15 / 7 : ℚ), 0, (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -1], ![1, 2, 0, -1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -1], ![1, 2, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 4 : ℚ), (1 / 4 : ℚ), -2, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-9 / 7 : ℚ), 0], ![0, 2, (-1 / 7 : ℚ), (-10 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-1 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (19 / 9 : ℚ), 0, (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-15 / 11 : ℚ), 0], ![0, 2, 0, (-17 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (19 / 9 : ℚ), (1 / 9 : ℚ), (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-9 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)], ![(3 / 10 : ℚ), (-1 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, -1, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), 0, 0], ![(1 / 10 : ℚ), (-9 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, 0], ![0, -1, (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(-1 / 8 : ℚ), (-9 / 8 : ℚ), 0, 0, (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 7 : ℚ), 1, (-1 / 7 : ℚ), -1, (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), 2, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 7 : ℚ), 1, (-2 / 7 : ℚ), -1, (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-13 / 9 : ℚ), 0, (-13 / 9 : ℚ), (-13 / 18 : ℚ)], ![(-1 / 18 : ℚ), (17 / 18 : ℚ), (-1 / 18 : ℚ), (-3 / 2 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), -1, (-4 / 3 : ℚ), 0], ![(1 / 12 : ℚ), 2, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(5 / 4 : ℚ), (9 / 4 : ℚ), (-5 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), (-4 / 3 : ℚ), 0], ![(4 / 3 : ℚ), (7 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(3 / 2 : ℚ), (5 / 2 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(5 / 4 : ℚ), (9 / 4 : ℚ), 0, (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), (-4 / 3 : ℚ), 0], ![(4 / 3 : ℚ), (7 / 3 : ℚ), 0, (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(3 / 2 : ℚ), (5 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0]] }
]

theorem conicDetC06_checked : conicDetC06.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
