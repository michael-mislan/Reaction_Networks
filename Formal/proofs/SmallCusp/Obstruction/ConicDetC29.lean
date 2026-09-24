import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC29 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 7 : ℚ), 1, (1 / 7 : ℚ), 0, -3], ![0, (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-10 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (-1 / 20 : ℚ), (23 / 20 : ℚ), (1 / 20 : ℚ), (-1 / 20 : ℚ)], ![(-11 / 10 : ℚ), 0, 0, (-11 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, 0, (-13 / 4 : ℚ)], ![0, 0, 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 13 : ℚ), 0, 0, (1 / 13 : ℚ), (-22 / 13 : ℚ)], ![(-37 / 52 : ℚ), (-19 / 52 : ℚ), (-193 / 52 : ℚ), (-14 / 13 : ℚ), (-21 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 13 : ℚ), 0, (1 / 13 : ℚ), (1 / 13 : ℚ), (-22 / 13 : ℚ)], ![(-37 / 52 : ℚ), (-19 / 52 : ℚ), (-53 / 13 : ℚ), (-14 / 13 : ℚ), (-21 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (9 / 8 : ℚ), (-3 / 4 : ℚ), (1 / 8 : ℚ), (-25 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-7 / 8 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), -3], ![0, 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), 0, 0, (-11 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), (3 / 2 : ℚ), (11 / 12 : ℚ), (1 / 12 : ℚ), (-43 / 12 : ℚ)], ![0, (-1 / 12 : ℚ), -1, 0, (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 4 : ℚ), (25 / 12 : ℚ), (5 / 3 : ℚ), (5 / 4 : ℚ), (-16 / 3 : ℚ)], ![(13 / 12 : ℚ), (-1 / 6 : ℚ), 0, (13 / 12 : ℚ), (-31 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 12 : ℚ), 2, (1 / 12 : ℚ), (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(1 / 2 : ℚ), (-1 / 12 : ℚ), 0, (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, (-1 / 4 : ℚ), 0, (-13 / 4 : ℚ)], ![0, 0, 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(11 / 20 : ℚ), (41 / 20 : ℚ), (1 / 20 : ℚ), (-1 / 4 : ℚ), (-22 / 5 : ℚ)], ![(9 / 20 : ℚ), 0, 0, 0, (-43 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(11 / 10 : ℚ), (21 / 10 : ℚ), (1 / 5 : ℚ), (-1 / 2 : ℚ), (-24 / 5 : ℚ)], ![(9 / 10 : ℚ), 0, 0, 0, (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 5 : ℚ), (21 / 10 : ℚ), (1 / 10 : ℚ), (-3 / 10 : ℚ), (-9 / 2 : ℚ)], ![(1 / 2 : ℚ), 0, 0, 0, (-11 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 6 : ℚ), 2, (1 / 12 : ℚ), (-7 / 6 : ℚ), (-17 / 3 : ℚ)], ![(7 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 4 : ℚ), (25 / 12 : ℚ), (1 / 6 : ℚ), (-5 / 4 : ℚ), (-35 / 6 : ℚ)], ![(5 / 4 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 4 : ℚ), (-31 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 6 : ℚ), 2, 0, (-7 / 6 : ℚ), (-17 / 3 : ℚ)], ![(7 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 4 : ℚ), (25 / 12 : ℚ), (1 / 6 : ℚ), 0, (-16 / 3 : ℚ)], ![(13 / 12 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (-31 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 12 : ℚ), 2, (1 / 24 : ℚ), (1 / 12 : ℚ), (-55 / 12 : ℚ)], ![(1 / 2 : ℚ), (-1 / 12 : ℚ), 0, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 12 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ), (-31 / 12 : ℚ)], ![(-1 / 2 : ℚ), (-7 / 12 : ℚ), (-49 / 12 : ℚ), (-25 / 12 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 4 : ℚ), (25 / 12 : ℚ), (1 / 6 : ℚ), (1 / 4 : ℚ), (-16 / 3 : ℚ)], ![(13 / 12 : ℚ), (-1 / 6 : ℚ), 0, (1 / 12 : ℚ), (-31 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 12 : ℚ), 2, (1 / 12 : ℚ), (1 / 24 : ℚ), (-55 / 12 : ℚ)], ![(1 / 2 : ℚ), (-1 / 12 : ℚ), 0, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 34 : ℚ), 0, (-3 / 34 : ℚ), (-37 / 17 : ℚ), (4 / 17 : ℚ)], ![(24 / 17 : ℚ), 0, (-3 / 34 : ℚ), (-74 / 17 : ℚ), (-5 / 34 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-11 / 5 : ℚ), (3 / 10 : ℚ)], ![(7 / 5 : ℚ), 0, (-1 / 10 : ℚ), (-22 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-11 / 5 : ℚ), (2 / 5 : ℚ)], ![(7 / 5 : ℚ), 0, (-1 / 10 : ℚ), (-22 / 5 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 2 : ℚ), 0], ![(5 / 4 : ℚ), 0, (1 / 4 : ℚ), -5, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, (-2 / 11 : ℚ), (-26 / 11 : ℚ), (-26 / 11 : ℚ)], ![(9 / 11 : ℚ), 0, (-2 / 11 : ℚ), (-52 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-5 / 2 : ℚ), (-11 / 4 : ℚ)], ![(3 / 4 : ℚ), 0, (-1 / 4 : ℚ), -5, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 13 : ℚ), 0, (-1 / 13 : ℚ), (-28 / 13 : ℚ), (-27 / 13 : ℚ)], ![(12 / 13 : ℚ), 0, (-1 / 13 : ℚ), (-56 / 13 : ℚ), (-7 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), 0, (-29 / 17 : ℚ), (-3 / 17 : ℚ), 0], ![(20 / 17 : ℚ), 0, (-58 / 17 : ℚ), (6 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), 0, (-26 / 17 : ℚ), (-6 / 17 : ℚ), 0], ![1, 0, (-52 / 17 : ℚ), (9 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(5 / 4 : ℚ), 0, -3, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 1, -1], ![2, 0, -6, -1, -1]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), 0, (-23 / 17 : ℚ), (-9 / 17 : ℚ), (-40 / 17 : ℚ)], ![(14 / 17 : ℚ), 0, (-46 / 17 : ℚ), (12 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), 0, (-23 / 17 : ℚ), (-9 / 17 : ℚ), (-43 / 17 : ℚ)], ![(14 / 17 : ℚ), 0, (-46 / 17 : ℚ), (12 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), 0, (-23 / 17 : ℚ), (-9 / 17 : ℚ), (-37 / 17 : ℚ)], ![(14 / 17 : ℚ), 0, (-46 / 17 : ℚ), (12 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, (-11 / 7 : ℚ), 0, (-1 / 7 : ℚ)], ![(8 / 7 : ℚ), 0, (-22 / 7 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(5 / 4 : ℚ), 0, -3, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 1, -1], ![2, 0, -6, 0, -1]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-11 / 5 : ℚ)], ![(9 / 10 : ℚ), 0, (-12 / 5 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-27 / 10 : ℚ), (9 / 10 : ℚ), 0], ![(21 / 10 : ℚ), 0, (-27 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-21 / 10 : ℚ)], ![(9 / 10 : ℚ), 0, (-12 / 5 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(5 / 4 : ℚ), 0, -3, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -3, 1, -1], ![(7 / 4 : ℚ), 0, -6, 1, -1]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0, -2], ![1, 0, (-16 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-1 / 5 : ℚ), (-13 / 5 : ℚ)], ![(4 / 5 : ℚ), 0, (-14 / 5 : ℚ), 0, (8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-1 / 5 : ℚ), (-11 / 5 : ℚ)], ![(4 / 5 : ℚ), 0, (-14 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, -1], ![(3 / 2 : ℚ), 0, -6, -1, -1]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (-8 / 3 : ℚ), 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 34 : ℚ), 0, (-117 / 34 : ℚ), (-20 / 17 : ℚ), (-35 / 34 : ℚ)], ![(101 / 68 : ℚ), 0, (-117 / 17 : ℚ), (-43 / 34 : ℚ), (-8 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), 0, (-61 / 18 : ℚ), (-11 / 9 : ℚ), (-10 / 9 : ℚ)], ![(3 / 2 : ℚ), 0, (-61 / 9 : ℚ), (-4 / 3 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-19 / 6 : ℚ), (-13 / 12 : ℚ), (-19 / 12 : ℚ)], ![(7 / 6 : ℚ), 0, (-19 / 3 : ℚ), (-13 / 12 : ℚ), (-19 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 11 : ℚ), 0, (-21 / 11 : ℚ), (-37 / 11 : ℚ), (-32 / 11 : ℚ)], ![(6 / 11 : ℚ), 0, (-42 / 11 : ℚ), (5 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-11 / 7 : ℚ), (-18 / 7 : ℚ), (-16 / 7 : ℚ)], ![(5 / 7 : ℚ), 0, (-22 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-17 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![(11 / 5 : ℚ), 0, (-34 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-11 / 7 : ℚ), (-20 / 7 : ℚ), (-16 / 7 : ℚ)], ![(5 / 7 : ℚ), 0, (-22 / 7 : ℚ), (2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-11 / 5 : ℚ), (-6 / 5 : ℚ)], ![(4 / 5 : ℚ), 0, (-14 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-23 / 13 : ℚ), 0, 0], ![(17 / 13 : ℚ), (-9 / 13 : ℚ), (-48 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-13 / 8 : ℚ), 0, 0], ![(5 / 4 : ℚ), (-3 / 4 : ℚ), (-27 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(5 / 4 : ℚ), (-3 / 4 : ℚ), (-13 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![1, -1, -4, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-17 / 12 : ℚ), 0, (-5 / 3 : ℚ)], ![(7 / 6 : ℚ), (-5 / 6 : ℚ), (-35 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-11 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(4 / 3 : ℚ), (-2 / 3 : ℚ), (-23 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-17 / 12 : ℚ), 0, (-19 / 12 : ℚ)], ![(7 / 6 : ℚ), (-5 / 6 : ℚ), (-35 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-11 / 7 : ℚ), 0, 0], ![(8 / 7 : ℚ), (-6 / 7 : ℚ), (-23 / 7 : ℚ), (1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(5 / 4 : ℚ), (-3 / 4 : ℚ), (-13 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![1, -1, (-11 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-18 / 11 : ℚ)], ![(13 / 11 : ℚ), (-9 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (-41 / 22 : ℚ), 0, (-21 / 11 : ℚ)], ![(12 / 11 : ℚ), (-9 / 22 : ℚ), (-42 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-16 / 11 : ℚ)], ![(13 / 11 : ℚ), (-9 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 5 : ℚ), 0, 0], ![(6 / 5 : ℚ), (-4 / 5 : ℚ), -3, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), 0, 0], ![(5 / 6 : ℚ), (-7 / 6 : ℚ), (-10 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), 0, -2], ![1, -1, (-19 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), 0, (-13 / 6 : ℚ)], ![1, -1, (-19 / 6 : ℚ), (1 / 6 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 4 : ℚ), 0, (-23 / 12 : ℚ)], ![1, -1, (-31 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, 0], ![(7 / 3 : ℚ), (1 / 3 : ℚ), (-20 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, 0], ![(7 / 3 : ℚ), (1 / 3 : ℚ), (-20 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-38 / 13 : ℚ), 0, 0], ![(30 / 13 : ℚ), (4 / 13 : ℚ), (-84 / 13 : ℚ), (-20 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-28 / 11 : ℚ), (-15 / 11 : ℚ), 0], ![2, 0, (-65 / 11 : ℚ), (-17 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-25 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(19 / 9 : ℚ), (1 / 9 : ℚ), (-19 / 3 : ℚ), (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-20 / 7 : ℚ), (-11 / 7 : ℚ), 0], ![(13 / 7 : ℚ), 0, (-47 / 7 : ℚ), (-11 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-32 / 9 : ℚ), 0, (4 / 9 : ℚ)], ![(20 / 9 : ℚ), (2 / 9 : ℚ), (-68 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-54 / 17 : ℚ), (-8 / 17 : ℚ), 0], ![(30 / 17 : ℚ), (-4 / 17 : ℚ), (-116 / 17 : ℚ), 0, (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, (-72 / 11 : ℚ), (-38 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-34 / 11 : ℚ), (-4 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 21 : ℚ), (-8 / 21 : ℚ), (-10 / 3 : ℚ), 0, 0], ![(46 / 21 : ℚ), (4 / 21 : ℚ), (-148 / 21 : ℚ), (8 / 21 : ℚ), (4 / 21 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), -3, 0, 0], ![2, 0, (-19 / 3 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 68 : ℚ), 1, (-33 / 34 : ℚ), -1, (-41 / 68 : ℚ)], ![0, 0, -2, 0, (-5 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 28 : ℚ), 1, (-13 / 14 : ℚ), -1, (-15 / 4 : ℚ)], ![0, 0, -2, 0, (-8 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 28 : ℚ), 1, (-13 / 14 : ℚ), -1, (-47 / 14 : ℚ)], ![0, 0, -2, 0, (-15 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (1 / 2 : ℚ), (-11 / 6 : ℚ), 0, 0], ![(1 / 3 : ℚ), (-1 / 2 : ℚ), (-23 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 74 : ℚ), (107 / 74 : ℚ), (3 / 74 : ℚ), (-133 / 74 : ℚ), (-292 / 37 : ℚ)], ![(-39 / 74 : ℚ), (-44 / 37 : ℚ), 0, (-127 / 74 : ℚ), (-289 / 74 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (3 / 5 : ℚ), (-26 / 15 : ℚ), (-1 / 15 : ℚ), (-31 / 15 : ℚ)], ![(1 / 3 : ℚ), (-1 / 3 : ℚ), (-53 / 15 : ℚ), 0, (-61 / 30 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 7 : ℚ), 0, -2], ![1, (-11 / 14 : ℚ), (-7 / 2 : ℚ), -1, (-13 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-7 / 6 : ℚ), (-17 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![(11 / 6 : ℚ), -1, (-20 / 3 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-7 / 6 : ℚ), (-5 / 2 : ℚ), 0, 0], ![2, (-5 / 6 : ℚ), (-17 / 3 : ℚ), (1 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-23 / 13 : ℚ), 0, 0, (-18 / 13 : ℚ)], ![(17 / 13 : ℚ), (-48 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-7 / 6 : ℚ), (-13 / 12 : ℚ), (-49 / 12 : ℚ)], ![0, (-7 / 12 : ℚ), (5 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-23 / 13 : ℚ), 0, 0, (-16 / 13 : ℚ)], ![(17 / 13 : ℚ), (-48 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 19 : ℚ), (-29 / 19 : ℚ), 0, 0, (-30 / 19 : ℚ)], ![(23 / 19 : ℚ), (-60 / 19 : ℚ), (2 / 19 : ℚ), (5 / 19 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-23 / 18 : ℚ), 0, (-1 / 18 : ℚ), (-11 / 6 : ℚ)], ![(10 / 9 : ℚ), (-47 / 18 : ℚ), (1 / 9 : ℚ), 0, (20 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 32 : ℚ), (-37 / 32 : ℚ), 0, 0, (-59 / 32 : ℚ)], ![(17 / 16 : ℚ), (-75 / 32 : ℚ), (1 / 32 : ℚ), (1 / 32 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-21 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-21 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-21 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-9 / 4 : ℚ)], ![1, (-7 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![1, -4, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![1, -4, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-17 / 12 : ℚ), 0, (-7 / 4 : ℚ), (-5 / 3 : ℚ)], ![(7 / 6 : ℚ), (-35 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-29 / 24 : ℚ), 0, (-11 / 6 : ℚ), (-43 / 24 : ℚ)], ![(13 / 12 : ℚ), (-59 / 24 : ℚ), (1 / 24 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-7 / 6 : ℚ), (-49 / 12 : ℚ), (-25 / 12 : ℚ)], ![0, (-7 / 12 : ℚ), (5 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-11 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-7 / 6 : ℚ)], ![(4 / 3 : ℚ), (-23 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-29 / 24 : ℚ), 0, (-43 / 24 : ℚ), (-11 / 12 : ℚ)], ![(13 / 12 : ℚ), (-59 / 24 : ℚ), (1 / 24 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (-9 / 7 : ℚ), 0, 0, (-27 / 14 : ℚ)], ![(15 / 14 : ℚ), (-37 / 14 : ℚ), (1 / 14 : ℚ), (1 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 52 : ℚ), (-21 / 26 : ℚ), (-14 / 13 : ℚ), (-37 / 52 : ℚ), (-62 / 13 : ℚ)], ![0, (-22 / 13 : ℚ), (1 / 13 : ℚ), (-5 / 13 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-5 / 4 : ℚ), 0, (-1 / 16 : ℚ), (-29 / 16 : ℚ)], ![(17 / 16 : ℚ), (-41 / 16 : ℚ), (1 / 16 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 0, (-7 / 4 : ℚ)], ![(5 / 4 : ℚ), (-13 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-21 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-21 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ)], ![1, (-11 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), -1, 1, (-13 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, 1, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ)], ![1, (-11 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 44 : ℚ), (-17 / 22 : ℚ), (-12 / 11 : ℚ), (-45 / 11 : ℚ), (-15 / 4 : ℚ)], ![0, (-18 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-18 / 11 : ℚ), (-16 / 11 : ℚ)], ![(13 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-6 / 11 : ℚ), (-13 / 11 : ℚ), (-46 / 11 : ℚ), (-24 / 11 : ℚ)], ![0, (-14 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 44 : ℚ), (-17 / 22 : ℚ), (-12 / 11 : ℚ), (-45 / 11 : ℚ), (-75 / 22 : ℚ)], ![0, (-18 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-16 / 11 : ℚ), (-9 / 11 : ℚ)], ![(13 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, (-19 / 10 : ℚ)], ![(11 / 10 : ℚ), (-5 / 2 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, (-19 / 10 : ℚ)], ![(11 / 10 : ℚ), (-5 / 2 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), 2]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), 0, 0, (-9 / 5 : ℚ)], ![(6 / 5 : ℚ), -3, (1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-4 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ)], ![(5 / 6 : ℚ), (-10 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-4 / 3 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![(5 / 6 : ℚ), (-10 / 3 : ℚ), 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ)], ![(2 / 3 : ℚ), (-11 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 12 : ℚ), (-5 / 4 : ℚ), (-1 / 2 : ℚ), (-49 / 12 : ℚ), (-7 / 2 : ℚ)], ![0, (-31 / 12 : ℚ), (-5 / 12 : ℚ), (5 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-3 / 2 : ℚ), 0, -2, (-11 / 6 : ℚ)], ![1, (-19 / 6 : ℚ), (1 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 12 : ℚ), (-5 / 4 : ℚ), (-1 / 2 : ℚ), (-29 / 6 : ℚ), (-21 / 8 : ℚ)], ![0, (-31 / 12 : ℚ), (-5 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-5 / 4 : ℚ), 0, (-25 / 12 : ℚ), (-23 / 12 : ℚ)], ![1, (-31 / 12 : ℚ), (1 / 12 : ℚ), (11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-5 / 4 : ℚ), 0, (-23 / 12 : ℚ), -1], ![1, (-31 / 12 : ℚ), (1 / 12 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-23 / 10 : ℚ), 0, (-13 / 10 : ℚ), 0], ![(21 / 10 : ℚ), (-28 / 5 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 7 : ℚ), 0, (-10 / 7 : ℚ), 0], ![(15 / 7 : ℚ), (-41 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0], ![(13 / 6 : ℚ), (-19 / 3 : ℚ), (-11 / 6 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -3, 0, 0, 0], ![(7 / 3 : ℚ), (-20 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-38 / 13 : ℚ), 0, 0, 0], ![(30 / 13 : ℚ), (-84 / 13 : ℚ), (-20 / 13 : ℚ), (4 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-19 / 8 : ℚ), 0, 0, (-1 / 8 : ℚ)], ![(17 / 8 : ℚ), -5, (-5 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-38 / 13 : ℚ), 0, 0, 0], ![(30 / 13 : ℚ), (-84 / 13 : ℚ), (-20 / 13 : ℚ), (8 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-43 / 20 : ℚ), 0, 0, (-1 / 20 : ℚ)], ![(41 / 20 : ℚ), (-22 / 5 : ℚ), (-1 / 4 : ℚ), (1 / 20 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-33 / 13 : ℚ), (-18 / 13 : ℚ), 0, (-2 / 13 : ℚ)], ![(27 / 13 : ℚ), (-77 / 13 : ℚ), (-20 / 13 : ℚ), (2 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-19 / 7 : ℚ), (-10 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![(13 / 7 : ℚ), (-45 / 7 : ℚ), (-10 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 8 : ℚ), (11 / 12 : ℚ), (-97 / 24 : ℚ), (-49 / 24 : ℚ)], ![0, (-11 / 24 : ℚ), (1 / 8 : ℚ), (1 / 24 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-19 / 7 : ℚ), (-10 / 7 : ℚ), (-4 / 7 : ℚ), 0], ![(13 / 7 : ℚ), (-45 / 7 : ℚ), (-10 / 7 : ℚ), (2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-21 / 8 : ℚ), (-11 / 8 : ℚ), 0, (-1 / 8 : ℚ)], ![(15 / 8 : ℚ), (-25 / 4 : ℚ), (-11 / 8 : ℚ), 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 5 : ℚ), (1 / 5 : ℚ), (-17 / 5 : ℚ), (-9 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), 0, (-17 / 5 : ℚ), (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0], ![(-7 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 3 : ℚ), 0, -3, (-5 / 3 : ℚ)], ![0, 0, 0, -3, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), 2, (2 / 7 : ℚ), (-40 / 7 : ℚ), (-22 / 7 : ℚ)], ![(2 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-40 / 7 : ℚ), (-22 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 7 : ℚ), (4 / 7 : ℚ), (-44 / 7 : ℚ), (-24 / 7 : ℚ)], ![0, (-4 / 7 : ℚ), 0, (-44 / 7 : ℚ), (-24 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-28 / 11 : ℚ), 0, (2 / 11 : ℚ), (-19 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-54 / 11 : ℚ), (-2 / 11 : ℚ), (1 / 11 : ℚ), (21 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (-29 / 12 : ℚ), (-14 / 3 : ℚ), (11 / 12 : ℚ)], ![(25 / 12 : ℚ), 0, (-31 / 12 : ℚ), (-19 / 4 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, (1 / 2 : ℚ), 0], ![(-7 / 20 : ℚ), -5, (-1 / 5 : ℚ), (2 / 5 : ℚ), (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-17 / 7 : ℚ), 0, (1 / 7 : ℚ), (-32 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-33 / 7 : ℚ), (-1 / 7 : ℚ), (1 / 14 : ℚ), -1]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (-28 / 9 : ℚ), (-52 / 9 : ℚ), 0], ![(20 / 9 : ℚ), 0, (-32 / 9 : ℚ), -6, (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), (-36 / 11 : ℚ), 0], ![(15 / 11 : ℚ), (-7 / 11 : ℚ), (-21 / 11 : ℚ), (-37 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), (-17 / 6 : ℚ), 0], ![(7 / 6 : ℚ), (-5 / 6 : ℚ), (-5 / 3 : ℚ), (-35 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (-24 / 11 : ℚ), (-47 / 11 : ℚ), 0], ![2, 0, (-25 / 11 : ℚ), (-95 / 22 : ℚ), (17 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-28 / 9 : ℚ), (-52 / 9 : ℚ), 0], ![(20 / 9 : ℚ), (2 / 9 : ℚ), (-32 / 9 : ℚ), -6, (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 2, (1 / 6 : ℚ), (1 / 12 : ℚ), -2], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-1 / 22 : ℚ), (1 / 11 : ℚ), (-37 / 22 : ℚ), (-51 / 11 : ℚ)], ![(-7 / 22 : ℚ), (-5 / 22 : ℚ), 0, (41 / 22 : ℚ), (-27 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-19 / 11 : ℚ), (-36 / 11 : ℚ), 0, (-16 / 11 : ℚ)], ![(15 / 11 : ℚ), (-21 / 11 : ℚ), (-37 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 10 : ℚ), 0, (-17 / 10 : ℚ), (-22 / 5 : ℚ)], ![(-3 / 10 : ℚ), (-1 / 10 : ℚ), 0, (19 / 10 : ℚ), (-22 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-5 / 4 : ℚ), (-29 / 12 : ℚ), 0, (-11 / 6 : ℚ)], ![(13 / 12 : ℚ), (-4 / 3 : ℚ), (-59 / 24 : ℚ), (1 / 12 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-3 / 2 : ℚ), (-29 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 12 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-8 / 5 : ℚ), -3, 0, (-7 / 5 : ℚ)], ![(6 / 5 : ℚ), (-8 / 5 : ℚ), -3, (1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-5 / 4 : ℚ), (-19 / 8 : ℚ), 0, -2], ![1, (-5 / 4 : ℚ), (-19 / 8 : ℚ), 0, (5 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 3 : ℚ), -3, 0, (-7 / 3 : ℚ)], ![1, (-5 / 3 : ℚ), -3, 0, 2]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-43 / 20 : ℚ), (-21 / 5 : ℚ), 0, 0], ![(41 / 20 : ℚ), (-9 / 4 : ℚ), (-17 / 4 : ℚ), (-1 / 4 : ℚ), (31 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 7 : ℚ), (-32 / 7 : ℚ), 0, 0], ![(15 / 7 : ℚ), (-19 / 7 : ℚ), (-33 / 7 : ℚ), (-5 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -3, (-16 / 3 : ℚ), 0, 0], ![(7 / 3 : ℚ), -3, (-16 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-24 / 11 : ℚ), (-47 / 11 : ℚ), (-13 / 11 : ℚ), 0], ![2, (-25 / 11 : ℚ), (-95 / 22 : ℚ), (-14 / 11 : ℚ), (6 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xx, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-23 / 9 : ℚ), (-44 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(19 / 9 : ℚ), (-25 / 9 : ℚ), -5, (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 17 : ℚ), (-72 / 17 : ℚ), (-23 / 34 : ℚ), (69 / 34 : ℚ), 0], ![(-37 / 17 : ℚ), (-37 / 17 : ℚ), (-2 / 17 : ℚ), (-65 / 34 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-67 / 32 : ℚ), (-33 / 8 : ℚ), (-27 / 32 : ℚ), (1 / 16 : ℚ), 0], ![(-67 / 32 : ℚ), (-67 / 32 : ℚ), (-1 / 16 : ℚ), (-61 / 32 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (4 / 3 : ℚ), (-2 / 3 : ℚ), -5], ![0, 0, 0, 0, -5]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-3, (-16 / 3 : ℚ), -1, (-7 / 3 : ℚ), 0], ![-3, -3, (-2 / 3 : ℚ), -6, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 11 : ℚ), (26 / 11 : ℚ), (8 / 11 : ℚ), (-76 / 11 : ℚ)], ![0, 0, (-8 / 11 : ℚ), 0, (-76 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 68 : ℚ), (-71 / 17 : ℚ)], ![0, (-1 / 17 : ℚ), (-1 / 17 : ℚ), (9 / 68 : ℚ), (-71 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-67 / 32 : ℚ), (-67 / 32 : ℚ), (-27 / 32 : ℚ), (1 / 16 : ℚ), 0], ![(-67 / 32 : ℚ), (-1 / 16 : ℚ), (-1 / 16 : ℚ), (-61 / 32 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (4 / 3 : ℚ), (-2 / 3 : ℚ), -5], ![0, 0, 0, 0, -5]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 2, (2 / 3 : ℚ), -6], ![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, -6]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-28 / 11 : ℚ), (-28 / 11 : ℚ), (-17 / 11 : ℚ), (4 / 11 : ℚ), 0], ![(-28 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-82 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-17 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), 0, 0, (-17 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (25 / 17 : ℚ), (4 / 17 : ℚ), 0, (-62 / 17 : ℚ)], ![0, (-4 / 17 : ℚ), 0, 0, (-62 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), -3], ![0, 0, 0, 0, -3]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 1, 0, 0, (-8 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 17 : ℚ), 2, (2 / 17 : ℚ), (-5 / 17 : ℚ), (-80 / 17 : ℚ)], ![(2 / 17 : ℚ), (-4 / 17 : ℚ), 0, (9 / 17 : ℚ), (-80 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (25 / 12 : ℚ), (1 / 6 : ℚ), 0, (-14 / 3 : ℚ)], ![0, (-1 / 6 : ℚ), 0, (3 / 4 : ℚ), (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 4 : ℚ), 0, (-5 / 34 : ℚ), (-74 / 17 : ℚ)], ![0, (-25 / 68 : ℚ), 0, (9 / 34 : ℚ), (-74 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, (1 / 4 : ℚ), 0, (-11 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), -3], ![0, 0, 0, 0, -3]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-7 / 2 : ℚ)], ![0, 0, (1 / 2 : ℚ), (-1 / 2 : ℚ), (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, (-1 / 4 : ℚ), (1 / 8 : ℚ), (-11 / 8 : ℚ)], ![(-1 / 2 : ℚ), (-5 / 8 : ℚ), (-7 / 2 : ℚ), (-9 / 8 : ℚ), (-11 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (17 / 8 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), -5], ![0, (-1 / 4 : ℚ), 0, (7 / 8 : ℚ), -5]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, (1 / 4 : ℚ), (-19 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), 0, (3 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (5 / 3 : ℚ), 0, (1 / 3 : ℚ), (-11 / 3 : ℚ)], ![0, 0, 0, (1 / 3 : ℚ), (-11 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, (5 / 3 : ℚ), (1 / 2 : ℚ), (-9 / 2 : ℚ)], ![0, (-1 / 6 : ℚ), 0, (1 / 2 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (20 / 9 : ℚ), 2, (11 / 9 : ℚ), (-52 / 9 : ℚ)], ![0, (-4 / 9 : ℚ), 0, (11 / 9 : ℚ), (-52 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (9 / 8 : ℚ), (-3 / 8 : ℚ), (-1 / 4 : ℚ), (-19 / 8 : ℚ)], ![0, 0, 0, (-1 / 4 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (11 / 5 : ℚ), (2 / 5 : ℚ), (-3 / 5 : ℚ), (-24 / 5 : ℚ)], ![0, 0, 0, 0, (-24 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (11 / 5 : ℚ), (2 / 5 : ℚ), (-3 / 5 : ℚ), (-24 / 5 : ℚ)], ![0, 0, 0, 0, (-24 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 3 : ℚ), 0, (-2 / 3 : ℚ), -5], ![0, 0, 0, 0, -5]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 7 : ℚ), 2, (1 / 7 : ℚ), (-11 / 7 : ℚ), (-34 / 7 : ℚ)], ![(1 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-11 / 7 : ℚ), (-34 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (15 / 7 : ℚ), (2 / 7 : ℚ), (-12 / 7 : ℚ), (-36 / 7 : ℚ)], ![0, (-2 / 7 : ℚ), 0, (-12 / 7 : ℚ), (-36 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 7 : ℚ), (4 / 7 : ℚ), (4 / 7 : ℚ), (-44 / 7 : ℚ)], ![0, (-4 / 7 : ℚ), 0, 0, (-44 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, (2 / 3 : ℚ), 0, -6], ![0, (-2 / 3 : ℚ), 0, 0, -6]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-11 / 4 : ℚ)], ![0, (-5 / 4 : ℚ), (-17 / 4 : ℚ), (-9 / 4 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (26 / 11 : ℚ), (8 / 11 : ℚ), 0, (-76 / 11 : ℚ)], ![0, (-8 / 11 : ℚ), 0, 0, (-76 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), 0, (-1 / 9 : ℚ), (-7 / 3 : ℚ), (8 / 9 : ℚ)], ![(19 / 9 : ℚ), (1 / 9 : ℚ), (1 / 9 : ℚ), (-22 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-29 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, 0, 0], ![(-1 / 5 : ℚ), -5, (-11 / 5 : ℚ), (-1 / 5 : ℚ), (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), 0, (-4 / 15 : ℚ), (-14 / 5 : ℚ), (-8 / 15 : ℚ)], ![(26 / 15 : ℚ), (4 / 15 : ℚ), (-4 / 15 : ℚ), (-46 / 15 : ℚ), (-2 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-10 / 3 : ℚ), (-4 / 9 : ℚ), 0, (-56 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-56 / 9 : ℚ), (-26 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), 0, (-4 / 3 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 6 : ℚ), (-53 / 12 : ℚ), (-1 / 12 : ℚ), (17 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-21 / 10 : ℚ), 0, (-6 / 5 : ℚ), (-11 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-83 / 20 : ℚ), 0, (5 / 4 : ℚ), (-11 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, (-7 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), -5, (-1 / 5 : ℚ), 2, (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 3 : ℚ), 0, (-5 / 3 : ℚ), (5 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-16 / 3 : ℚ), (-1 / 3 : ℚ), (5 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 28 : ℚ), 0, (-59 / 28 : ℚ), (9 / 56 : ℚ), (-43 / 28 : ℚ)], ![(69 / 56 : ℚ), (1 / 28 : ℚ), (-15 / 7 : ℚ), (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-25 / 11 : ℚ), 0, (-41 / 22 : ℚ), (-60 / 11 : ℚ)], ![(-15 / 22 : ℚ), (-49 / 11 : ℚ), (-1 / 11 : ℚ), (43 / 22 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-12 / 5 : ℚ), 0, (-9 / 5 : ℚ), (-23 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-23 / 5 : ℚ), 0, 2, (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-12 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-7 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-23 / 5 : ℚ), 0, (1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-28 / 11 : ℚ), (12 / 11 : ℚ), 0], ![(25 / 11 : ℚ), (2 / 11 : ℚ), (-30 / 11 : ℚ), (2 / 11 : ℚ), (-8 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 2 : ℚ), 1, -1], ![2, 0, (-11 / 4 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-13 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-53 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-7 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-19 / 12 : ℚ), (-2 / 3 : ℚ), (-13 / 12 : ℚ), (-49 / 12 : ℚ)], ![0, (-37 / 12 : ℚ), (-3 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-11 / 5 : ℚ), 0, (-13 / 10 : ℚ), (-43 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-43 / 10 : ℚ), 0, (1 / 10 : ℚ), (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-19 / 4 : ℚ), 0, (7 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-9 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-9 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-35 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-5 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-8 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-17 / 3 : ℚ)], ![(-2 / 3 : ℚ), -5, 0, (-5 / 3 : ℚ), 2]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 3 : ℚ), 0, 0, (4 / 3 : ℚ)], ![(-1 / 2 : ℚ), (-14 / 3 : ℚ), (-1 / 6 : ℚ), (4 / 3 : ℚ), (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-23 / 10 : ℚ), 0, 0, (-43 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-9 / 2 : ℚ), (-1 / 10 : ℚ), (7 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 5 : ℚ), 0, (-9 / 5 : ℚ)], ![(6 / 5 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, (-19 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-19 / 4 : ℚ), 0, (7 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (-31 / 14 : ℚ), 0, 1, (-30 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-61 / 14 : ℚ), (-1 / 14 : ℚ), (13 / 14 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, (-8 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 9 : ℚ)], ![(20 / 9 : ℚ), (2 / 9 : ℚ), (-26 / 9 : ℚ), (-17 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-17 / 7 : ℚ), 0, (-33 / 7 : ℚ), (-32 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-33 / 7 : ℚ), (-1 / 7 : ℚ), (1 / 7 : ℚ), -1]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-22 / 7 : ℚ), 0, (-44 / 7 : ℚ), (-40 / 7 : ℚ)], ![(-8 / 7 : ℚ), (-40 / 7 : ℚ), 0, (-20 / 7 : ℚ), (-40 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 16 : ℚ), (-7 / 16 : ℚ), (-7 / 4 : ℚ), (-65 / 16 : ℚ), (-33 / 16 : ℚ)], ![0, (-13 / 16 : ℚ), (-29 / 16 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-22 / 7 : ℚ), 0, (-48 / 7 : ℚ), (-40 / 7 : ℚ)], ![(-8 / 7 : ℚ), (-40 / 7 : ℚ), 0, (4 / 7 : ℚ), (-40 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 3 : ℚ), 0, (1 / 6 : ℚ)], ![(4 / 3 : ℚ), (-2 / 3 : ℚ), (-11 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-9 / 5 : ℚ), 0, 0], ![(7 / 5 : ℚ), (-3 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(5 / 4 : ℚ), (-3 / 4 : ℚ), (-7 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![1, -1, -2, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-14 / 11 : ℚ)], ![(15 / 11 : ℚ), (-7 / 11 : ℚ), (-21 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-16 / 11 : ℚ)], ![(15 / 11 : ℚ), (-7 / 11 : ℚ), (-21 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-9 / 5 : ℚ), 0, -1], ![(7 / 5 : ℚ), (-3 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), -1]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ), 0, (1 / 5 : ℚ)], ![(6 / 5 : ℚ), (-4 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] }
]

theorem conicDetC29_checked : conicDetC29.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
