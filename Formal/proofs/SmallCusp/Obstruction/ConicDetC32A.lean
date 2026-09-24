import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC32A : List RationalConicRecord := [
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![(-3 / 2 : ℚ), 0, (-31 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(9 / 7 : ℚ), (-2 / 7 : ℚ), 0, -6, (-38 / 7 : ℚ)], ![(9 / 7 : ℚ), (-20 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ), (-38 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, -6, (-16 / 5 : ℚ)], ![0, (-16 / 5 : ℚ), (-2 / 5 : ℚ), -6, (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-34 / 25 : ℚ), 0, (-59 / 25 : ℚ), (-221 / 50 : ℚ), (51 / 25 : ℚ)], ![(-37 / 25 : ℚ), (3 / 25 : ℚ), (-62 / 25 : ℚ), (-112 / 25 : ℚ), (27 / 25 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-65 / 44 : ℚ), (-1 / 22 : ℚ), (-49 / 22 : ℚ), (-93 / 22 : ℚ), 1], ![(-20 / 11 : ℚ), 0, (-51 / 22 : ℚ), (-47 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 8 : ℚ), 0, (-17 / 8 : ℚ), (-199 / 48 : ℚ), (1 / 24 : ℚ)], ![(-8 / 3 : ℚ), (1 / 24 : ℚ), (-13 / 6 : ℚ), (-25 / 6 : ℚ), (-7 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, (-17 / 8 : ℚ), (-199 / 48 : ℚ), (19 / 24 : ℚ)], ![(-7 / 6 : ℚ), (1 / 24 : ℚ), (-13 / 6 : ℚ), (-25 / 6 : ℚ), (37 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-55 / 36 : ℚ), (-1 / 18 : ℚ), (-41 / 18 : ℚ), (-77 / 18 : ℚ), 0], ![(-17 / 9 : ℚ), 0, (-43 / 18 : ℚ), (-13 / 3 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-1 / 11 : ℚ), 0, 0, (-15 / 11 : ℚ)], ![(9 / 22 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 22 : ℚ), (16 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), (-17 / 4 : ℚ), (11 / 12 : ℚ)], ![(-7 / 4 : ℚ), 0, (-9 / 4 : ℚ), (-103 / 24 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, (-1 / 22 : ℚ), 0, 0, (-46 / 11 : ℚ)], ![(21 / 22 : ℚ), (-23 / 11 : ℚ), (-1 / 22 : ℚ), (-1 / 44 : ℚ), (-29 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 9 : ℚ), (-1 / 9 : ℚ), (-20 / 9 : ℚ), (-13 / 3 : ℚ), (-1 / 9 : ℚ)], ![(-11 / 6 : ℚ), 0, (-7 / 3 : ℚ), (-79 / 18 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 22 : ℚ), 0, (-1 / 22 : ℚ), (-47 / 22 : ℚ), (21 / 22 : ℚ)], ![(-13 / 11 : ℚ), (1 / 22 : ℚ), (1 / 22 : ℚ), (-24 / 11 : ℚ), (13 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 13 : ℚ), (-1 / 13 : ℚ), (-2 / 13 : ℚ), (-32 / 13 : ℚ), 1], ![(-22 / 13 : ℚ), 0, (2 / 13 : ℚ), (-34 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 10 : ℚ), 0, -1, 0], ![(-1 / 10 : ℚ), (-5 / 2 : ℚ), (-11 / 10 : ℚ), (-11 / 10 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(15 / 14 : ℚ), (-16 / 7 : ℚ), (-1 / 14 : ℚ), (1 / 14 : ℚ), (-31 / 7 : ℚ)], ![1, (-9 / 2 : ℚ), (-31 / 14 : ℚ), 0, (-11 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, (-31 / 12 : ℚ), (-1 / 9 : ℚ), 0, (-91 / 18 : ℚ)], ![(23 / 36 : ℚ), (-91 / 18 : ℚ), (-20 / 9 : ℚ), (-1 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-25 / 11 : ℚ), 0, (-41 / 33 : ℚ), (-27 / 22 : ℚ)], ![(9 / 22 : ℚ), (-49 / 11 : ℚ), (-1 / 11 : ℚ), (4 / 3 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, (-13 / 6 : ℚ), (31 / 12 : ℚ), (1 / 4 : ℚ)], ![(-7 / 6 : ℚ), (1 / 12 : ℚ), (-13 / 6 : ℚ), (13 / 6 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 29 : ℚ), 0, (-67 / 29 : ℚ), (30 / 29 : ℚ), (3 / 29 : ℚ)], ![(-63 / 29 : ℚ), (3 / 29 : ℚ), (-70 / 29 : ℚ), (-27 / 29 : ℚ), (-20 / 29 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-7 / 3 : ℚ), 1, -1], ![(-3 / 2 : ℚ), 0, (-5 / 2 : ℚ), -1, -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 24 : ℚ), (-1 / 24 : ℚ), (-53 / 24 : ℚ), (1 / 3 : ℚ), (1 / 2 : ℚ)], ![(-31 / 24 : ℚ), 0, (-55 / 24 : ℚ), (-1 / 4 : ℚ), (25 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-55 / 36 : ℚ), (-1 / 18 : ℚ), (-41 / 18 : ℚ), (47 / 36 : ℚ), 0], ![(-17 / 9 : ℚ), 0, (-43 / 18 : ℚ), (-2 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 8 : ℚ), 0, (-19 / 8 : ℚ), (33 / 16 : ℚ), (3 / 16 : ℚ)], ![(-11 / 8 : ℚ), (3 / 16 : ℚ), (-19 / 8 : ℚ), (9 / 8 : ℚ), (3 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-9 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-5 / 4 : ℚ)], ![(1 / 2 : ℚ), (-35 / 8 : ℚ), 0, (1 / 8 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-77 / 52 : ℚ), (-1 / 26 : ℚ), (-57 / 26 : ℚ), 1, (17 / 52 : ℚ)], ![(-24 / 13 : ℚ), 0, (-59 / 26 : ℚ), (1 / 13 : ℚ), (-3 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, (-3 / 2 : ℚ), 0, 0], ![(-3 / 4 : ℚ), -2, (-7 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 12 : ℚ), (-1 / 12 : ℚ), (-29 / 12 : ℚ), 1, 0], ![(-19 / 12 : ℚ), 0, (-31 / 12 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-65 / 44 : ℚ), (-1 / 22 : ℚ), (-49 / 22 : ℚ), 1, 0], ![(-20 / 11 : ℚ), 0, (-51 / 22 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-16 / 7 : ℚ), 0, (-17 / 14 : ℚ), (-31 / 7 : ℚ)], ![(1 / 2 : ℚ), (-31 / 7 : ℚ), 0, (1 / 7 : ℚ), (-31 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-11 / 5 : ℚ), 0, (1 / 10 : ℚ), (-6 / 5 : ℚ)], ![(1 / 2 : ℚ), (-43 / 10 : ℚ), 0, (3 / 2 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-1 / 8 : ℚ), (-19 / 8 : ℚ), (9 / 8 : ℚ), (3 / 4 : ℚ)], ![(-9 / 8 : ℚ), 0, (-19 / 8 : ℚ), (9 / 8 : ℚ), (13 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, (-7 / 3 : ℚ), (7 / 6 : ℚ), (-3 / 2 : ℚ)], ![(-7 / 6 : ℚ), (1 / 6 : ℚ), (-7 / 3 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 12 : ℚ), 0, (-13 / 6 : ℚ), 0, -1], ![(-11 / 4 : ℚ), 0, (-9 / 4 : ℚ), -1, -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, (-9 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)], ![(-11 / 6 : ℚ), (1 / 12 : ℚ), (-7 / 3 : ℚ), (-3 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-91 / 60 : ℚ), (-1 / 30 : ℚ), (-13 / 6 : ℚ), (19 / 60 : ℚ), 0], ![(-29 / 15 : ℚ), 0, (-67 / 30 : ℚ), (-4 / 15 : ℚ), (1 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (-21 / 10 : ℚ), 0, (1 / 20 : ℚ), (-83 / 20 : ℚ)], ![(1 / 4 : ℚ), (-83 / 20 : ℚ), 0, (5 / 4 : ℚ), (-83 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, (-17 / 8 : ℚ), (-9 / 8 : ℚ), (19 / 24 : ℚ)], ![(-7 / 6 : ℚ), (1 / 24 : ℚ), (-13 / 6 : ℚ), (-7 / 6 : ℚ), (37 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-55 / 36 : ℚ), (-1 / 18 : ℚ), (-41 / 18 : ℚ), (-23 / 18 : ℚ), 0], ![(-17 / 9 : ℚ), 0, (-43 / 18 : ℚ), (-25 / 18 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 14 : ℚ), (-1 / 14 : ℚ), (-33 / 14 : ℚ), 0, (-2 / 7 : ℚ)], ![(-3 / 2 : ℚ), 0, (-5 / 2 : ℚ), (1 / 7 : ℚ), (-1 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (1 / 2 : ℚ), 0], ![(-5 / 4 : ℚ), 0, (-9 / 4 : ℚ), (13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 11 : ℚ), (-19 / 11 : ℚ), (-9 / 11 : ℚ), (-36 / 11 : ℚ), (-18 / 11 : ℚ)], ![0, (-36 / 11 : ℚ), -1, (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-12 / 5 : ℚ), 0, (-23 / 5 : ℚ), (-23 / 5 : ℚ)], ![(1 / 2 : ℚ), (-23 / 5 : ℚ), 0, (1 / 5 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), (13 / 24 : ℚ), (11 / 12 : ℚ)], ![(-7 / 4 : ℚ), 0, (-9 / 4 : ℚ), (-11 / 24 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-1 / 10 : ℚ), 0, (-7 / 5 : ℚ), (-6 / 5 : ℚ)], ![(1 / 2 : ℚ), (-11 / 5 : ℚ), 0, (3 / 2 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, (-5 / 4 : ℚ), 0], ![(3 / 8 : ℚ), (-17 / 8 : ℚ), (-1 / 8 : ℚ), (11 / 8 : ℚ), (11 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, (-5 / 4 : ℚ), (5 / 4 : ℚ)], ![(1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), (5 / 4 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, (-1 / 22 : ℚ), 0, (-13 / 11 : ℚ), (-46 / 11 : ℚ)], ![(21 / 22 : ℚ), (-23 / 11 : ℚ), (-1 / 22 : ℚ), (27 / 22 : ℚ), (-29 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-1 / 11 : ℚ), 0, (-15 / 11 : ℚ), (-49 / 11 : ℚ)], ![(9 / 22 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (16 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-1 / 10 : ℚ), 0, (-7 / 5 : ℚ), (-43 / 10 : ℚ)], ![(1 / 2 : ℚ), (-11 / 5 : ℚ), 0, (3 / 2 : ℚ), (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (-11 / 5 : ℚ), (9 / 10 : ℚ), (9 / 10 : ℚ)], ![(-6 / 5 : ℚ), 0, (-11 / 5 : ℚ), (1 / 10 : ℚ), (9 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, (-6 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), (13 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), 0, 0], ![(-5 / 6 : ℚ), -1, (-4 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 13 : ℚ), (-1 / 13 : ℚ), (-28 / 13 : ℚ), (12 / 13 : ℚ), 0], ![(-79 / 52 : ℚ), 0, (-29 / 13 : ℚ), (1 / 13 : ℚ), (1 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), (11 / 12 : ℚ), (-1 / 3 : ℚ)], ![(-7 / 4 : ℚ), 0, (-9 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-1 / 10 : ℚ), 0, (-13 / 10 : ℚ), (-43 / 10 : ℚ)], ![(1 / 2 : ℚ), (-11 / 5 : ℚ), 0, (1 / 10 : ℚ), (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-5 / 4 : ℚ)], ![(1 / 2 : ℚ), (-17 / 8 : ℚ), 0, (11 / 8 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), -5], ![(5 / 4 : ℚ), (-5 / 2 : ℚ), 0, (-5 / 4 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-3 / 2 : ℚ), (-13 / 2 : ℚ)], ![(3 / 2 : ℚ), -3, 0, (-3 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, 0, 0, (-83 / 20 : ℚ)], ![(19 / 20 : ℚ), (-41 / 20 : ℚ), (-1 / 20 : ℚ), (1 / 10 : ℚ), (-13 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, (-31 / 7 : ℚ)], ![(5 / 14 : ℚ), (-15 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -5], ![0, (-7 / 3 : ℚ), 0, (2 / 3 : ℚ), -5]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, (-1 / 11 : ℚ), 0, (1 / 2 : ℚ), (-48 / 11 : ℚ)], ![(10 / 11 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (9 / 22 : ℚ), (-47 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 9 : ℚ), (-1 / 9 : ℚ), (-20 / 9 : ℚ), (-11 / 9 : ℚ), (-1 / 9 : ℚ)], ![(-11 / 6 : ℚ), 0, (-7 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 11 : ℚ), (-2 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), 0], ![(-17 / 11 : ℚ), 0, (-28 / 11 : ℚ), (2 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 7 : ℚ), -1, (-22 / 7 : ℚ), (-22 / 7 : ℚ)], ![0, (-11 / 7 : ℚ), -1, (-10 / 7 : ℚ), (-22 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ)], ![(-7 / 4 : ℚ), 0, (-9 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-1 / 7 : ℚ), 0, (-33 / 7 : ℚ), (-31 / 7 : ℚ)], ![(1 / 2 : ℚ), (-16 / 7 : ℚ), 0, (1 / 7 : ℚ), (-31 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 8 : ℚ), 0, (-1 / 8 : ℚ), (9 / 16 : ℚ), (-1 / 4 : ℚ)], ![(-3 / 2 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), (-7 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 17 : ℚ), (-1 / 17 : ℚ), (-2 / 17 : ℚ), (14 / 17 : ℚ), 0], ![(-24 / 17 : ℚ), 0, (1 / 17 : ℚ), 0, (2 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 10 : ℚ), (-1 / 20 : ℚ), (-1 / 5 : ℚ), (-43 / 20 : ℚ)], ![0, (-43 / 20 : ℚ), (-11 / 10 : ℚ), (1 / 4 : ℚ), (-43 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), (-1 / 14 : ℚ), (-1 / 14 : ℚ), (5 / 14 : ℚ), 0], ![(-17 / 14 : ℚ), (-1 / 14 : ℚ), 0, (1 / 14 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (-1 / 12 : ℚ)], ![(-5 / 4 : ℚ), (-1 / 12 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (-1 / 10 : ℚ), (2 / 5 : ℚ), (1 / 10 : ℚ)], ![(-6 / 5 : ℚ), (1 / 10 : ℚ), 0, (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-7 / 3 : ℚ)], ![0, (-13 / 6 : ℚ), (-7 / 6 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-11 / 4 : ℚ)], ![0, (-9 / 4 : ℚ), (-5 / 4 : ℚ), 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 13 : ℚ), 0, 0, 0, 0], ![(-21 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ), (-8 / 13 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 10 : ℚ), 0, 0, 0, 0], ![(-7 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (-2 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-19 / 8 : ℚ)], ![0, (-19 / 8 : ℚ), (-9 / 8 : ℚ), (3 / 8 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-33 / 28 : ℚ), (-1 / 28 : ℚ), (-1 / 14 : ℚ), (-33 / 28 : ℚ), (1 / 14 : ℚ)], ![(-5 / 4 : ℚ), 0, (1 / 28 : ℚ), (-5 / 4 : ℚ), (19 / 28 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-4 / 3 : ℚ), (-1 / 9 : ℚ), 0, (-23 / 9 : ℚ)], ![(-11 / 18 : ℚ), (-23 / 9 : ℚ), (-11 / 9 : ℚ), (-1 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 14 : ℚ), 0, (4 / 7 : ℚ), (3 / 7 : ℚ), (-1 / 14 : ℚ)], ![(-9 / 7 : ℚ), (1 / 14 : ℚ), 0, (1 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 44 : ℚ), (-1 / 44 : ℚ), (7 / 22 : ℚ), (1 / 4 : ℚ), 0], ![(-51 / 44 : ℚ), 0, 0, (1 / 22 : ℚ), (1 / 22 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 28 : ℚ), (-1 / 28 : ℚ), (2 / 7 : ℚ), (1 / 4 : ℚ), 0], ![(-31 / 28 : ℚ), 0, 0, (1 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (-1 / 6 : ℚ), 0, -2], ![0, (-9 / 4 : ℚ), (5 / 12 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 10 : ℚ), (-1 / 5 : ℚ), 0, (-37 / 10 : ℚ)], ![0, (-23 / 10 : ℚ), (1 / 2 : ℚ), 0, (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-1 / 6 : ℚ), (5 / 6 : ℚ), (5 / 6 : ℚ), 0], ![(-3 / 2 : ℚ), 0, (-1 / 2 : ℚ), (5 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 13 : ℚ), 0, (9 / 26 : ℚ), (1 / 13 : ℚ), 0], ![(-17 / 13 : ℚ), (1 / 13 : ℚ), (-7 / 26 : ℚ), (-3 / 13 : ℚ), (1 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-39 / 34 : ℚ), (-1 / 34 : ℚ), (4 / 17 : ℚ), (7 / 34 : ℚ), 0], ![(-41 / 34 : ℚ), 0, (-3 / 17 : ℚ), 0, (1 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)], ![(-7 / 5 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-20 / 17 : ℚ), 0, 1, -1, (8 / 17 : ℚ)], ![(-43 / 34 : ℚ), 0, -1, -1, (35 / 34 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 1, -1, 0], ![(-11 / 8 : ℚ), 0, -1, -1, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 1, -1, (-2 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, -1, -1, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 15 : ℚ), (-19 / 15 : ℚ), (-11 / 45 : ℚ), (-37 / 15 : ℚ), (-28 / 15 : ℚ)], ![0, (-37 / 15 : ℚ), (14 / 45 : ℚ), (1 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-1 / 24 : ℚ), (5 / 24 : ℚ), 0, 0], ![(-9 / 8 : ℚ), 0, (-1 / 8 : ℚ), (1 / 24 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 11 : ℚ), (-19 / 11 : ℚ), (-2 / 3 : ℚ), (-36 / 11 : ℚ), (-18 / 11 : ℚ)], ![0, (-36 / 11 : ℚ), (28 / 33 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, (9 / 8 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ)], ![(-7 / 4 : ℚ), (3 / 8 : ℚ), (-3 / 4 : ℚ), (3 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 16 : ℚ), (-3 / 16 : ℚ), (15 / 16 : ℚ), 0, (-3 / 16 : ℚ)], ![(-25 / 16 : ℚ), 0, (-9 / 16 : ℚ), 0, (-3 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 10 : ℚ), (-7 / 10 : ℚ), (11 / 10 : ℚ), (19 / 10 : ℚ), (-1 / 10 : ℚ)], ![(-19 / 10 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ), (19 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-18 / 5 : ℚ)], ![0, (-12 / 5 : ℚ), (2 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-19 / 8 : ℚ)], ![0, (-19 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 4 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (2 / 3 : ℚ), (4 / 9 : ℚ), (-1 / 9 : ℚ)], ![(-13 / 9 : ℚ), (1 / 9 : ℚ), (1 / 9 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 17 : ℚ), (-1 / 17 : ℚ), (11 / 17 : ℚ), (7 / 17 : ℚ), 0], ![(-24 / 17 : ℚ), 0, (2 / 17 : ℚ), 0, (2 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), 0, (2 / 7 : ℚ), (3 / 14 : ℚ), 0], ![(-8 / 7 : ℚ), (1 / 14 : ℚ), (1 / 14 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 17 : ℚ), 0, 1, -1, (-1 / 17 : ℚ)], ![(-26 / 17 : ℚ), 0, 0, -1, (1 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (-7 / 4 : ℚ), (-3 / 4 : ℚ), (3 / 4 : ℚ), (-7 / 2 : ℚ)], ![0, (-7 / 2 : ℚ), 0, (3 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -1, 0, 0, (-5 / 2 : ℚ)], ![(-1 / 2 : ℚ), -2, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 26 : ℚ), (-1 / 26 : ℚ), (11 / 26 : ℚ), 0, (-1 / 13 : ℚ)], ![(-33 / 26 : ℚ), 0, (1 / 13 : ℚ), (1 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 7 : ℚ), 0, (8 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ)], ![(-11 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 11 : ℚ), (-19 / 11 : ℚ), (-7 / 11 : ℚ), (-36 / 11 : ℚ), (-18 / 11 : ℚ)], ![0, (-36 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 7 : ℚ), (-3 / 7 : ℚ), (-20 / 7 : ℚ), (-20 / 7 : ℚ)], ![0, (-20 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 14 : ℚ), (-1 / 14 : ℚ), (1 / 2 : ℚ), 0, (-1 / 14 : ℚ)], ![(-17 / 14 : ℚ), 0, (1 / 7 : ℚ), 0, (-1 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 8 : ℚ), 0, (1 / 8 : ℚ), (13 / 8 : ℚ), (-3 / 8 : ℚ)], ![(-13 / 8 : ℚ), (5 / 8 : ℚ), (-5 / 8 : ℚ), (13 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 8 : ℚ), (1 / 8 : ℚ), 0, (-3 / 8 : ℚ)], ![0, (-17 / 8 : ℚ), (1 / 2 : ℚ), 0, (29 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), (7 / 10 : ℚ), 0], ![(-13 / 10 : ℚ), 0, (-3 / 10 : ℚ), (7 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 1], ![(-5 / 4 : ℚ), (1 / 4 : ℚ), (5 / 4 : ℚ), (-5 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-3 / 4 : ℚ)], ![0, (-9 / 4 : ℚ), 0, 0, (13 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, (-3 / 4 : ℚ), -2], ![0, (-9 / 4 : ℚ), 0, (13 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, (7 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![(-7 / 4 : ℚ), (3 / 4 : ℚ), (7 / 4 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 6 : ℚ), 0, (-23 / 6 : ℚ), (-11 / 6 : ℚ)], ![0, (-13 / 6 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-9 / 4 : ℚ)], ![0, (-9 / 4 : ℚ), 0, (13 / 4 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-20 / 17 : ℚ), 0, 0, -1, (8 / 17 : ℚ)], ![(-43 / 34 : ℚ), 0, -1, -1, (35 / 34 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, -1, 0], ![(-7 / 4 : ℚ), 0, -1, -1, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, 0, -1, (-1 / 2 : ℚ)], ![(-3 / 2 : ℚ), 0, -1, -1, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 17 : ℚ), (-1 / 17 : ℚ), (7 / 17 : ℚ), 0, 0], ![(-24 / 17 : ℚ), 0, 0, (2 / 17 : ℚ), (1 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 26 : ℚ), (-1 / 26 : ℚ), (5 / 26 : ℚ), 0, 0], ![(-29 / 26 : ℚ), 0, 0, (1 / 26 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-22 / 17 : ℚ), (-1 / 17 : ℚ), (7 / 17 : ℚ), 0, 0], ![(-24 / 17 : ℚ), 0, 0, (2 / 17 : ℚ), (2 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 26 : ℚ), (-1 / 26 : ℚ), (5 / 26 : ℚ), 0, 0], ![(-29 / 26 : ℚ), 0, 0, (1 / 13 : ℚ), 0]] }
]

theorem conicDetC32A_checked : conicDetC32A.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
