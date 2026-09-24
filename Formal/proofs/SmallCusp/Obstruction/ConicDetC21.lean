import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC21 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .x), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-23 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 5 : ℚ)], ![0, (-1 / 20 : ℚ), (-9 / 4 : ℚ), (-11 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 32 : ℚ), (1 / 16 : ℚ), (-5 / 4 : ℚ), (-1 / 16 : ℚ), (-3 / 8 : ℚ)], ![(-3 / 32 : ℚ), 0, (-39 / 16 : ℚ), (-21 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, (-23 / 20 : ℚ), 0, 0], ![(-3 / 10 : ℚ), (-1 / 20 : ℚ), (-9 / 4 : ℚ), (-21 / 20 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 28 : ℚ), 0, (-17 / 14 : ℚ), (-1 / 14 : ℚ), (-16 / 7 : ℚ)], ![(-1 / 28 : ℚ), (-1 / 14 : ℚ), (-33 / 14 : ℚ), (-8 / 7 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-17 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 12 : ℚ), (-19 / 12 : ℚ), 0, (1 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 34 : ℚ), (-49 / 34 : ℚ), (-3 / 34 : ℚ), (21 / 34 : ℚ), (35 / 34 : ℚ)], ![(49 / 34 : ℚ), (-55 / 34 : ℚ), 0, (-21 / 34 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-5 / 24 : ℚ), (-23 / 24 : ℚ), 0, (1 / 24 : ℚ)], ![(1 / 12 : ℚ), (-5 / 24 : ℚ), (-11 / 6 : ℚ), 0, (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(51 / 37 : ℚ), 0, (-55 / 37 : ℚ), (-18 / 37 : ℚ), (7 / 37 : ℚ)], ![(-51 / 37 : ℚ), (-6 / 37 : ℚ), (-104 / 37 : ℚ), (18 / 37 : ℚ), (38 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 24 : ℚ), 0, (-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)], ![(-5 / 24 : ℚ), (-1 / 12 : ℚ), (-7 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (-35 / 24 : ℚ)], ![0, (-1 / 24 : ℚ), (-53 / 24 : ℚ), (1 / 8 : ℚ), (5 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 30 : ℚ), (7 / 30 : ℚ), (11 / 15 : ℚ)], ![(7 / 6 : ℚ), (-37 / 30 : ℚ), 0, (-7 / 30 : ℚ), (23 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (-2 / 5 : ℚ), -1, 0, (-9 / 5 : ℚ)], ![(3 / 10 : ℚ), (-2 / 5 : ℚ), (-9 / 5 : ℚ), 0, (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), (-3 / 10 : ℚ), (-1 / 5 : ℚ)], ![(-1 / 10 : ℚ), 0, (-23 / 10 : ℚ), (1 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 12 : ℚ), (1 / 12 : ℚ), (-4 / 3 : ℚ), (-5 / 12 : ℚ), 0], ![(-5 / 12 : ℚ), 0, (-31 / 12 : ℚ), 0, (5 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 8 : ℚ), (-5 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 13 : ℚ), (-18 / 13 : ℚ), (-1 / 13 : ℚ), (11 / 13 : ℚ), (-2 / 13 : ℚ)], ![(15 / 13 : ℚ), (-20 / 13 : ℚ), 0, (2 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 11 : ℚ), (-16 / 11 : ℚ), (-1 / 11 : ℚ), 1, 0], ![(15 / 11 : ℚ), (-18 / 11 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 20 : ℚ), (-23 / 20 : ℚ), (-1 / 20 : ℚ), (7 / 20 : ℚ), 0], ![(11 / 20 : ℚ), (-23 / 20 : ℚ), 0, (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 8 : ℚ), 0, (-5 / 4 : ℚ), 0, (-3 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, (-19 / 8 : ℚ), (3 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 16 : ℚ), (-19 / 16 : ℚ), (-1 / 16 : ℚ), (-11 / 8 : ℚ)], ![(-1 / 8 : ℚ), (1 / 16 : ℚ), (-9 / 4 : ℚ), (-1 / 16 : ℚ), (11 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-3 / 2 : ℚ), 0, (-5 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-5 / 2 : ℚ), 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (-1 / 3 : ℚ), -1, 0, 0], ![(-1 / 3 : ℚ), (-1 / 2 : ℚ), -2, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 10 : ℚ), 0, (-29 / 20 : ℚ), (3 / 20 : ℚ), (-59 / 20 : ℚ)], ![(-29 / 20 : ℚ), (-3 / 20 : ℚ), (-11 / 4 : ℚ), 1, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 15 : ℚ), 0, (-11 / 10 : ℚ), (1 / 30 : ℚ), (-5 / 3 : ℚ)], ![(-3 / 10 : ℚ), (-1 / 30 : ℚ), (-13 / 6 : ℚ), (1 / 5 : ℚ), (31 / 30 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(14 / 25 : ℚ), 0, (-29 / 25 : ℚ), (2 / 25 : ℚ), (-56 / 25 : ℚ)], ![(-16 / 25 : ℚ), 0, (-56 / 25 : ℚ), (2 / 5 : ℚ), (-56 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 30 : ℚ), (1 / 15 : ℚ), (-19 / 15 : ℚ), (1 / 15 : ℚ), (-28 / 15 : ℚ)], ![(-1 / 10 : ℚ), 0, (-37 / 15 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 29 : ℚ), 0, (-41 / 29 : ℚ), 0, (-56 / 29 : ℚ)], ![(-2 / 29 : ℚ), (-4 / 29 : ℚ), (-78 / 29 : ℚ), (-4 / 29 : ℚ), (48 / 29 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 28 : ℚ), (-33 / 28 : ℚ), (-1 / 28 : ℚ), (-3 / 14 : ℚ), (-3 / 28 : ℚ)], ![(-1 / 28 : ℚ), (-5 / 4 : ℚ), 0, (1 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 6 : ℚ), (-3 / 2 : ℚ), (-9 / 4 : ℚ)], ![(-1 / 12 : ℚ), 0, (-9 / 4 : ℚ), (5 / 12 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 11 : ℚ), (-16 / 11 : ℚ), (-1 / 11 : ℚ), 0, 0], ![(15 / 11 : ℚ), (-18 / 11 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 5 : ℚ), (-16 / 5 : ℚ), (-16 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-16 / 5 : ℚ), (2 / 5 : ℚ), (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 12 : ℚ), (-7 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 4 : ℚ), (5 / 12 : ℚ)], ![(7 / 12 : ℚ), (-5 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 36 : ℚ), (-1 / 18 : ℚ), (-7 / 36 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 36 : ℚ), (-13 / 12 : ℚ), (7 / 36 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, (-1 / 8 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 16 : ℚ), (-17 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 16 : ℚ), 0, 0, (-1 / 8 : ℚ), (1 / 8 : ℚ)], ![(-3 / 16 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 11 : ℚ), (-4 / 11 : ℚ), (-26 / 11 : ℚ)], ![0, (-1 / 11 : ℚ), (-13 / 11 : ℚ), (4 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 20 : ℚ), (-1 / 5 : ℚ), (-9 / 4 : ℚ)], ![0, (-1 / 20 : ℚ), (-11 / 10 : ℚ), (1 / 5 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 36 : ℚ), (-2 / 9 : ℚ), (-1 / 18 : ℚ), 0, (-31 / 18 : ℚ)], ![(7 / 36 : ℚ), (-2 / 9 : ℚ), (-8 / 9 : ℚ), 0, (-31 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), (-1 / 20 : ℚ), (-3 / 20 : ℚ), (-3 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-3 / 4 : ℚ), (-7 / 20 : ℚ), (1 / 20 : ℚ), (-3 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, (-3 / 8 : ℚ), (-7 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-7 / 6 : ℚ), 0, 1, -1], ![1, (-4 / 3 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 24 : ℚ), (-1 / 8 : ℚ), (-13 / 6 : ℚ)], ![(-1 / 24 : ℚ), (-1 / 24 : ℚ), (-13 / 12 : ℚ), (1 / 24 : ℚ), (-7 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-13 / 12 : ℚ), (-1 / 24 : ℚ), (5 / 24 : ℚ), (-1 / 24 : ℚ)], ![(7 / 24 : ℚ), (-9 / 8 : ℚ), 0, (1 / 24 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 20 : ℚ), (-11 / 10 : ℚ), (-1 / 20 : ℚ), (1 / 5 : ℚ), 0], ![(3 / 10 : ℚ), (-11 / 10 : ℚ), 0, (1 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, 0, 0, (-1 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-7 / 6 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, (-10 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (-1 / 8 : ℚ), 0, (-19 / 8 : ℚ)], ![(-1 / 16 : ℚ), 0, (-9 / 8 : ℚ), 0, (13 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (-21 / 20 : ℚ), (-1 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), -3]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), 0, (-1 / 11 : ℚ), 0, (-26 / 11 : ℚ)], ![(-1 / 22 : ℚ), (-1 / 11 : ℚ), (-13 / 11 : ℚ), (-1 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 9 : ℚ), 0, (-28 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-13 / 9 : ℚ), (-2 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 11 : ℚ), (-27 / 11 : ℚ), (-26 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (-13 / 11 : ℚ), (1 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 14 : ℚ), (-16 / 7 : ℚ), (-31 / 14 : ℚ)], ![(-1 / 14 : ℚ), 0, (-8 / 7 : ℚ), (-5 / 14 : ℚ), (-31 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-9 / 7 : ℚ), (-1 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, (-10 / 7 : ℚ), 0, (1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 8 : ℚ)], ![0, (-3 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (-1 / 10 : ℚ)], ![(1 / 5 : ℚ), (-3 / 10 : ℚ), 0, (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)], ![(1 / 5 : ℚ), (-3 / 10 : ℚ), 0, (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-5 / 9 : ℚ), 0, 0, 0], ![(4 / 9 : ℚ), (-5 / 9 : ℚ), 0, (2 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ)], ![0, 0, (1 / 4 : ℚ), 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-7 / 2 : ℚ)], ![0, 0, (1 / 4 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (-5 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 15 : ℚ), (16 / 15 : ℚ), (8 / 15 : ℚ), (-4 / 15 : ℚ)], ![0, (-4 / 15 : ℚ), (-16 / 15 : ℚ), (-16 / 15 : ℚ), (-4 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 8 : ℚ), 0, (-1 / 8 : ℚ)], ![0, (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 3 : ℚ), 0, (-4 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), 0, 0, (-12 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, 0, (4 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-35 / 18 : ℚ), (7 / 6 : ℚ), (35 / 18 : ℚ), 0], ![(25 / 18 : ℚ), (-35 / 18 : ℚ), (1 / 9 : ℚ), (35 / 18 : ℚ), (1 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), 0, (-5 / 9 : ℚ), 0, (-34 / 9 : ℚ)], ![(-1 / 9 : ℚ), 0, (2 / 9 : ℚ), 0, (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (1 / 10 : ℚ)], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, (-1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, (-1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 10 : ℚ)], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0], ![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (3 / 2 : ℚ), (-1 / 2 : ℚ)], ![(3 / 2 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), (3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![0, 0, 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 2 : ℚ), (-7 / 4 : ℚ), (7 / 4 : ℚ), (-7 / 4 : ℚ), 0], ![0, (-7 / 4 : ℚ), (7 / 4 : ℚ), (-7 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), -2], ![0, (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, (-7 / 2 : ℚ), -2], ![(-1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (-1 / 2 : ℚ), (-11 / 4 : ℚ), (-3 / 2 : ℚ)], ![-1, (1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, 0, (-26 / 7 : ℚ), (-12 / 7 : ℚ)], ![(-1 / 7 : ℚ), 0, 0, (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (-13 / 4 : ℚ), 0], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 10 : ℚ), (-3 / 5 : ℚ), (-7 / 10 : ℚ)], ![(-3 / 10 : ℚ), (-3 / 10 : ℚ), (-3 / 5 : ℚ), (-9 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (4 / 9 : ℚ), 0, (-8 / 9 : ℚ)], ![0, (-2 / 3 : ℚ), (-4 / 3 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(16 / 17 : ℚ), (16 / 17 : ℚ), (8 / 17 : ℚ), 0, (-44 / 17 : ℚ)], ![(-24 / 17 : ℚ), (16 / 17 : ℚ), 0, 0, (-44 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-3 / 5 : ℚ), (2 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), -1, (-8 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (3 / 7 : ℚ), 0, 0], ![(1 / 14 : ℚ), (-1 / 2 : ℚ), (-19 / 14 : ℚ), (3 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ), (-16 / 7 : ℚ), (-10 / 7 : ℚ)], ![(-6 / 7 : ℚ), 0, 0, (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (4 / 9 : ℚ), (-10 / 9 : ℚ), 0], ![(-1 / 9 : ℚ), (-1 / 3 : ℚ), (-11 / 9 : ℚ), (4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, 0, (-4 / 3 : ℚ), (-2 / 3 : ℚ)], ![(-2 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), (-9 / 8 : ℚ)], ![(-3 / 4 : ℚ), 0, 0, (-1 / 2 : ℚ), (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ), (-20 / 11 : ℚ), (-14 / 11 : ℚ)], ![(-6 / 11 : ℚ), 0, 0, (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-13 / 10 : ℚ), (1 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-12 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (2 / 11 : ℚ), (-18 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (-4 / 11 : ℚ), (-16 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 8 : ℚ), (-11 / 4 : ℚ), -5, (1 / 4 : ℚ), 0], ![(29 / 16 : ℚ), (-1 / 4 : ℚ), (-5 / 2 : ℚ), (-31 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 7 : ℚ), (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-8 / 7 : ℚ), 0, (-2 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 17 : ℚ), (-8 / 17 : ℚ), (8 / 17 : ℚ), (8 / 17 : ℚ), (-100 / 17 : ℚ)], ![(-10 / 17 : ℚ), (-8 / 17 : ℚ), 0, (-24 / 17 : ℚ), (-96 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), 0, (1 / 8 : ℚ), (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 20 : ℚ), (3 / 20 : ℚ), (1 / 20 : ℚ), (-8 / 5 : ℚ)], ![(-3 / 20 : ℚ), (-3 / 20 : ℚ), 0, (-1 / 20 : ℚ), (-29 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), (-38 / 13 : ℚ), (-68 / 13 : ℚ), 0, 0], ![0, (-4 / 13 : ℚ), (-34 / 13 : ℚ), (-76 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (-8 / 3 : ℚ)], ![-1, 0, (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (6 / 41 : ℚ), (24 / 41 : ℚ), (8 / 41 : ℚ), (-260 / 41 : ℚ)], ![(-24 / 41 : ℚ), (-24 / 41 : ℚ), 0, (-8 / 41 : ℚ), (-248 / 41 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-23 / 10 : ℚ), (-22 / 5 : ℚ), (-7 / 10 : ℚ), 0], ![0, (-1 / 10 : ℚ), (-11 / 5 : ℚ), (-23 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(31 / 28 : ℚ), (-9 / 28 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 4 : ℚ)], ![(-31 / 28 : ℚ), (-3 / 14 : ℚ), (-3 / 28 : ℚ), (-16 / 7 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (-11 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 24 : ℚ), 0, 0, (-9 / 8 : ℚ), (1 / 12 : ℚ)], ![(-5 / 8 : ℚ), (-1 / 12 : ℚ), (-1 / 24 : ℚ), (-13 / 6 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ), (-17 / 9 : ℚ), (-32 / 9 : ℚ)], ![(-8 / 9 : ℚ), 0, 0, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 60 : ℚ), 0, 0, (-1 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 60 : ℚ), (-1 / 10 : ℚ), (-1 / 20 : ℚ), (-11 / 10 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 16 : ℚ), (-17 / 16 : ℚ), (-35 / 16 : ℚ), (-1 / 8 : ℚ), (3 / 16 : ℚ)], ![(1 / 4 : ℚ), 0, (-9 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-8 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-41 / 16 : ℚ), (-19 / 4 : ℚ), (31 / 16 : ℚ), 0], ![(1 / 16 : ℚ), (-3 / 16 : ℚ), (-19 / 8 : ℚ), (-31 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ), 0, (-10 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(137 / 62 : ℚ), (-27 / 124 : ℚ), (4 / 31 : ℚ), (-17 / 62 : ℚ), (-140 / 31 : ℚ)], ![(-137 / 62 : ℚ), (-47 / 124 : ℚ), 0, (17 / 62 : ℚ), (-138 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 16 : ℚ), (-33 / 16 : ℚ), (-17 / 4 : ℚ), (19 / 16 : ℚ), 0], ![(5 / 4 : ℚ), 0, (-17 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (-9 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, 0, (-71 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 10 : ℚ), (-23 / 10 : ℚ), (-22 / 5 : ℚ), (1 / 10 : ℚ), 0], ![(8 / 5 : ℚ), (-1 / 10 : ℚ), (-11 / 5 : ℚ), (-19 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 22 : ℚ), (-5 / 2 : ℚ), (-49 / 11 : ℚ), (2 / 11 : ℚ), (-1 / 11 : ℚ)], ![(25 / 22 : ℚ), (-2 / 11 : ℚ), (-51 / 22 : ℚ), (-37 / 22 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-23 / 10 : ℚ), (-22 / 5 : ℚ), (-7 / 10 : ℚ), 0], ![0, (-1 / 10 : ℚ), (-11 / 5 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (2 / 3 : ℚ), (-8 / 3 : ℚ)], ![-1, 0, (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-16 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-30 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 7 : ℚ), (1 / 7 : ℚ), (-10 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 13 : ℚ), (4 / 13 : ℚ), (-80 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-38 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (8 / 21 : ℚ), (8 / 21 : ℚ), (-16 / 3 : ℚ)], ![(-8 / 21 : ℚ), (-8 / 21 : ℚ), (-16 / 21 : ℚ), (-16 / 21 : ℚ), (-36 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-7 / 6 : ℚ), 0, (1 / 6 : ℚ), (-7 / 6 : ℚ)], ![(-1 / 18 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 2 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 7 : ℚ), (2 / 7 : ℚ), (4 / 7 : ℚ), (2 / 7 : ℚ), (-12 / 7 : ℚ)], ![(-8 / 7 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (-13 / 11 : ℚ), (1 / 11 : ℚ), (-7 / 11 : ℚ), (-1 / 11 : ℚ)], ![(-1 / 22 : ℚ), (-1 / 11 : ℚ), (-27 / 11 : ℚ), (-26 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-50 / 19 : ℚ), (4 / 19 : ℚ), 0, (-12 / 19 : ℚ)], ![(-4 / 19 : ℚ), (-4 / 19 : ℚ), (-104 / 19 : ℚ), (-100 / 19 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (3 / 8 : ℚ), -1], ![(-3 / 8 : ℚ), 0, (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 24 : ℚ), (-5 / 2 : ℚ), (1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 3 : ℚ), (-16 / 3 : ℚ), -5, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0, -2], ![0, (-1 / 3 : ℚ), 0, -4, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, 0, -1, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-11 / 7 : ℚ), (2 / 7 : ℚ), (-11 / 7 : ℚ), 0], ![0, (-2 / 7 : ℚ), (-24 / 7 : ℚ), (-11 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-5 / 2 : ℚ), (1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ)], ![(-1 / 18 : ℚ), (-1 / 6 : ℚ), (-31 / 6 : ℚ), (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 11 : ℚ), (-34 / 11 : ℚ), (8 / 11 : ℚ), (-34 / 11 : ℚ), 0], ![(-2 / 11 : ℚ), (-8 / 11 : ℚ), (-76 / 11 : ℚ), (-34 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 42 : ℚ), (-8 / 7 : ℚ), (-1 / 14 : ℚ), (1 / 7 : ℚ), (3 / 7 : ℚ)], ![(1 / 42 : ℚ), (-1 / 7 : ℚ), 0, (-17 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, 0, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-13 / 9 : ℚ), (-1 / 9 : ℚ), (2 / 9 : ℚ), (-2 / 9 : ℚ)], ![(-1 / 9 : ℚ), (-2 / 9 : ℚ), 0, (-28 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 24 : ℚ), 0, (-9 / 8 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)], ![(-5 / 8 : ℚ), (-1 / 12 : ℚ), (-13 / 6 : ℚ), (-1 / 12 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), -3], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-13 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, 0, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), (-17 / 7 : ℚ)], ![0, (-2 / 7 : ℚ), 0, (-20 / 7 : ℚ), (-16 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, (-1 / 8 : ℚ), (-9 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-124 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-25 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-3 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, 0, 0, (-7 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-9 / 5 : ℚ), (-4 / 5 : ℚ), (-32 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 8 : ℚ), (1 / 8 : ℚ), (1 / 2 : ℚ), (-7 / 8 : ℚ), (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, 0, (7 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 6 : ℚ), (1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, 0, -2, (1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 17 : ℚ), (-11 / 17 : ℚ), (-89 / 17 : ℚ)], ![0, (-3 / 17 : ℚ), (-6 / 17 : ℚ), (11 / 17 : ℚ), (-43 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(6 / 5 : ℚ), (2 / 5 : ℚ), (4 / 5 : ℚ), 0, (-16 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 31 : ℚ), (-74 / 31 : ℚ), (8 / 31 : ℚ), (59 / 31 : ℚ), (-4 / 31 : ℚ)], ![(1 / 31 : ℚ), (-8 / 31 : ℚ), (-156 / 31 : ℚ), (-59 / 31 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (-20 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0], ![0, 0, (-3 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(17 / 16 : ℚ), (3 / 16 : ℚ), 2, (-17 / 16 : ℚ), (17 / 16 : ℚ)], ![(-17 / 16 : ℚ), 0, 0, 0, (17 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-15 / 7 : ℚ), (1 / 7 : ℚ), (2 / 7 : ℚ), (-1 / 7 : ℚ)], ![(3 / 7 : ℚ), 0, (-31 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 7 : ℚ), (2 / 7 : ℚ), (4 / 7 : ℚ), (-12 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-8 / 7 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-15 / 7 : ℚ), (2 / 7 : ℚ), (3 / 7 : ℚ), (-1 / 7 : ℚ)], ![(5 / 7 : ℚ), 0, (-32 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, (2 / 3 : ℚ), 0, -1], ![-1, 0, (-2 / 3 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-9 / 8 : ℚ), (13 / 8 : ℚ), 0, 0], ![(-1 / 16 : ℚ), (-1 / 8 : ℚ), (-19 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 18 : ℚ), 0, (1 / 9 : ℚ), (-11 / 6 : ℚ), (-91 / 18 : ℚ)], ![(-26 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), (-11 / 9 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-9 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-30 / 7 : ℚ)], ![0, 0, (-20 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-11 / 9 : ℚ), (1 / 9 : ℚ), (-1 / 9 : ℚ), (-35 / 18 : ℚ)], ![(-1 / 18 : ℚ), (-1 / 9 : ℚ), (-23 / 9 : ℚ), 0, (-17 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 11 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ), (-58 / 11 : ℚ)], ![(-15 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (9 / 11 : ℚ), (-28 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-21 / 17 : ℚ), (4 / 17 : ℚ), (4 / 17 : ℚ), (-40 / 17 : ℚ)], ![(-4 / 17 : ℚ), (-4 / 17 : ℚ), (-46 / 17 : ℚ), (-8 / 17 : ℚ), (-38 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-9 / 4 : ℚ), (5 / 6 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 36 : ℚ), (-1 / 12 : ℚ), (-55 / 12 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 3 : ℚ), (1 / 6 : ℚ), 3, (2 / 3 : ℚ), (-13 / 3 : ℚ)], ![-2, 0, 0, (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-8 / 3 : ℚ), 2, (-5 / 3 : ℚ), 0], ![(-1 / 9 : ℚ), (-4 / 9 : ℚ), (-52 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-14 / 5 : ℚ), (4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, 0, (-32 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 21 : ℚ), (-22 / 7 : ℚ), (8 / 21 : ℚ), (-8 / 21 : ℚ), (-16 / 21 : ℚ)], ![0, (-8 / 21 : ℚ), (-20 / 3 : ℚ), 0, (8 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-9 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, -5, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 5 : ℚ), (-47 / 10 : ℚ), (-13 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-23 / 5 : ℚ), (-12 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-5 / 4 : ℚ), (-5 / 8 : ℚ), (-5 / 4 : ℚ), 0], ![0, (-1 / 8 : ℚ), (-5 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), (-14 / 5 : ℚ), 0, (-32 / 15 : ℚ), (-4 / 15 : ℚ)], ![0, (-4 / 15 : ℚ), (-28 / 5 : ℚ), (-14 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), (-5 / 2 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 2 : ℚ), (-7 / 6 : ℚ), (-5 / 2 : ℚ), 0], ![(-1 / 12 : ℚ), (-1 / 3 : ℚ), -5, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-13 / 10 : ℚ), 0, (-13 / 10 : ℚ), (9 / 10 : ℚ)], ![(1 / 10 : ℚ), (-3 / 10 : ℚ), 0, (-13 / 5 : ℚ), (-9 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, 0, (-14 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (-6 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 15 : ℚ), (-1 / 5 : ℚ), 0, (-12 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(9 / 17 : ℚ), 0, (-37 / 34 : ℚ), 0, (3 / 34 : ℚ)], ![(-21 / 34 : ℚ), (-3 / 34 : ℚ), (-37 / 17 : ℚ), 0, (6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-3 / 2 : ℚ), 0, (-3 / 2 : ℚ), (-9 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 2 : ℚ), 0, -3, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-5 / 4 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, 0, 0, -3, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 15 : ℚ), (-9 / 5 : ℚ), 0, (-9 / 5 : ℚ), (-16 / 5 : ℚ)], ![(-4 / 15 : ℚ), (-4 / 5 : ℚ), 0, (-18 / 5 : ℚ), (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-20 / 17 : ℚ), (-3 / 17 : ℚ), (-43 / 17 : ℚ), (11 / 17 : ℚ)], ![0, (-3 / 17 : ℚ), 0, (-89 / 17 : ℚ), (-11 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (-21 / 20 : ℚ), (-1 / 20 : ℚ), (-43 / 20 : ℚ), (1 / 5 : ℚ)], ![(1 / 4 : ℚ), 0, 0, (-87 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), 0, (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 9 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-23 / 20 : ℚ), (-3 / 20 : ℚ), (-49 / 20 : ℚ), (-11 / 4 : ℚ)], ![(-3 / 20 : ℚ), (-3 / 20 : ℚ), 0, (-101 / 20 : ℚ), (-13 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 11 : ℚ), (-2 / 11 : ℚ), (-28 / 11 : ℚ), (-25 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-58 / 11 : ℚ), (-24 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 16 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ), (-7 / 16 : ℚ), (-5 / 16 : ℚ)], ![(-3 / 16 : ℚ), 0, 0, (7 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -1, (-1 / 2 : ℚ), 0, 0], ![(1 / 8 : ℚ), 0, (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-43 / 17 : ℚ), 0, (32 / 17 : ℚ), (-3 / 17 : ℚ)], ![0, (-3 / 17 : ℚ), (-86 / 17 : ℚ), (-32 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(6 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (-16 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 31 : ℚ), (-74 / 31 : ℚ), (-32 / 31 : ℚ), (59 / 31 : ℚ), (-4 / 31 : ℚ)], ![(1 / 31 : ℚ), (-8 / 31 : ℚ), (-148 / 31 : ℚ), (-59 / 31 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ)], ![0, 0, (-43 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, 0, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 1, 0, 0], ![0, 0, (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (-20 / 9 : ℚ), 0, (4 / 9 : ℚ), (-2 / 9 : ℚ)], ![(2 / 3 : ℚ), 0, (-14 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, 0, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-13 / 6 : ℚ), -1, (1 / 2 : ℚ), (-1 / 6 : ℚ)], ![(5 / 6 : ℚ), 0, (-14 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 2 : ℚ), 0, 0], ![0, 0, (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-7 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0], ![(-1 / 12 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-13 / 11 : ℚ), (-25 / 22 : ℚ), (-15 / 44 : ℚ), (-125 / 44 : ℚ)], ![0, (-1 / 11 : ℚ), (-26 / 11 : ℚ), 0, (-12 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-81 / 20 : ℚ)], ![0, 0, (-43 / 20 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-13 / 11 : ℚ), (-25 / 22 : ℚ), (-15 / 44 : ℚ), (-43 / 22 : ℚ)], ![0, (-1 / 11 : ℚ), (-26 / 11 : ℚ), 0, (-21 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-28 / 11 : ℚ), 0, (2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-2 / 11 : ℚ), (-56 / 11 : ℚ), (-19 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-3 / 4 : ℚ), (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-25 / 11 : ℚ), (-13 / 11 : ℚ), (2 / 11 : ℚ), (-6 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-50 / 11 : ℚ), (-16 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), 0, (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 12 : ℚ), (-9 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(10 / 17 : ℚ), (6 / 17 : ℚ), (6 / 17 : ℚ), (20 / 17 : ℚ), (-56 / 17 : ℚ)], ![(-22 / 17 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-9 / 4 : ℚ), (-7 / 12 : ℚ), (-5 / 4 : ℚ), 0], ![0, (-1 / 6 : ℚ), (-9 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-22 / 9 : ℚ), 0, (-4 / 9 : ℚ), (-4 / 9 : ℚ)], ![0, 0, (-16 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-26 / 19 : ℚ), (-62 / 19 : ℚ), (-44 / 19 : ℚ), (-8 / 19 : ℚ), (20 / 19 : ℚ)], ![0, (-8 / 19 : ℚ), (-124 / 19 : ℚ), 0, (24 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), -2, (-5 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-11 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, (-24 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 22 : ℚ), (-28 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (-6 / 11 : ℚ)], ![(-3 / 22 : ℚ), (-4 / 11 : ℚ), (-56 / 11 : ℚ), 0, (-2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (-2 / 3 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 12 : ℚ), (-9 / 4 : ℚ), (-53 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(17 / 6 : ℚ), (3 / 2 : ℚ), -3, (1 / 4 : ℚ), -2], ![(-17 / 6 : ℚ), (-1 / 4 : ℚ), (-23 / 4 : ℚ), 0, 2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-27 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 3 : ℚ), (7 / 12 : ℚ), (-9 / 4 : ℚ), 0, (1 / 12 : ℚ)], ![(-7 / 4 : ℚ), (-1 / 12 : ℚ), (-53 / 12 : ℚ), (-1 / 12 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (-10 / 3 : ℚ), (1 / 3 : ℚ), (-19 / 3 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 3 : ℚ), (-19 / 3 : ℚ), 0, -3]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-50 / 17 : ℚ), (-8 / 17 : ℚ), (-96 / 17 : ℚ)], ![0, 0, (-92 / 17 : ℚ), (-16 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 5 : ℚ), (3 / 10 : ℚ)], ![0, (-1 / 10 : ℚ), 0, (-23 / 10 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (-21 / 20 : ℚ), (-1 / 20 : ℚ), (-21 / 10 : ℚ), (1 / 5 : ℚ)], ![(1 / 4 : ℚ), 0, 0, (-43 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ), 0, (1 / 4 : ℚ)], ![(1 / 2 : ℚ), 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, (-4 / 3 : ℚ), 0, 0], ![(1 / 6 : ℚ), 0, (-4 / 3 : ℚ), 0, 0]] }
]

theorem conicDetC21_checked : conicDetC21.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
