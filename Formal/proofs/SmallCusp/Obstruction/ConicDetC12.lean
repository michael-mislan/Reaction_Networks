import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC12 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 38 : ℚ), (-81 / 38 : ℚ), (-1 / 38 : ℚ), (9 / 38 : ℚ), (3 / 19 : ℚ)], ![(11 / 38 : ℚ), (-41 / 38 : ℚ), 0, 0, (1 / 38 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), -2, (-1 / 4 : ℚ), 0, 0], ![(1 / 6 : ℚ), -1, (-1 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-27 / 10 : ℚ), 0, (1 / 2 : ℚ), 0], ![(3 / 5 : ℚ), (-7 / 5 : ℚ), (1 / 10 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, (2 / 5 : ℚ), (-2 / 5 : ℚ)], ![(2 / 5 : ℚ), (-7 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-11 / 4 : ℚ), 0, (1 / 2 : ℚ), 0], ![(3 / 4 : ℚ), (-11 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-36 / 11 : ℚ), 0, (28 / 33 : ℚ), 0], ![(40 / 33 : ℚ), (-19 / 11 : ℚ), (2 / 11 : ℚ), (-2 / 3 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 32 : ℚ), (-137 / 32 : ℚ), 0, (5 / 4 : ℚ), 0], ![(23 / 16 : ℚ), (-35 / 16 : ℚ), (1 / 2 : ℚ), (-37 / 32 : ℚ), (3 / 64 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -3, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)], ![(2 / 3 : ℚ), (-3 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-31 / 12 : ℚ), 0, (7 / 12 : ℚ), 0], ![(2 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-19 / 8 : ℚ), 0, (3 / 8 : ℚ), (-3 / 8 : ℚ)], ![(3 / 8 : ℚ), (-5 / 4 : ℚ), 0, 0, (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-11 / 5 : ℚ), (-1 / 20 : ℚ), (1 / 4 : ℚ), 0], ![(3 / 10 : ℚ), (-11 / 10 : ℚ), 0, (1 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-29 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 2 : ℚ), 0], ![(7 / 12 : ℚ), (-5 / 4 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-17 / 4 : ℚ), (1 / 3 : ℚ), (17 / 12 : ℚ), 0], ![(3 / 2 : ℚ), (-13 / 6 : ℚ), (5 / 12 : ℚ), (1 / 12 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-3 / 8 : ℚ), 0, 0], ![(1 / 8 : ℚ), -1, (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-19 / 8 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![(1 / 8 : ℚ), (-5 / 4 : ℚ), 0, (-3 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-10 / 3 : ℚ), 0, 0, (4 / 9 : ℚ)], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 9 : ℚ), (-7 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-36 / 11 : ℚ), 0, 0, 0], ![(2 / 11 : ℚ), (-19 / 11 : ℚ), (2 / 11 : ℚ), (-8 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ)], ![(1 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (-11 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-9 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-9 / 8 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-20 / 7 : ℚ), 0, (-5 / 7 : ℚ), 0], ![(1 / 7 : ℚ), (-11 / 7 : ℚ), 0, (-5 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-16 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0], ![0, (-8 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-19 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ)], ![0, (-10 / 7 : ℚ), 0, (1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -4, 0, 0, 0], ![(1 / 6 : ℚ), -2, (1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 25 : ℚ), (-57 / 25 : ℚ), 0, (-3 / 25 : ℚ), (7 / 25 : ℚ)], ![(13 / 25 : ℚ), (-6 / 5 : ℚ), (3 / 25 : ℚ), (1 / 50 : ℚ), (-4 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-73 / 33 : ℚ), 0, (-1 / 11 : ℚ), (14 / 33 : ℚ)], ![(17 / 33 : ℚ), (-38 / 33 : ℚ), (1 / 11 : ℚ), (1 / 66 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-7 / 6 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-8 / 3 : ℚ), 0, (-2 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (-5 / 3 : ℚ), (2 / 9 : ℚ), (1 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), (-14 / 5 : ℚ), (-3 / 10 : ℚ), (-7 / 10 : ℚ), (7 / 10 : ℚ)], ![(7 / 10 : ℚ), (-17 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, 0], ![0, (-3 / 2 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-8 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-3 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 35 : ℚ), (-74 / 35 : ℚ), (-3 / 70 : ℚ), (3 / 10 : ℚ), (5 / 14 : ℚ)], ![(33 / 70 : ℚ), (-11 / 10 : ℚ), 0, 0, (3 / 35 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-7 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)], ![(1 / 2 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-43 / 18 : ℚ), 0, (4 / 9 : ℚ), 0], ![(11 / 18 : ℚ), (-23 / 18 : ℚ), (1 / 6 : ℚ), (-5 / 18 : ℚ), (-5 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 2 : ℚ), 0, 1, -1], ![1, -2, 0, -1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-9 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 12 : ℚ)], ![(1 / 2 : ℚ), (-9 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 25 : ℚ), (-54 / 25 : ℚ), (-3 / 50 : ℚ), (11 / 50 : ℚ), 0], ![(23 / 50 : ℚ), (-57 / 50 : ℚ), 0, (-1 / 10 : ℚ), (3 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 13 : ℚ), (-61 / 13 : ℚ), 0, (21 / 13 : ℚ), 0], ![(27 / 13 : ℚ), (-32 / 13 : ℚ), (24 / 13 : ℚ), (-18 / 13 : ℚ), (3 / 26 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-17 / 8 : ℚ), (-1 / 16 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ)], ![(3 / 16 : ℚ), (-17 / 16 : ℚ), 0, 0, (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-67 / 30 : ℚ), 0, (7 / 15 : ℚ), 0], ![(17 / 30 : ℚ), (-7 / 6 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 4 : ℚ), 0, 1, -1], ![1, (-7 / 4 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-32 / 15 : ℚ), (-1 / 30 : ℚ), (11 / 30 : ℚ), 0], ![(7 / 15 : ℚ), (-16 / 15 : ℚ), (1 / 30 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-70 / 33 : ℚ), (-1 / 22 : ℚ), (25 / 66 : ℚ), 0], ![(31 / 66 : ℚ), (-73 / 66 : ℚ), 0, (1 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-77 / 17 : ℚ), 0, (32 / 17 : ℚ), 0], ![(35 / 17 : ℚ), (-40 / 17 : ℚ), (30 / 17 : ℚ), (3 / 17 : ℚ), (3 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)], ![(1 / 2 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), -1, 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), -2, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 5 : ℚ), 0, 0, (4 / 15 : ℚ)], ![(2 / 5 : ℚ), (-7 / 5 : ℚ), (2 / 5 : ℚ), (-3 / 5 : ℚ), (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-52 / 19 : ℚ), 0, 0, 0], ![(6 / 19 : ℚ), (-29 / 19 : ℚ), (6 / 19 : ℚ), (-10 / 19 : ℚ), (6 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-39 / 16 : ℚ), 0, 0, (-17 / 8 : ℚ)], ![(3 / 16 : ℚ), (-21 / 16 : ℚ), (3 / 16 : ℚ), (-5 / 16 : ℚ), (-65 / 32 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-36 / 7 : ℚ), 0, (-10 / 7 : ℚ), (-2 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-18 / 7 : ℚ), (1 / 7 : ℚ), (-11 / 7 : ℚ), (-1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 9 : ℚ), (-49 / 18 : ℚ), 0, (-5 / 3 : ℚ), (2 / 9 : ℚ)], ![(2 / 9 : ℚ), (-16 / 9 : ℚ), (2 / 9 : ℚ), (-17 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 8 : ℚ), 0, (-1 / 12 : ℚ)], ![(1 / 8 : ℚ), (-9 / 8 : ℚ), 0, (1 / 4 : ℚ), (-1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 31 : ℚ), (-70 / 31 : ℚ), (-3 / 31 : ℚ), (-6 / 31 : ℚ), (-6 / 31 : ℚ)], ![0, (-38 / 31 : ℚ), 0, (6 / 31 : ℚ), (6 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -4, 0, 0, 0], ![(1 / 8 : ℚ), -2, (1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-14 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 5 : ℚ), (3 / 5 : ℚ)], ![(3 / 5 : ℚ), (-8 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-8 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, (-2 / 11 : ℚ), (-6 / 11 : ℚ), (-4 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-13 / 11 : ℚ), (8 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), -1, -1], ![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 6 : ℚ), (-1 / 3 : ℚ), (-5 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 8 : ℚ), (1 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-1 / 8 : ℚ), (-3 / 8 : ℚ), (-9 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 8 : ℚ), (1 / 2 : ℚ), (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), 0, (-6 / 25 : ℚ), (-18 / 25 : ℚ), (-68 / 25 : ℚ)], ![(-6 / 25 : ℚ), (-3 / 25 : ℚ), (-31 / 25 : ℚ), (24 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 25 : ℚ), (-109 / 25 : ℚ), (-34 / 75 : ℚ), (33 / 25 : ℚ), 0], ![(39 / 25 : ℚ), (-56 / 25 : ℚ), (67 / 75 : ℚ), (-6 / 5 : ℚ), (3 / 50 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), -1, -1], ![(-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 20 : ℚ), 0], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (-21 / 20 : ℚ), (1 / 10 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, (-1 / 2 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-1 / 5 : ℚ), (-11 / 5 : ℚ)], ![(-1 / 10 : ℚ), 0, (-11 / 10 : ℚ), (1 / 10 : ℚ), (-11 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-24 / 11 : ℚ), (-1 / 11 : ℚ), (9 / 22 : ℚ), (-1 / 11 : ℚ)], ![(1 / 2 : ℚ), (-25 / 22 : ℚ), 0, (1 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), 0, (-1 / 11 : ℚ), (-2 / 11 : ℚ), (-47 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-1 / 22 : ℚ), (-12 / 11 : ℚ), (1 / 11 : ℚ), (-93 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-10 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-26 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (4 / 5 : ℚ), -5]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0, (-14 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, (-2 / 9 : ℚ), (-2 / 9 : ℚ), (-8 / 3 : ℚ)], ![(-2 / 9 : ℚ), (-1 / 9 : ℚ), (-11 / 9 : ℚ), (-4 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-7 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), (1 / 6 : ℚ), (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-14 / 11 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), -4, -4], ![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 1, -1, -1], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 1, -1, (-5 / 2 : ℚ)], ![-1, 0, 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 9 : ℚ), (-14 / 9 : ℚ), 0, 0, (-34 / 9 : ℚ)], ![0, -1, 0, 0, (-32 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (7 / 36 : ℚ), 0, (-20 / 9 : ℚ)], ![(-1 / 4 : ℚ), 0, (-31 / 72 : ℚ), (-31 / 36 : ℚ), (-10 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-64 / 13 : ℚ), (-7 / 13 : ℚ), 0, 0], ![(2 / 13 : ℚ), (-34 / 13 : ℚ), (-4 / 13 : ℚ), (-24 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), 0, (1 / 4 : ℚ), (1 / 20 : ℚ), (-19 / 5 : ℚ)], ![(-3 / 10 : ℚ), 0, (-4 / 5 : ℚ), 0, (-19 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (4 / 3 : ℚ), (-11 / 3 : ℚ), (-10 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 10 : ℚ), (-12 / 5 : ℚ), (-1 / 10 : ℚ), (-8 / 5 : ℚ), (-8 / 5 : ℚ)], ![0, (-6 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-3 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (4 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (6 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-93 / 22 : ℚ), (81 / 44 : ℚ), (63 / 44 : ℚ), (-1 / 22 : ℚ)], ![(89 / 44 : ℚ), (-95 / 44 : ℚ), (-9 / 11 : ℚ), (1 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -2, 0, 0, -4], ![(1 / 3 : ℚ), -1, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-25 / 6 : ℚ), (13 / 12 : ℚ), (13 / 12 : ℚ), (-1 / 12 : ℚ)], ![(5 / 4 : ℚ), (-25 / 12 : ℚ), (-13 / 12 : ℚ), (13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 3 : ℚ), (-1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 2 : ℚ), (3 / 2 : ℚ), 0, 0], ![(5 / 3 : ℚ), (-7 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-36 / 7 : ℚ), (13 / 7 : ℚ), (-13 / 7 : ℚ), 0], ![(13 / 7 : ℚ), (-20 / 7 : ℚ), (-13 / 7 : ℚ), (-13 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (-3 / 16 : ℚ), (-3 / 16 : ℚ), (-1 / 8 : ℚ)], ![(-1 / 16 : ℚ), 0, (1 / 4 : ℚ), (1 / 16 : ℚ), (-1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-67 / 16 : ℚ), (39 / 32 : ℚ), (-1 / 16 : ℚ), (-1 / 16 : ℚ)], ![(47 / 32 : ℚ), (-67 / 32 : ℚ), (-35 / 32 : ℚ), (-1 / 32 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-12 / 25 : ℚ), (-12 / 25 : ℚ), (-6 / 25 : ℚ), (-6 / 25 : ℚ)], ![0, (-9 / 25 : ℚ), (18 / 25 : ℚ), (6 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), -4, (17 / 16 : ℚ), 0, 0], ![(19 / 16 : ℚ), -2, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 50 : ℚ), (-83 / 20 : ℚ), (229 / 200 : ℚ), (-3 / 100 : ℚ), (-27 / 200 : ℚ)], ![(253 / 200 : ℚ), (-421 / 200 : ℚ), (-217 / 200 : ℚ), 0, (-3 / 40 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-9 / 2 : ℚ)], ![0, (-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-17 / 4 : ℚ), (9 / 8 : ℚ), (9 / 8 : ℚ), (-1 / 8 : ℚ)], ![(5 / 4 : ℚ), (-17 / 8 : ℚ), 0, (9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(2 / 9 : ℚ), (-1 / 3 : ℚ), (2 / 9 : ℚ), (2 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 10 : ℚ), 0, 0, 0], ![(1 / 10 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 4 : ℚ), (59 / 40 : ℚ), 0, (-1 / 20 : ℚ)], ![(63 / 40 : ℚ), (-87 / 40 : ℚ), (1 / 10 : ℚ), (-47 / 40 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 3 : ℚ), (17 / 12 : ℚ), (-17 / 12 : ℚ), 0], ![(17 / 12 : ℚ), (-9 / 4 : ℚ), 0, (-17 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), 0], ![0, (-1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-21 / 5 : ℚ), (7 / 5 : ℚ), 0, 0], ![(3 / 2 : ℚ), (-21 / 10 : ℚ), (1 / 10 : ℚ), 0, (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-3 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), -4, (13 / 10 : ℚ), 0, 0], ![(7 / 5 : ℚ), -2, (1 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-9 / 2 : ℚ), (11 / 6 : ℚ), 0, (-1 / 3 : ℚ)], ![2, (-7 / 3 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, -4], ![(1 / 3 : ℚ), -1, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-11 / 4 : ℚ)], ![(1 / 4 : ℚ), -1, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, 0, 0, -4], ![(-1 / 2 : ℚ), -1, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-4 / 9 : ℚ), 0, (-4 / 9 : ℚ), (-4 / 9 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 3 : ℚ), 0, (-3 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (-5 / 2 : ℚ), (-11 / 6 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, 0, (4 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -5, 0, 0, 0], ![(1 / 4 : ℚ), (-5 / 2 : ℚ), (-7 / 4 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, 0, 0, 0], ![(1 / 4 : ℚ), -2, (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-23 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ)], ![(1 / 10 : ℚ), (-12 / 5 : ℚ), (-7 / 5 : ℚ), (1 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-13 / 3 : ℚ), (-3 / 2 : ℚ), (-1 / 3 : ℚ), 0], ![0, (-13 / 6 : ℚ), (-3 / 2 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 8 : ℚ), (-1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .yy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -4, (-4 / 3 : ℚ), 0, 0], ![(1 / 6 : ℚ), -2, (-4 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (1 / 3 : ℚ), -4, -2, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (1 / 3 : ℚ), 4, 2, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 3 : ℚ), 4, 2, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 3 : ℚ), -4, -2, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-22 / 5 : ℚ), (-12 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-14 / 3 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-28 / 13 : ℚ)], ![(-8 / 13 : ℚ), (-8 / 13 : ℚ), (-60 / 13 : ℚ), (-34 / 13 : ℚ), (-24 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-25 / 6 : ℚ), (-13 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-32 / 7 : ℚ), (-18 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-14 / 3 : ℚ), (-8 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 7 : ℚ), 0, 0, (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (12 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 7 : ℚ), 0], ![(4 / 7 : ℚ), (4 / 7 : ℚ), (-20 / 7 : ℚ), (-20 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 3 : ℚ), (-1 / 3 : ℚ)], ![(1 / 3 : ℚ), (4 / 3 : ℚ), (-5 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 7 : ℚ), 0], ![(4 / 7 : ℚ), (4 / 7 : ℚ), (-20 / 7 : ℚ), (-20 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), 0], ![0, (1 / 3 : ℚ), -4, (-7 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 7 : ℚ), 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 7 : ℚ), 0], ![(4 / 7 : ℚ), (4 / 7 : ℚ), (-20 / 7 : ℚ), (-20 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 7 : ℚ), 0], ![(4 / 7 : ℚ), (4 / 7 : ℚ), (-20 / 7 : ℚ), (-20 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![(-1 / 12 : ℚ), 0, (-1 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -3, (-3 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 5 : ℚ), 0], ![(1 / 10 : ℚ), (1 / 10 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (2 / 5 : ℚ), -2, -2, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, -1], ![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(2 / 3 : ℚ), 0, (-10 / 3 : ℚ), (-8 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-8 / 3 : ℚ), (-2 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, -1], ![(-1 / 2 : ℚ), -2, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(2 / 3 : ℚ), 0, (-10 / 3 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, -1, 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), (-8 / 3 : ℚ), -2, (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(2 / 3 : ℚ), 0, (-10 / 3 : ℚ), (-8 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, -1, 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), (-8 / 3 : ℚ), -2, (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 2]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-11 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-16 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 3 : ℚ)], ![(-4 / 9 : ℚ), (-22 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-32 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-14 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-64 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-30 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-36 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![0, 0, -4, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-21 / 16 : ℚ), 0], ![0, (-7 / 8 : ℚ), -4, (-51 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-14 / 17 : ℚ), (-62 / 17 : ℚ)], ![(-4 / 17 : ℚ), (-25 / 34 : ℚ), (-72 / 17 : ℚ), (-7 / 2 : ℚ), (-29 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), 0, (-44 / 9 : ℚ), (-44 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 14 : ℚ), (-53 / 14 : ℚ)], ![(-1 / 7 : ℚ), (-25 / 14 : ℚ), (-29 / 7 : ℚ), (-33 / 14 : ℚ), (-26 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), (-10 / 3 : ℚ), (-10 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), (-10 / 3 : ℚ), (-10 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (-16 / 7 : ℚ), (-16 / 7 : ℚ), (4 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 7 : ℚ), (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (-16 / 7 : ℚ), (-16 / 7 : ℚ), (4 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-8 / 17 : ℚ), 0, 0], ![(4 / 17 : ℚ), (-20 / 17 : ℚ), (-20 / 17 : ℚ), (18 / 17 : ℚ), (2 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 3 : ℚ), -1], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), -1, -1, (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (-16 / 5 : ℚ), (-16 / 5 : ℚ), 0, (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (-16 / 5 : ℚ), (-16 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-21 / 5 : ℚ), (-3 / 2 : ℚ), (-7 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-32 / 7 : ℚ), -2, (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-14 / 3 : ℚ), (-8 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (2 / 5 : ℚ), -2, (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, (2 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-4 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (5 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(-1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 6 : ℚ), 0], ![0, (1 / 6 : ℚ), -4, (-1 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), 0, (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-8 / 5 : ℚ), -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, (2 / 5 : ℚ), -2], ![(-4 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-3 / 4 : ℚ), 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), -2, (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(2 / 3 : ℚ), 0, (-10 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 2 : ℚ), 0, (-5 / 2 : ℚ), -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), -2, (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, 0], ![(-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -3, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, -2], ![(-2 / 3 : ℚ), (-4 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), (2 / 3 : ℚ)], ![(2 / 3 : ℚ), 0, (-10 / 3 : ℚ), (-4 / 3 : ℚ), (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, -1, 0], ![(1 / 3 : ℚ), (-1 / 3 : ℚ), (-8 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), -4, 0, 0, (9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), -4, 0, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-5 / 3 : ℚ)], ![(-2 / 3 : ℚ), -4, 0, 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![(1 / 2 : ℚ), 0, -4, -2, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-5 / 2 : ℚ)], ![(-1 / 4 : ℚ), -4, 0, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), -4, 0, 0, 7]] },
  { network := { reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-9 / 2 : ℚ)], ![(-1 / 2 : ℚ), -4, 0, 0, (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-11 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-16 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (13 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-11 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-43 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-40 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-18 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-26 / 9 : ℚ), (-8 / 9 : ℚ), 0, (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![0, 0, -4, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (9 / 5 : ℚ), 0, 0, (-9 / 5 : ℚ)], ![(-9 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-20 / 31 : ℚ), (-118 / 31 : ℚ)], ![(-4 / 31 : ℚ), (-53 / 62 : ℚ), (-128 / 31 : ℚ), (-79 / 62 : ℚ), (-57 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-14 / 3 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-14 / 3 : ℚ)], ![(-13 / 18 : ℚ), (-31 / 18 : ℚ), (-29 / 9 : ℚ), 0, (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (-16 / 7 : ℚ), (-10 / 7 : ℚ), (6 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-8 / 7 : ℚ), 0, 0], ![(4 / 7 : ℚ), (-20 / 7 : ℚ), (-12 / 7 : ℚ), (4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), (-10 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), -1, (-3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), -2, (-6 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), 2]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), (16 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, -2, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (-16 / 5 : ℚ), -2, 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-28 / 5 : ℚ), -1, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-32 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-44 / 9 : ℚ), 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (1 / 2 : ℚ), 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 2, -2, 0, 2], ![2, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 0, -4, 1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 0, -4, -1]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 2, 0, -5], ![-2, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), (-1 / 8 : ℚ), 0, 0], ![(1 / 8 : ℚ), 0, 0, (-17 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (1 / 2 : ℚ), -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (1 / 2 : ℚ), -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (1 / 3 : ℚ), -4, (-1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 3 : ℚ)], ![0, (1 / 3 : ℚ), -4, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 6 : ℚ)], ![0, (1 / 6 : ℚ), -4, (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .zero), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, (1 / 2 : ℚ), -4, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, (1 / 2 : ℚ), 4, 0]] }
]

theorem conicDetC12_checked : conicDetC12.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
