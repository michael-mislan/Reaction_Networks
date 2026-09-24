import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC18 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, -1, 1, -1], ![-1, 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 12 : ℚ), 0, 0, 0, (1 / 12 : ℚ)], ![(-1 / 12 : ℚ), -1, 0, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 0, 0], ![(-1 / 6 : ℚ), -1, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), -1, 0, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, -1, 1, (-5 / 2 : ℚ)], ![(-7 / 6 : ℚ), 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 0, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), -1, 0, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), 0, (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), 0, (1 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (5 / 12 : ℚ), 0, (1 / 12 : ℚ), 0], ![0, (-7 / 12 : ℚ), 0, (-1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), 0, -1], ![(-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (1 / 7 : ℚ), (-5 / 7 : ℚ), 0, (-6 / 7 : ℚ)], ![(-2 / 7 : ℚ), 0, 0, 0, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-3 / 20 : ℚ)], ![0, (-2 / 5 : ℚ), 0, 0, (-1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 8 : ℚ), (-3 / 4 : ℚ), (-5 / 8 : ℚ), (-7 / 16 : ℚ)], ![(-3 / 8 : ℚ), 0, 0, (1 / 8 : ℚ), (-5 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![0, (-2 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (5 / 12 : ℚ), 0, 0, 0], ![0, (-7 / 12 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), (-7 / 12 : ℚ), (-5 / 6 : ℚ), (-19 / 18 : ℚ)], ![(-1 / 2 : ℚ), 0, (-5 / 12 : ℚ), (1 / 6 : ℚ), (-4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 8 : ℚ), (-3 / 4 : ℚ), (-5 / 8 : ℚ), -1], ![(-3 / 8 : ℚ), 0, 0, (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 24 : ℚ)], ![0, (-1 / 2 : ℚ), 0, (1 / 6 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![0, (-2 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 7 : ℚ), 0, 0, 0], ![(-1 / 14 : ℚ), (-6 / 7 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 41 : ℚ), (4 / 41 : ℚ), 0, 0, 0], ![(21 / 41 : ℚ), (-33 / 41 : ℚ), (4 / 41 : ℚ), (42 / 41 : ℚ), (2 / 41 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 4 : ℚ), (-1 / 3 : ℚ), (-7 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 12 : ℚ), 0, (11 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 44 : ℚ), (2 / 11 : ℚ), (-5 / 44 : ℚ), (-5 / 44 : ℚ), 0], ![(-1 / 44 : ℚ), (-23 / 44 : ℚ), (3 / 44 : ℚ), (3 / 44 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (1 / 9 : ℚ), 0, (1 / 9 : ℚ), 0], ![(-1 / 18 : ℚ), (-8 / 9 : ℚ), 0, (-5 / 18 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), (2 / 11 : ℚ), 0, (2 / 11 : ℚ), 0], ![(1 / 11 : ℚ), (-7 / 11 : ℚ), (2 / 11 : ℚ), (-7 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (-3 / 11 : ℚ), (2 / 11 : ℚ), (-8 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-1 / 11 : ℚ), (-4 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (-3 / 11 : ℚ), (2 / 11 : ℚ), (-7 / 22 : ℚ)], ![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-1 / 11 : ℚ), (-4 / 11 : ℚ), (-5 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 7 : ℚ), 0, 0, (-4 / 21 : ℚ)], ![(-1 / 14 : ℚ), (-6 / 7 : ℚ), 0, 0, (-1 / 42 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (11 / 28 : ℚ), 0, 0, (-3 / 7 : ℚ)], ![(-1 / 14 : ℚ), (-17 / 28 : ℚ), 0, 0, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (11 / 28 : ℚ), 0, 0, (-1 / 14 : ℚ)], ![(-1 / 14 : ℚ), (-17 / 28 : ℚ), 0, 0, (-1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 37 : ℚ), (6 / 37 : ℚ), (-6 / 37 : ℚ), (-10 / 37 : ℚ), 0], ![(1 / 37 : ℚ), (-19 / 37 : ℚ), 0, (6 / 37 : ℚ), (3 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 20 : ℚ), (-2 / 5 : ℚ), (-7 / 20 : ℚ), (-21 / 80 : ℚ)], ![(-3 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 4 : ℚ), (-1 / 10 : ℚ), (-3 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 8 : ℚ), (-3 / 4 : ℚ), -1, (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, 0, (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 24 : ℚ)], ![0, (-1 / 2 : ℚ), 0, (1 / 6 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (-3 / 11 : ℚ), (-7 / 22 : ℚ), (-3 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-1 / 11 : ℚ), (-5 / 22 : ℚ), (-1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), 0, 0, 0, 0], ![(2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![(-1 / 16 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![(-5 / 16 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 1], ![0, -1, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, -1, 1, -1], ![-1, 0, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 12 : ℚ), 0, 0, 0, (1 / 12 : ℚ)], ![(-1 / 12 : ℚ), -1, 0, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, 0, 0], ![(-1 / 4 : ℚ), -1, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), -1, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, -1, 1, (-19 / 8 : ℚ)], ![(-9 / 8 : ℚ), 0, -2, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, 0, (-3 / 8 : ℚ)], ![(-1 / 4 : ℚ), -1, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 17 : ℚ), (-2 / 17 : ℚ), (-6 / 17 : ℚ), (-6 / 17 : ℚ)], ![0, (-6 / 17 : ℚ), (-1 / 17 : ℚ), (6 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 17 : ℚ), (3 / 17 : ℚ), 0, (-1 / 17 : ℚ), (-1 / 17 : ℚ)], ![(2 / 17 : ℚ), (-8 / 17 : ℚ), (3 / 17 : ℚ), (1 / 17 : ℚ), (2 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(6 / 17 : ℚ), (3 / 17 : ℚ), (-8 / 17 : ℚ), 0, (3 / 17 : ℚ)], ![(-6 / 17 : ℚ), 0, (-13 / 17 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(6 / 17 : ℚ), (3 / 17 : ℚ), (-8 / 17 : ℚ), 0, (-15 / 17 : ℚ)], ![(-6 / 17 : ℚ), 0, (-13 / 17 : ℚ), 0, (-6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), 0, 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 136 : ℚ), (3 / 17 : ℚ), (-7 / 136 : ℚ), 0, 0], ![(9 / 136 : ℚ), (-57 / 136 : ℚ), (5 / 68 : ℚ), 0, (3 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (2 / 13 : ℚ), (-1 / 13 : ℚ), (-4 / 13 : ℚ), (-2 / 13 : ℚ)], ![0, (-6 / 13 : ℚ), 0, (2 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 17 : ℚ), (-2 / 17 : ℚ), 0, 0], ![0, (-6 / 17 : ℚ), (-1 / 17 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (1 / 8 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (2 / 13 : ℚ), (-1 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ)], ![0, (-6 / 13 : ℚ), 0, (2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-7 / 24 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 17 : ℚ), (-2 / 17 : ℚ), 0, 0], ![0, (-6 / 17 : ℚ), (-1 / 17 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 49 : ℚ), (4 / 49 : ℚ), 0, 0, 0], ![(25 / 49 : ℚ), (-37 / 49 : ℚ), (4 / 49 : ℚ), (50 / 49 : ℚ), (2 / 49 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 8 : ℚ), (1 / 12 : ℚ), (19 / 24 : ℚ), (17 / 24 : ℚ), 0], ![(31 / 24 : ℚ), (-37 / 24 : ℚ), (5 / 3 : ℚ), (19 / 24 : ℚ), (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 53 : ℚ), (8 / 53 : ℚ), (-4 / 53 : ℚ), (-3 / 53 : ℚ), (4 / 53 : ℚ)], ![(1 / 53 : ℚ), (-25 / 53 : ℚ), 0, (5 / 53 : ℚ), (8 / 53 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-7 / 18 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (1 / 7 : ℚ), 0, (1 / 7 : ℚ), 0], ![(1 / 7 : ℚ), (-4 / 7 : ℚ), (1 / 7 : ℚ), (-4 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), 0, (1 / 6 : ℚ), 0], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 11 : ℚ), (1 / 11 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ), (-9 / 11 : ℚ)], ![(-3 / 11 : ℚ), 0, 0, (1 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 27 : ℚ), (-7 / 27 : ℚ), (-28 / 81 : ℚ), (-7 / 27 : ℚ)], ![(-4 / 27 : ℚ), (-8 / 27 : ℚ), (-19 / 54 : ℚ), (-8 / 81 : ℚ), (-5 / 27 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (2 / 17 : ℚ), (-1 / 17 : ℚ), 0, 0], ![(4 / 17 : ℚ), (-10 / 17 : ℚ), 0, (2 / 17 : ℚ), (2 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (1 / 24 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 24 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-5 / 24 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 1], ![0, (-3 / 2 : ℚ), 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, 0, 0], ![0, -1, (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, 0, (2 / 15 : ℚ), 0], ![(1 / 30 : ℚ), (-14 / 15 : ℚ), (-1 / 5 : ℚ), (-7 / 30 : ℚ), (1 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), 0, 0, 0, (-14 / 13 : ℚ)], ![0, (-17 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![(1 / 2 : ℚ), (-3 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 0, 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 2 : ℚ), 0], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, 0, 0, 0], ![(-1 / 3 : ℚ), -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 7 : ℚ), 0, 0, 0, 0], ![(3 / 7 : ℚ), (-5 / 7 : ℚ), (1 / 7 : ℚ), 0, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), 0, 0, (-3 / 10 : ℚ), 0], ![(1 / 10 : ℚ), (-1 / 2 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), 0, 0, 0, 0], ![(2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), 0, 0, 0, 0], ![(2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 20 : ℚ), 0, 0, (-3 / 20 : ℚ), 0], ![(1 / 20 : ℚ), (-1 / 4 : ℚ), (1 / 20 : ℚ), (1 / 10 : ℚ), (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 0, 0], ![(-1 / 3 : ℚ), -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 25 : ℚ), 0, 0, 0, 0], ![(13 / 25 : ℚ), (-21 / 25 : ℚ), (2 / 25 : ℚ), (26 / 25 : ℚ), (2 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 16 : ℚ), 0, 0, (11 / 16 : ℚ), 0], ![(21 / 16 : ℚ), (-25 / 16 : ℚ), (1 / 16 : ℚ), (13 / 16 : ℚ), (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 7 : ℚ), 0, 0, 0, 0], ![(1 / 7 : ℚ), (-5 / 7 : ℚ), (1 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 7 : ℚ), -1, -1, (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 4 : ℚ), -1, -1, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 2 : ℚ), -1, -1, 0, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, (-1 / 4 : ℚ)], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![0, (-5 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, 0, (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), (-1 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), 0, 0, 0, 0], ![(4 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ), (4 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![0, (-3 / 2 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 17 : ℚ), 0, (23 / 17 : ℚ), (-21 / 17 : ℚ)], ![0, (-20 / 17 : ℚ), (-3 / 17 : ℚ), (-23 / 17 : ℚ), (-9 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (-1 / 3 : ℚ), (5 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 17 : ℚ), 0, (25 / 17 : ℚ), (-14 / 17 : ℚ)], ![0, (-21 / 17 : ℚ), (-4 / 17 : ℚ), (-25 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (1 / 16 : ℚ), 1, -1, (-7 / 8 : ℚ)], ![-1, 0, 0, 0, (-5 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), 1, -1, (-5 / 2 : ℚ)], ![-1, 0, 0, 0, (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), 1, -1, (-7 / 3 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), 1, -1, (-9 / 4 : ℚ)], ![-1, 0, 0, 0, (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (1 / 9 : ℚ), (2 / 9 : ℚ), 0, 0], ![(-1 / 18 : ℚ), (-8 / 9 : ℚ), (-7 / 9 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 21 : ℚ), (1 / 21 : ℚ), (22 / 21 : ℚ), (-19 / 21 : ℚ), (-82 / 21 : ℚ)], ![(-61 / 84 : ℚ), 0, (-31 / 84 : ℚ), (-13 / 28 : ℚ), (-11 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, -4], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 15 : ℚ), (1 / 30 : ℚ), (31 / 30 : ℚ), (-14 / 15 : ℚ), (-227 / 60 : ℚ)], ![(-7 / 30 : ℚ), 0, (-5 / 6 : ℚ), (-9 / 10 : ℚ), (-113 / 30 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), 0, (2 / 11 : ℚ), (-14 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-13 / 11 : ℚ), (-2 / 11 : ℚ), (-13 / 11 : ℚ), (-6 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 17 : ℚ), (4 / 17 : ℚ), 0, (4 / 17 : ℚ), (-14 / 17 : ℚ)], ![0, (-21 / 17 : ℚ), (-4 / 17 : ℚ), (-21 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-22 / 15 : ℚ)], ![(-1 / 15 : ℚ), (-16 / 15 : ℚ), (-19 / 60 : ℚ), (-3 / 4 : ℚ), (-7 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 1, (-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), (1 / 4 : ℚ), 0, -2], ![(-1 / 8 : ℚ), (-7 / 8 : ℚ), (-3 / 4 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 7 : ℚ), (2 / 7 : ℚ), (9 / 7 : ℚ), (-24 / 7 : ℚ), (-24 / 7 : ℚ)], ![(-11 / 7 : ℚ), 0, 0, 0, (-11 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (1 / 11 : ℚ), 0, (-7 / 11 : ℚ), (-7 / 22 : ℚ)], ![0, (-12 / 11 : ℚ), (-1 / 11 : ℚ), (-3 / 11 : ℚ), (-3 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 4 : ℚ), (5 / 4 : ℚ), (-13 / 4 : ℚ), (-7 / 4 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 13 : ℚ), (4 / 13 : ℚ), (17 / 13 : ℚ), (-46 / 13 : ℚ), (-40 / 13 : ℚ)], ![(-21 / 13 : ℚ), 0, 0, 0, (-38 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), (1 / 24 : ℚ), (25 / 24 : ℚ), (-31 / 8 : ℚ), (-23 / 12 : ℚ)], ![(-7 / 24 : ℚ), 0, (-19 / 24 : ℚ), (-89 / 24 : ℚ), (-15 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (1 / 10 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 36 : ℚ), (1 / 18 : ℚ), 0, 0, (-1 / 18 : ℚ)], ![(19 / 36 : ℚ), (-23 / 36 : ℚ), 0, 1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 4 : ℚ), (1 / 20 : ℚ), (-3 / 20 : ℚ), (-1 / 20 : ℚ), (-13 / 10 : ℚ)], ![(3 / 4 : ℚ), (-17 / 20 : ℚ), (3 / 20 : ℚ), 0, (11 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 7 : ℚ), (8 / 7 : ℚ), (4 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (4 / 7 : ℚ), (12 / 7 : ℚ), (4 / 7 : ℚ), 0], ![(4 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 31 : ℚ), (32 / 31 : ℚ), (16 / 31 : ℚ), (-12 / 31 : ℚ)], ![0, (-32 / 31 : ℚ), (-32 / 31 : ℚ), (-32 / 31 : ℚ), (-4 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (4 / 11 : ℚ), (6 / 11 : ℚ), 0, 0], ![(2 / 11 : ℚ), -1, (-6 / 11 : ℚ), (-8 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 16 : ℚ), 0, (-1 / 8 : ℚ)], ![0, (-9 / 16 : ℚ), (-1 / 16 : ℚ), (-1 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (11 / 18 : ℚ), (4 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, (-19 / 18 : ℚ), (-4 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 7 : ℚ), (4 / 7 : ℚ), 0, (-24 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-8 / 7 : ℚ), 0, 0, (4 / 7 : ℚ), (-8 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), -1, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 5 : ℚ), (2 / 5 : ℚ), 0, (-12 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![(1 / 3 : ℚ), -1, 0, (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-7 / 20 : ℚ)], ![(1 / 20 : ℚ), (-17 / 20 : ℚ), 0, 0, (1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), (1 / 10 : ℚ), 0, 0, (-1 / 10 : ℚ)], ![(1 / 2 : ℚ), (-4 / 5 : ℚ), (1 / 10 : ℚ), 1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-13 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), 0, 2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 0, (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![0, (-3 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![0, (-5 / 8 : ℚ), 0, 0, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), (-1 / 16 : ℚ), 0], ![(1 / 16 : ℚ), (-13 / 16 : ℚ), 0, (-1 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 36 : ℚ), (-1 / 24 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 36 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), (-5 / 6 : ℚ), (-4 / 3 : ℚ), (-5 / 6 : ℚ)], ![(-1 / 2 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 24 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), (1 / 24 : ℚ), (-5 / 24 : ℚ), (-11 / 24 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (1 / 24 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (1 / 8 : ℚ), 0, (9 / 8 : ℚ), -1], ![(9 / 8 : ℚ), (-11 / 8 : ℚ), (-9 / 8 : ℚ), (9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 0, (-9 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, 2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 7 : ℚ), 0, 0, (-31 / 28 : ℚ)], ![(-1 / 14 : ℚ), (-6 / 7 : ℚ), 0, 0, (25 / 28 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (11 / 28 : ℚ), 0, 0, (-15 / 7 : ℚ)], ![(-1 / 14 : ℚ), (-17 / 28 : ℚ), 0, 0, (13 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 7 : ℚ), 0, 0, (-1 / 14 : ℚ)], ![(-1 / 14 : ℚ), (-6 / 7 : ℚ), 0, 0, (-1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 24 : ℚ), (1 / 24 : ℚ), (-1 / 24 : ℚ), (-49 / 24 : ℚ), (-5 / 8 : ℚ)], ![0, (-7 / 8 : ℚ), 0, 2, (11 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (-3 / 11 : ℚ), (-29 / 22 : ℚ), (-7 / 22 : ℚ)], ![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-1 / 11 : ℚ), (17 / 22 : ℚ), (-5 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 11 : ℚ), (1 / 11 : ℚ), (-1 / 11 : ℚ), (-18 / 11 : ℚ), (-13 / 11 : ℚ)], ![(5 / 11 : ℚ), (-8 / 11 : ℚ), 0, (27 / 11 : ℚ), (10 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (-13 / 6 : ℚ), (1 / 24 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 2, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (2 / 11 : ℚ), (-2 / 11 : ℚ), (-3 / 22 : ℚ), (-2 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-5 / 11 : ℚ), 0, (-1 / 22 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 76 : ℚ), (3 / 38 : ℚ), (3 / 38 : ℚ), 0, 0], ![(1 / 76 : ℚ), -1, (-1 / 4 : ℚ), (-7 / 38 : ℚ), (3 / 76 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(-2 / 5 : ℚ), -1, (-4 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), (4 / 9 : ℚ), 0, (-2 / 3 : ℚ)], ![(-4 / 9 : ℚ), -1, (-8 / 9 : ℚ), 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (-4 / 3 : ℚ), -2], ![(-1 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (1 / 3 : ℚ), (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 35 : ℚ), (16 / 35 : ℚ), (-16 / 15 : ℚ), (-4 / 5 : ℚ)], ![(-16 / 35 : ℚ), (-32 / 35 : ℚ), (-32 / 35 : ℚ), (-32 / 105 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), (4 / 9 : ℚ), (-16 / 9 : ℚ), (-7 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ), (-5 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 11 : ℚ), (4 / 11 : ℚ), (-7 / 11 : ℚ), (-6 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ), (-5 / 11 : ℚ), (-2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 19 : ℚ), (11 / 38 : ℚ), 0, 0, 0], ![(4 / 19 : ℚ), (-35 / 38 : ℚ), (-16 / 19 : ℚ), (4 / 19 : ℚ), (2 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, (-28 / 27 : ℚ), (-2 / 3 : ℚ)], ![(-4 / 9 : ℚ), -1, 0, (-8 / 27 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 4 : ℚ), (9 / 8 : ℚ), 0, -3, (-13 / 8 : ℚ)], ![(-11 / 8 : ℚ), 0, (-1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 28 : ℚ), (1 / 2 : ℚ), (-9 / 28 : ℚ), (-15 / 14 : ℚ), 0], ![(-3 / 28 : ℚ), (-5 / 4 : ℚ), (-9 / 28 : ℚ), (3 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 3 : ℚ), -1, 0, (-1 / 2 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, 0], ![0, (-5 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), 0, 0, (-5 / 3 : ℚ), 0], ![(-1 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ), (-28 / 9 : ℚ), (-4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, -1, 0, 0, 0], ![1, -1, 1, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), -1, 0, 0, 0], ![(1 / 6 : ℚ), -1, 1, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, 0], ![0, (-5 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -5], ![(-3 / 2 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 5 : ℚ), -2, 0, 0, 0], ![(1 / 5 : ℚ), -2, 2, (-26 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 3 : ℚ), (-10 / 3 : ℚ), 0, 0, 0], ![0, (-10 / 3 : ℚ), (22 / 9 : ℚ), (-68 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-8 / 5 : ℚ), 0], ![(-2 / 5 : ℚ), 0, (-3 / 5 : ℚ), (-8 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, -1, 0, (-8 / 5 : ℚ), 0], ![1, -1, 1, (-19 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), -1, 0, (-7 / 6 : ℚ), 0], ![(1 / 6 : ℚ), -1, 1, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-3 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -5], ![(-3 / 2 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 5 : ℚ), -2, 0, (-14 / 5 : ℚ), 0], ![(2 / 5 : ℚ), -2, 2, (-32 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), (3 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), -7], ![(-5 / 4 : ℚ), (3 / 4 : ℚ), (-7 / 4 : ℚ), 0, -7]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), -1], ![0, 0, 0, (-1 / 2 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, 0, (-7 / 6 : ℚ)], ![-1, (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -5], ![(-3 / 2 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 5 : ℚ), 0, 0, (-24 / 5 : ℚ)], ![(-11 / 5 : ℚ), (2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, (2 / 3 : ℚ)], ![(5 / 3 : ℚ), (-5 / 3 : ℚ), (5 / 3 : ℚ), 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-7 / 6 : ℚ), 0, 0, (1 / 6 : ℚ)], ![(1 / 3 : ℚ), (-7 / 6 : ℚ), (7 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-3 / 2 : ℚ), 0, 0, 0], ![0, (-3 / 2 : ℚ), 1, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, -2, (-9 / 2 : ℚ)], ![(-13 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), -2, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), -2, 0, (1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), -2, 2, (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)], ![(3 / 2 : ℚ), (-3 / 2 : ℚ), (3 / 2 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-4 / 3 : ℚ), -1], ![(-1 / 3 : ℚ), 0, 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 16 : ℚ), 0, 0, (-19 / 16 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 16 : ℚ), (-3 / 16 : ℚ), (-37 / 16 : ℚ), (3 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), 0, 0, (-8 / 5 : ℚ), -4], ![(-3 / 5 : ℚ), 0, 0, (-29 / 10 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, 0, (-9 / 7 : ℚ), -4], ![(-2 / 7 : ℚ), 0, 0, (-17 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, -1, 0, (-1 / 4 : ℚ), 0], ![1, -1, 1, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), -1, 0, (-1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), -1, 1, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), 0, (-1 / 8 : ℚ), (-17 / 4 : ℚ)], ![(-3 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), (-11 / 8 : ℚ), (-17 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 10 : ℚ), -2, 0, (-1 / 10 : ℚ), 0], ![(1 / 20 : ℚ), -2, 2, (4 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![1, 1, 0, (-1 / 4 : ℚ), 0], ![-1, 1, -1, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 1, -1], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, 0, (3 / 8 : ℚ), -4], ![(-1 / 4 : ℚ), 0, 0, (-3 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, 1, -4], ![(-7 / 6 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, -1, 0, 0, -2], ![1, -1, 1, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![0, 0, 0, 1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -5], ![0, 0, 0, 1, -5]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, -1, -4], ![(-1 / 3 : ℚ), 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, -1, -4], ![(-1 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-25 / 12 : ℚ), 0, (13 / 12 : ℚ), 0], ![(5 / 4 : ℚ), (-25 / 12 : ℚ), (25 / 12 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, 0, 0, 0], ![(1 / 2 : ℚ), -2, 2, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, (-5 / 2 : ℚ), 0, 0, 0], ![0, (-5 / 2 : ℚ), 2, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), 0, (1 / 2 : ℚ), (-17 / 4 : ℚ)], ![-1, (1 / 8 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), (-17 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), (-1 / 5 : ℚ), 0, (2 / 5 : ℚ), (-18 / 5 : ℚ)], ![(-8 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-7 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, 0], ![0, (4 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, -1, 0, 0], ![1, 1, 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-124 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 3 : ℚ), 0, (-10 / 3 : ℚ), 0, 0], ![(4 / 9 : ℚ), (22 / 9 : ℚ), 0, (-68 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-32 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 20 : ℚ), (1 / 4 : ℚ), (-73 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (-11 / 10 : ℚ), (-3 / 4 : ℚ), (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), -1], ![0, 0, 0, (-9 / 5 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), (-6 / 5 : ℚ)], ![0, 0, 0, (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 19 : ℚ), (-1 / 19 : ℚ), (-14 / 57 : ℚ), 0, (-22 / 19 : ℚ)], ![0, (-3 / 19 : ℚ), (-1 / 19 : ℚ), (-28 / 57 : ℚ), (-49 / 57 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 25 : ℚ), (-24 / 25 : ℚ), 0, (-118 / 25 : ℚ)], ![(-3 / 25 : ℚ), (-9 / 25 : ℚ), (-3 / 25 : ℚ), (-48 / 25 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 17 : ℚ), (20 / 17 : ℚ), (4 / 17 : ℚ), (-132 / 17 : ℚ)], ![(-28 / 17 : ℚ), (-28 / 17 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 11 : ℚ), (-4 / 11 : ℚ), (-29 / 11 : ℚ), (-37 / 11 : ℚ), 0], ![(21 / 11 : ℚ), (25 / 11 : ℚ), (-4 / 11 : ℚ), (-78 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), -1], ![0, 0, 0, (-1 / 2 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (-27 / 4 : ℚ)], ![-1, (-3 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-13 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, (-9 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 0, 1], ![0, -2, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .y), (.y, .xy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-5 / 4 : ℚ), (-1 / 8 : ℚ), (-3 / 8 : ℚ), (3 / 8 : ℚ)], ![(3 / 8 : ℚ), (-11 / 8 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0, (1 / 4 : ℚ)], ![(5 / 4 : ℚ), (5 / 4 : ℚ), 0, (1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xx), (.x, .xy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, (-13 / 10 : ℚ), 0, 0], ![0, 1, (-1 / 5 : ℚ), (1 / 5 : ℚ), -1]] }
]

theorem conicDetC18_checked : conicDetC18.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
