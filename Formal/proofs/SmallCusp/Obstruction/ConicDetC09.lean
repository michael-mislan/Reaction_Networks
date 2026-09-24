import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC09 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), 0, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0, (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), 0, (-1 / 22 : ℚ), 0, (-24 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-1 / 22 : ℚ), (-12 / 11 : ℚ), (-1 / 22 : ℚ), (-7 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, (-2 / 9 : ℚ), 0, (-28 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (-13 / 9 : ℚ), (-2 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), 0, (-1 / 22 : ℚ), (-49 / 22 : ℚ), (-24 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-1 / 22 : ℚ), (-12 / 11 : ℚ), (1 / 22 : ℚ), (-7 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), 0, (-1 / 14 : ℚ), (-16 / 7 : ℚ), (-31 / 14 : ℚ)], ![(-1 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-5 / 14 : ℚ), (-31 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-3 / 2 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-2 / 7 : ℚ), (-24 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-4 / 7 : ℚ), 0, (-11 / 7 : ℚ), (2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), 0, 1, -1, (-1 / 3 : ℚ)], ![-1, 0, 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 4 : ℚ), 1, -1, (-11 / 4 : ℚ)], ![-1, 0, 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0, (-1 / 6 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 1, -1, (-9 / 4 : ℚ)], ![-1, 0, 0, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, (5 / 6 : ℚ), 0, (-10 / 3 : ℚ)], ![-1, 0, (-1 / 6 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, 1, 0, -4], ![(-7 / 6 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 14 : ℚ), 0, 0, (-25 / 14 : ℚ)], ![(-1 / 14 : ℚ), (-19 / 28 : ℚ), (-11 / 28 : ℚ), (-15 / 14 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), 0, (-9 / 4 : ℚ)], ![(-1 / 3 : ℚ), 0, (-5 / 6 : ℚ), (-5 / 6 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), (1 / 6 : ℚ), 1, (1 / 6 : ℚ), (-19 / 6 : ℚ)], ![(-8 / 3 : ℚ), 0, (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 3 : ℚ), (4 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (1 / 5 : ℚ), (6 / 5 : ℚ), -3, -3], ![(-7 / 5 : ℚ), 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-23 / 20 : ℚ), (-3 / 20 : ℚ), (-2 / 5 : ℚ), 0], ![(1 / 20 : ℚ), (-23 / 20 : ℚ), (-1 / 10 : ℚ), (-3 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (7 / 6 : ℚ), (-17 / 6 : ℚ), (-5 / 2 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 4 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-3 / 8 : ℚ), 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (1 / 2 : ℚ), 0, (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-3 / 8 : ℚ), 0, (-3 / 8 : ℚ)], ![(-1 / 8 : ℚ), 0, (1 / 2 : ℚ), 0, (29 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (1 / 10 : ℚ)], ![0, (-1 / 5 : ℚ), (3 / 10 : ℚ), 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 16 : ℚ), (-1 / 16 : ℚ), 0, 0], ![(1 / 16 : ℚ), (-5 / 16 : ℚ), (3 / 16 : ℚ), (3 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 16 : ℚ), (-1 / 16 : ℚ), 0, 0], ![(1 / 16 : ℚ), (-5 / 16 : ℚ), (3 / 16 : ℚ), (3 / 16 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-3 / 8 : ℚ)], ![(-1 / 8 : ℚ), 0, (3 / 8 : ℚ), (3 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ), (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-10 / 11 : ℚ), (2 / 11 : ℚ), 0, (-2 / 11 : ℚ)], ![(6 / 11 : ℚ), (-12 / 11 : ℚ), 0, (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (3 / 5 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-6 / 11 : ℚ), (6 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0, 0], ![(2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0, 0], ![(2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-1 / 4 : ℚ), 0, -2], ![(-1 / 8 : ℚ), 0, (1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), 0, (-15 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), 0, (1 / 10 : ℚ)], ![0, (-1 / 5 : ℚ), (1 / 10 : ℚ), 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (1 / 4 : ℚ), (3 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-3 / 10 : ℚ), (-2 / 5 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), 0, (1 / 10 : ℚ), 0, (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-3 / 10 : ℚ), (-1 / 2 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), 0, (1 / 10 : ℚ), (1 / 10 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), 0], ![0, (-1 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, 0, (1 / 2 : ℚ), 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, 0, (1 / 2 : ℚ), 0, (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, (-3 / 4 : ℚ), -2], ![(-1 / 4 : ℚ), 0, 0, (13 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-23 / 6 : ℚ), (-11 / 6 : ℚ)], ![(-1 / 6 : ℚ), 0, 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (5 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 7 : ℚ), 0, (-6 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (-10 / 7 : ℚ), (-10 / 7 : ℚ), (-10 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), -1, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), 0, (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-6 / 7 : ℚ), (-6 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-6 / 7 : ℚ), (-6 / 7 : ℚ), 0, (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ), (-4 / 7 : ℚ), 0], ![0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), 0], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-16 / 9 : ℚ), 0], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-1 / 9 : ℚ), (-14 / 9 : ℚ), (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 10 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-1 / 9 : ℚ), (-2 / 9 : ℚ), (-14 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-36 / 5 : ℚ)], ![(-8 / 15 : ℚ), (-8 / 15 : ℚ), 0, (-8 / 15 : ℚ), (-18 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![0, 0, (-4 / 3 : ℚ), -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-32 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 14 : ℚ), (1 / 14 : ℚ), (-9 / 7 : ℚ), (5 / 7 : ℚ)], ![(-9 / 7 : ℚ), (-1 / 14 : ℚ), 0, (-17 / 14 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (1 / 8 : ℚ), 0, (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-1 / 8 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 14 : ℚ), (1 / 14 : ℚ), (5 / 7 : ℚ), (-9 / 7 : ℚ)], ![(-9 / 7 : ℚ), (-1 / 14 : ℚ), 0, (1 / 7 : ℚ), (-17 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-16 / 5 : ℚ), (-28 / 5 : ℚ), (-6 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (-14 / 5 : ℚ), (-32 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ), (-2 / 3 : ℚ), (-10 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 12 : ℚ), (1 / 3 : ℚ), (5 / 4 : ℚ), (-16 / 3 : ℚ)], ![(-17 / 6 : ℚ), (-1 / 3 : ℚ), 0, (1 / 6 : ℚ), (-31 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 4 : ℚ), 0, (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (1 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 8 : ℚ), 0, 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-23 / 10 : ℚ), (-22 / 5 : ℚ), (-7 / 10 : ℚ), 0], ![0, (-1 / 10 : ℚ), (-11 / 5 : ℚ), (-23 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, 0, (-4 / 3 : ℚ), -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-2 / 5 : ℚ), 0, (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), 0], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-2 / 5 : ℚ), 0, (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 37 : ℚ), (14 / 37 : ℚ), (6 / 37 : ℚ), (-77 / 37 : ℚ), (-33 / 37 : ℚ)], ![(-21 / 37 : ℚ), (-6 / 37 : ℚ), 0, (-63 / 37 : ℚ), (39 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), (-8 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), -2, (-15 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 15 : ℚ), (-1 / 15 : ℚ), (1 / 15 : ℚ), (-10 / 9 : ℚ), (-7 / 30 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 15 : ℚ), 0, (-97 / 45 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-7 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (-11 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 21 : ℚ), (-10 / 7 : ℚ), 0], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-1 / 21 : ℚ), (-18 / 7 : ℚ), (5 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ), (-17 / 9 : ℚ), (-32 / 9 : ℚ)], ![(-8 / 9 : ℚ), 0, 0, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-7 / 6 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-9 / 8 : ℚ), (-9 / 4 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ)], ![(1 / 2 : ℚ), 0, (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-8 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, 0], ![0, 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (-29 / 6 : ℚ), (3 / 2 : ℚ), 0], ![(5 / 3 : ℚ), (-1 / 12 : ℚ), (-29 / 12 : ℚ), (-17 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-4 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), 0], ![(3 / 5 : ℚ), 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 30 : ℚ), (-8 / 15 : ℚ), (1 / 30 : ℚ), (-7 / 60 : ℚ), (-62 / 15 : ℚ)], ![(-1 / 20 : ℚ), (-17 / 60 : ℚ), 0, (3 / 20 : ℚ), (-247 / 60 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-33 / 16 : ℚ), (-17 / 4 : ℚ), (19 / 16 : ℚ), 0], ![(5 / 4 : ℚ), 0, (-17 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), -5], ![(-1 / 2 : ℚ), 0, 0, 0, (-39 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 9 : ℚ), 0, (-16 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-2 / 9 : ℚ), (2 / 9 : ℚ), (7 / 9 : ℚ), (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), (2 / 3 : ℚ), 0, (-10 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-2 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-23 / 10 : ℚ), (-22 / 5 : ℚ), (-7 / 10 : ℚ), 0], ![0, (-1 / 10 : ℚ), (-11 / 5 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-8 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-10 / 7 : ℚ), 0, 0], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-18 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, -2, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-80 / 13 : ℚ)], ![(-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ), (-76 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![0, 0, 0, -2, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -3, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, 0, -2, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -7], ![(-3 / 7 : ℚ), (-3 / 7 : ℚ), (-3 / 7 : ℚ), (-3 / 7 : ℚ), (-23 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), -2], ![(-3 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -6], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-40 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (-5 / 4 : ℚ), 0, (1 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 6 : ℚ), 0, (-5 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), (-5 / 3 : ℚ), (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -6], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), 0, (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0], ![0, 0, 0, 0, -3]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, 0, 0, 0, (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), -2, 2, 0], ![-2, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, -1, 0, (-2 / 3 : ℚ)], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), -2, 0, 2], ![-2, 0, 0, 0, (9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-1 / 4 : ℚ)], ![(1 / 4 : ℚ), 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-1 / 4 : ℚ)], ![(1 / 2 : ℚ), 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 4 : ℚ), (-11 / 8 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-5 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 4 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 5 : ℚ), 0, 0, 0], ![0, (-2 / 5 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 6 : ℚ), 0, (-1 / 6 : ℚ)], ![(-1 / 12 : ℚ), 0, (-13 / 12 : ℚ), (-1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 4 : ℚ), 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), 0, 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 6 : ℚ), 0, (7 / 6 : ℚ)], ![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (-5 / 3 : ℚ), (7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-15 / 8 : ℚ), 0, (-39 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 4 : ℚ), (-1 / 8 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, -3], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-15 / 8 : ℚ), 0, (-71 / 16 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 4 : ℚ), (-1 / 8 : ℚ), (-35 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-8 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), -2, 2, 0], ![-2, (-2 / 3 : ℚ), -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 8 : ℚ), 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (-17 / 8 : ℚ), (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-11 / 8 : ℚ), 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 2 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-17 / 14 : ℚ), 0, 0], ![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-16 / 7 : ℚ), (-1 / 7 : ℚ), (5 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 5 : ℚ), 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, (-11 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, (-5 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 5 : ℚ), 0, (-47 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-12 / 5 : ℚ), (-1 / 5 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), 0, 0, 0], ![(1 / 10 : ℚ), (-1 / 10 : ℚ), (-9 / 10 : ℚ), (-1 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-124 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-25 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-9 / 5 : ℚ), (-4 / 5 : ℚ), (-32 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 2, 0, -2], ![-2, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 7 : ℚ), (1 / 7 : ℚ), 0, (-1 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-26 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-58 / 17 : ℚ), (-24 / 17 : ℚ), 0, (-8 / 17 : ℚ)], ![0, (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-124 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), (22 / 9 : ℚ), 0, (-68 / 9 : ℚ)], ![(-10 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-34 / 11 : ℚ), (-12 / 11 : ℚ), 0, (-8 / 11 : ℚ)], ![0, (-8 / 11 : ℚ), (-8 / 11 : ℚ), (-76 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-3 / 4 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 4 : ℚ), 0, (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (-1 / 5 : ℚ), -1, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, 0], ![0, (-1 / 3 : ℚ), -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 13 : ℚ), (-66 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ), (9 / 13 : ℚ), (-32 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-3 / 4 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), (-47 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, -3, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![0, 0, -4, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 6 : ℚ), 0, (1 / 3 : ℚ), (-1 / 6 : ℚ)], ![(1 / 2 : ℚ), 0, (-9 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-8 / 3 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-25 / 12 : ℚ), 0, (1 / 4 : ℚ), (-1 / 12 : ℚ)], ![(5 / 12 : ℚ), 0, (-13 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 6 : ℚ), (7 / 6 : ℚ)], ![(-7 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 3 : ℚ), (-7 / 6 : ℚ), (7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-15 / 8 : ℚ), (-41 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 4 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-13 / 3 : ℚ)], ![0, 0, -3, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-15 / 8 : ℚ), (-71 / 16 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 4 : ℚ), (-35 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-2 / 3 : ℚ), (-1 / 12 : ℚ), (-35 / 12 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), 0, (-14 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 2 : ℚ), (-14 / 3 : ℚ)], ![(-13 / 18 : ℚ), (-2 / 9 : ℚ), (-29 / 9 : ℚ), (1 / 2 : ℚ), (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-26 / 9 : ℚ), 0, (-8 / 9 : ℚ), (-8 / 9 : ℚ)], ![0, 0, (-20 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-124 / 17 : ℚ), (-96 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ), (-92 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, 0, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, -1, -1], ![0, 0, -6, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-23 / 4 : ℚ), (-7 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-11 / 2 : ℚ), -3]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (4 / 5 : ℚ), (-8 / 5 : ℚ), 0, (2 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-13 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 12 : ℚ), (-13 / 12 : ℚ), (-7 / 12 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-5 / 12 : ℚ), (-1 / 3 : ℚ), 0], ![(1 / 6 : ℚ), (-1 / 12 : ℚ), (-11 / 12 : ℚ), (-5 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-14 / 5 : ℚ), (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-9 / 8 : ℚ), (-5 / 16 : ℚ), (-9 / 8 : ℚ), 0], ![0, (-1 / 16 : ℚ), (-9 / 4 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 25 : ℚ), (-74 / 25 : ℚ), (-4 / 5 : ℚ), (-64 / 25 : ℚ), (-8 / 25 : ℚ)], ![(-4 / 25 : ℚ), (-8 / 25 : ℚ), (-148 / 25 : ℚ), (-74 / 25 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 17 : ℚ), (-16 / 17 : ℚ), (-48 / 17 : ℚ), (-32 / 17 : ℚ), (-16 / 17 : ℚ)], ![0, 0, (-112 / 17 : ℚ), (-48 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-5 / 2 : ℚ), (-7 / 6 : ℚ), (-5 / 2 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), -5, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)], ![0, 0, 0, 0, (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-7 / 5 : ℚ)], ![0, 0, 0, 0, (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .xy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0, -2], ![(1 / 4 : ℚ), 0, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .yy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, 0, (-6 / 7 : ℚ)], ![0, 0, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, 0, (-7 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ)], ![(-7 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), -1, -1, (-3 / 7 : ℚ), (-1 / 7 : ℚ)], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 7 : ℚ), (-5 / 7 : ℚ), (1 / 7 : ℚ), 0], ![(-3 / 7 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-1 / 5 : ℚ), (-19 / 20 : ℚ), 0, (4 / 5 : ℚ)], ![(-9 / 10 : ℚ), 0, 0, (-9 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), -2, 0, (-8 / 9 : ℚ), (-2 / 9 : ℚ)], ![(2 / 9 : ℚ), 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), (-16 / 5 : ℚ)], ![(-7 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), -2, 0, (-8 / 9 : ℚ), (-1 / 9 : ℚ)], ![(2 / 9 : ℚ), 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-6 / 5 : ℚ), 0], ![(-3 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ), (-12 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .xy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -2, 0, 0], ![(-3 / 4 : ℚ), (-1 / 4 : ℚ), -2, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .yy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-5 / 4 : ℚ), 0, 0, -2], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 34 : ℚ), (-18 / 17 : ℚ), (-1 / 34 : ℚ), (-5 / 17 : ℚ), (5 / 34 : ℚ)], ![(7 / 34 : ℚ), (-1 / 34 : ℚ), 0, (-36 / 17 : ℚ), (-2 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (-1 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ)], ![0, 0, 0, (-43 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (-25 / 22 : ℚ), 0, (-4 / 11 : ℚ), 0], ![0, (-1 / 22 : ℚ), (1 / 22 : ℚ), (-25 / 11 : ℚ), (1 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), 0, (-67 / 44 : ℚ), (1 / 22 : ℚ), (-51 / 11 : ℚ)], ![(-7 / 22 : ℚ), (-1 / 11 : ℚ), (-13 / 11 : ℚ), 0, (-25 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ), (-1 / 10 : ℚ)], ![0, 0, 0, (-23 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 22 : ℚ), (-51 / 22 : ℚ), (17 / 22 : ℚ), (-49 / 22 : ℚ), 0], ![0, (-2 / 11 : ℚ), (21 / 22 : ℚ), (-51 / 11 : ℚ), (1 / 11 : ℚ)]] }
]

theorem conicDetC09_checked : conicDetC09.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
