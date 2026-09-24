import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC17 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 6 : ℚ), 0, 0, 0, -4], ![-3, 0, 0, (-7 / 6 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 1, -1], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 8 : ℚ), 0, 0, (9 / 8 : ℚ), -1], ![-1, 0, 0, (-1 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 22 : ℚ), 0, (2 / 11 : ℚ), (-24 / 11 : ℚ)], ![(-1 / 22 : ℚ), (-19 / 22 : ℚ), 0, (-19 / 44 : ℚ), (-12 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), 0, -4, (-3 / 5 : ℚ), 0], ![(-1 / 10 : ℚ), -2, -2, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(6 / 5 : ℚ), (3 / 5 : ℚ), 0, 0, (-14 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 3 : ℚ), (-7 / 9 : ℚ), 0, 0], ![(1 / 3 : ℚ), -1, (-5 / 9 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ), -4], ![(-4 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, (1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 7 : ℚ), 0, -4, (17 / 14 : ℚ), 0], ![(19 / 14 : ℚ), -2, -2, (1 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, -4], ![(-1 / 2 : ℚ), 0, 0, -1, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-2 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(41 / 22 : ℚ), 0, 0, (2 / 11 : ℚ), -4], ![(-45 / 22 : ℚ), 0, 0, 1, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 12 : ℚ), 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 24 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-12 / 7 : ℚ)], ![(-3 / 7 : ℚ), (-13 / 14 : ℚ), (-3 / 14 : ℚ), (-3 / 7 : ℚ), (3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, -2], ![(-1 / 2 : ℚ), -1, -1, 0, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), (2 / 11 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ)], ![(1 / 11 : ℚ), (-7 / 11 : ℚ), (2 / 11 : ℚ), (-10 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), (-3 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (12 / 25 : ℚ), (12 / 25 : ℚ), (12 / 25 : ℚ), (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-24 / 25 : ℚ), (-24 / 25 : ℚ), (-24 / 25 : ℚ), (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ), 0], ![(4 / 9 : ℚ), (-16 / 9 : ℚ), (-8 / 3 : ℚ), (-16 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 35 : ℚ), (16 / 35 : ℚ), (16 / 35 : ℚ), (-4 / 5 : ℚ)], ![(-16 / 35 : ℚ), (-32 / 35 : ℚ), (-32 / 35 : ℚ), (-32 / 35 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 22 : ℚ), (1 / 11 : ℚ), 0, (1 / 11 : ℚ), 0], ![(1 / 22 : ℚ), (-7 / 22 : ℚ), (1 / 11 : ℚ), (-5 / 11 : ℚ), (-9 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 17 : ℚ), (-2 / 17 : ℚ), (3 / 17 : ℚ), 0], ![(-3 / 17 : ℚ), (-6 / 17 : ℚ), (-4 / 17 : ℚ), (-6 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), 0, 0], ![(1 / 11 : ℚ), (-7 / 11 : ℚ), (-10 / 11 : ℚ), (-9 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (12 / 25 : ℚ), (12 / 25 : ℚ), 0, (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-24 / 25 : ℚ), (-24 / 25 : ℚ), (-12 / 25 : ℚ), (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ), 0, 0], ![(4 / 9 : ℚ), (-16 / 9 : ℚ), (-8 / 3 : ℚ), (-8 / 3 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 35 : ℚ), (16 / 35 : ℚ), 0, (-4 / 5 : ℚ)], ![(-16 / 35 : ℚ), (-32 / 35 : ℚ), (-32 / 35 : ℚ), (-16 / 35 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-3 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 10 : ℚ), (1 / 10 : ℚ), 0, (-1 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (12 / 25 : ℚ), (12 / 25 : ℚ), 0, (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-24 / 25 : ℚ), (-24 / 25 : ℚ), (-12 / 25 : ℚ), (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), (4 / 9 : ℚ), 0, (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 17 : ℚ), (8 / 17 : ℚ), 0, (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-16 / 17 : ℚ), (-16 / 17 : ℚ), 0, (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 19 : ℚ), (1 / 19 : ℚ), (-6 / 19 : ℚ), (1 / 19 : ℚ), (-1 / 19 : ℚ)], ![(9 / 19 : ℚ), (-12 / 19 : ℚ), (14 / 19 : ℚ), (-22 / 19 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)], ![(1 / 3 : ℚ), (-5 / 6 : ℚ), (1 / 6 : ℚ), (-4 / 3 : ℚ), (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 16 : ℚ), (1 / 8 : ℚ), 0, (1 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (-15 / 16 : ℚ), (1 / 16 : ℚ), (-63 / 16 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 6 : ℚ), 0], ![(1 / 3 : ℚ), (-5 / 6 : ℚ), (1 / 6 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 48 : ℚ), (1 / 6 : ℚ), (-17 / 48 : ℚ), (1 / 6 : ℚ), 0], ![(-1 / 48 : ℚ), (-23 / 48 : ℚ), (1 / 6 : ℚ), (-5 / 8 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 4 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, 0, 0], ![(-1 / 6 : ℚ), -1, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-1 / 4 : ℚ)], ![(1 / 12 : ℚ), (-7 / 12 : ℚ), (1 / 6 : ℚ), (-5 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), (2 / 11 : ℚ), 0, (2 / 11 : ℚ), 0], ![(1 / 11 : ℚ), (-7 / 11 : ℚ), (2 / 11 : ℚ), (-10 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (-3 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-1 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 7 : ℚ), 0, (1 / 7 : ℚ), 0], ![(-1 / 14 : ℚ), (-6 / 7 : ℚ), 0, (-27 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 33 : ℚ), (2 / 11 : ℚ), (-2 / 33 : ℚ), (2 / 11 : ℚ), 0], ![(1 / 33 : ℚ), (-19 / 33 : ℚ), (4 / 33 : ℚ), (-26 / 33 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 6 : ℚ), 0, (1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (-2 / 3 : ℚ), (1 / 6 : ℚ), -1, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), (2 / 11 : ℚ), 0, (2 / 11 : ℚ), 0], ![(1 / 11 : ℚ), (-7 / 11 : ℚ), (2 / 11 : ℚ), (-10 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (1 / 4 : ℚ), 0], ![(-1 / 2 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 17 : ℚ), (-2 / 17 : ℚ), (3 / 17 : ℚ), 0], ![0, (-6 / 17 : ℚ), (-1 / 17 : ℚ), (-6 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), 0, (1 / 12 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 12 : ℚ), (-1 / 3 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-7 / 18 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 53 : ℚ), (8 / 53 : ℚ), (-8 / 53 : ℚ), (8 / 53 : ℚ), (-4 / 53 : ℚ)], ![(-3 / 53 : ℚ), (-21 / 53 : ℚ), (-8 / 53 : ℚ), (-26 / 53 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 7 : ℚ), 0, 0, 0, 0], ![(1 / 7 : ℚ), (-5 / 7 : ℚ), (1 / 7 : ℚ), (-8 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ), (-8 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), 0, 0, 0, 0], ![(4 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ), (-20 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), 1, (1 / 6 : ℚ), -1], ![-1, 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 19 : ℚ), (9 / 19 : ℚ), (2 / 19 : ℚ), (-3 / 19 : ℚ)], ![(-2 / 19 : ℚ), (-12 / 19 : ℚ), (-9 / 19 : ℚ), (-66 / 19 : ℚ), (-1 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (2 / 11 : ℚ), 0, (2 / 11 : ℚ), (-14 / 11 : ℚ)], ![0, (-13 / 11 : ℚ), (-2 / 11 : ℚ), (-46 / 11 : ℚ), (-6 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ), (-17 / 6 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 17 : ℚ), (4 / 17 : ℚ), 0, (4 / 17 : ℚ), (-14 / 17 : ℚ)], ![0, (-21 / 17 : ℚ), (-4 / 17 : ℚ), (-72 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, -1], ![0, -1, -1, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, (-3 / 8 : ℚ)], ![0, -1, -1, 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), 0, 0], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 2, 0, 0], ![0, (-3 / 4 : ℚ), (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 36 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-11 / 36 : ℚ), 0], ![(1 / 36 : ℚ), (-19 / 36 : ℚ), (-13 / 18 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (-2 / 3 : ℚ), -1, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (-7 / 24 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-5 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 7 : ℚ), (1 / 7 : ℚ), 0, 0], ![(-1 / 14 : ℚ), (-6 / 7 : ℚ), (-27 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), 0, (-1 / 10 : ℚ)], ![(1 / 2 : ℚ), (-4 / 5 : ℚ), (-7 / 5 : ℚ), 1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 11 : ℚ), (1 / 11 : ℚ), (1 / 11 : ℚ), (-1 / 11 : ℚ), (-18 / 11 : ℚ)], ![(5 / 11 : ℚ), (-8 / 11 : ℚ), (-14 / 11 : ℚ), 0, (27 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), 0, (-1 / 11 : ℚ)], ![(1 / 11 : ℚ), (-7 / 11 : ℚ), (-10 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 25 : ℚ), (12 / 25 : ℚ), (12 / 25 : ℚ), (12 / 25 : ℚ), 0], ![(2 / 25 : ℚ), (-38 / 25 : ℚ), (-52 / 25 : ℚ), (-38 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 35 : ℚ), (16 / 35 : ℚ), (16 / 35 : ℚ), (-4 / 5 : ℚ)], ![(-16 / 35 : ℚ), (-32 / 35 : ℚ), (-32 / 35 : ℚ), (-32 / 35 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 14 : ℚ), (3 / 14 : ℚ), 0, (-1 / 2 : ℚ)], ![(-3 / 14 : ℚ), -1, -4, (-3 / 14 : ℚ), (-1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (3 / 7 : ℚ), 0, (-12 / 7 : ℚ)], ![(-3 / 7 : ℚ), (-13 / 14 : ℚ), -4, (-3 / 7 : ℚ), (3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ), (-1 / 3 : ℚ), 0], ![(-1 / 9 : ℚ), (-4 / 3 : ℚ), (-14 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), (4 / 9 : ℚ), (-16 / 9 : ℚ), (-28 / 27 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ), (-8 / 27 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 35 : ℚ), (16 / 35 : ℚ), (-16 / 15 : ℚ), (-4 / 5 : ℚ)], ![(-16 / 35 : ℚ), (-32 / 35 : ℚ), (-32 / 35 : ℚ), (-32 / 105 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 0, (-1 / 6 : ℚ)], ![(1 / 6 : ℚ), (-2 / 3 : ℚ), -1, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ), 0, 0], ![(4 / 11 : ℚ), (-16 / 11 : ℚ), (-24 / 11 : ℚ), (4 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 47 : ℚ), (16 / 47 : ℚ), (16 / 47 : ℚ), 0, (-16 / 47 : ℚ)], ![(-2 / 47 : ℚ), (-46 / 47 : ℚ), (-60 / 47 : ℚ), (8 / 47 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), (1 / 6 : ℚ), (-7 / 12 : ℚ), (5 / 36 : ℚ), (1 / 6 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 6 : ℚ), (1 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (1 / 12 : ℚ), (1 / 24 : ℚ), 0, (-5 / 12 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, (-1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (12 / 25 : ℚ), 0, 0, (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-24 / 25 : ℚ), (-12 / 25 : ℚ), (-12 / 25 : ℚ), (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (4 / 9 : ℚ), (-20 / 27 : ℚ), 0, 0], ![(4 / 9 : ℚ), (-16 / 9 : ℚ), (-52 / 27 : ℚ), (-16 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 17 : ℚ), 0, 0, (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-16 / 17 : ℚ), (-8 / 17 : ℚ), 0, (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (1 / 5 : ℚ), (-1 / 2 : ℚ), (1 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-3 / 10 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-3 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 16 : ℚ), (1 / 32 : ℚ), (-37 / 64 : ℚ), (1 / 64 : ℚ), (-3 / 16 : ℚ)], ![(-3 / 32 : ℚ), 0, (29 / 64 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), 0, (1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 184 : ℚ), (19 / 92 : ℚ), (-19 / 184 : ℚ), (3 / 184 : ℚ), (109 / 184 : ℚ)], ![(-7 / 184 : ℚ), (-43 / 184 : ℚ), (3 / 92 : ℚ), 0, (-153 / 184 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 9 : ℚ), 0], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-7 / 18 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 13 : ℚ), (2 / 13 : ℚ), 0, 0, (-3 / 13 : ℚ)], ![(1 / 13 : ℚ), (-7 / 13 : ℚ), (2 / 13 : ℚ), 0, (-6 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (1 / 10 : ℚ), 0, 0, 0], ![(1 / 10 : ℚ), (-3 / 10 : ℚ), (1 / 10 : ℚ), (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (-3 / 11 : ℚ), 0, (-3 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-1 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (-3 / 11 : ℚ), 0, (2 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-1 / 11 : ℚ), (-2 / 11 : ℚ), (-4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (11 / 28 : ℚ), 0, 0, 0], ![(-1 / 14 : ℚ), (-17 / 28 : ℚ), 0, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 26 : ℚ), (1 / 13 : ℚ), 0, 0, 0], ![(-1 / 26 : ℚ), (-9 / 26 : ℚ), (1 / 13 : ℚ), (-11 / 26 : ℚ), (1 / 26 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (1 / 7 : ℚ), (-1 / 7 : ℚ), 0, 0], ![(1 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-6 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 11 : ℚ), (-3 / 11 : ℚ), 0, (-7 / 22 : ℚ)], ![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-1 / 11 : ℚ), (-2 / 11 : ℚ), (-5 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 16 : ℚ), (-1 / 16 : ℚ), (-1 / 16 : ℚ), 0], ![0, (-3 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 18 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 9 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 17 : ℚ), (-2 / 17 : ℚ), 0, (-9 / 34 : ℚ)], ![(-3 / 17 : ℚ), (-6 / 17 : ℚ), (-4 / 17 : ℚ), 0, (-3 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 17 : ℚ), (-2 / 17 : ℚ), 0, (3 / 17 : ℚ)], ![(-3 / 17 : ℚ), (-6 / 17 : ℚ), (-4 / 17 : ℚ), 0, (-6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 36 : ℚ), (1 / 6 : ℚ), (1 / 36 : ℚ), (-7 / 36 : ℚ), 0], ![(1 / 36 : ℚ), (-19 / 36 : ℚ), (1 / 18 : ℚ), (-7 / 18 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), 0, (-1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 17 : ℚ), (-2 / 17 : ℚ), 0, (-16 / 51 : ℚ)], ![(-3 / 17 : ℚ), (-6 / 17 : ℚ), (-4 / 17 : ℚ), 0, (-11 / 51 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, -1], ![(-1 / 2 : ℚ), 0, -2, (-1 / 2 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, -2, (-1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 6 : ℚ), (-5 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-11 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, 0, 0, -4], ![(-2 / 3 : ℚ), 0, -2, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, 0, 0, -4], ![(-2 / 3 : ℚ), 0, -2, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, -2, (-1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 3 : ℚ), (1 / 6 : ℚ), 2, (5 / 6 : ℚ), -2], ![-2, 1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 27 : ℚ), (5 / 54 : ℚ), 0, (-32 / 27 : ℚ), (1 / 6 : ℚ)], ![0, (-28 / 27 : ℚ), (-41 / 54 : ℚ), (-59 / 18 : ℚ), (11 / 54 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 13 : ℚ), (-6 / 13 : ℚ), 0, (-6 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-21 / 13 : ℚ), (-2 / 13 : ℚ), (-64 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), (1 / 6 : ℚ), (25 / 12 : ℚ), (1 / 4 : ℚ), (-14 / 3 : ℚ)], ![(-9 / 4 : ℚ), (5 / 12 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 17 : ℚ), 0, (-5 / 17 : ℚ), (-24 / 17 : ℚ)], ![(-2 / 17 : ℚ), (-19 / 17 : ℚ), (-21 / 34 : ℚ), (-7 / 2 : ℚ), (-23 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (-1 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, -1, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 7 : ℚ), (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (-24 / 7 : ℚ)], ![(-8 / 7 : ℚ), 0, 0, 0, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 19 : ℚ), (8 / 19 : ℚ), (-3 / 19 : ℚ), 0, 0], ![(3 / 19 : ℚ), -1, (-14 / 19 : ℚ), 0, (4 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, 0, 0], ![0, (-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 1, 0, 0], ![0, (-3 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, -1, -2], ![(-2 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ), (-5 / 6 : ℚ), (-4 / 3 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 6 : ℚ), (-4 / 9 : ℚ), 0, (-1 / 12 : ℚ)], ![(1 / 3 : ℚ), (-5 / 6 : ℚ), (-19 / 18 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), 0, 0, 0], ![0, (-1 / 4 : ℚ), (-1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (11 / 28 : ℚ), 0, 0, 0], ![(-1 / 14 : ℚ), (-17 / 28 : ℚ), -2, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 20 : ℚ), (1 / 20 : ℚ), (-7 / 20 : ℚ), 0, (-1 / 20 : ℚ)], ![(1 / 2 : ℚ), (-13 / 20 : ℚ), (-13 / 10 : ℚ), 1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 11 : ℚ), (1 / 11 : ℚ), (1 / 22 : ℚ), (-1 / 11 : ℚ), (-18 / 11 : ℚ)], ![(5 / 11 : ℚ), (-8 / 11 : ℚ), (-37 / 22 : ℚ), 0, (27 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (2 / 11 : ℚ), 0, (-2 / 11 : ℚ), (-3 / 22 : ℚ)], ![(-1 / 11 : ℚ), (-5 / 11 : ℚ), (-3 / 11 : ℚ), 0, (-1 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (12 / 25 : ℚ), 0, (12 / 25 : ℚ), (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-24 / 25 : ℚ), (-12 / 25 : ℚ), (-24 / 25 : ℚ), (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (4 / 9 : ℚ), 0, (4 / 9 : ℚ), 0], ![(4 / 9 : ℚ), (-16 / 9 : ℚ), (-8 / 3 : ℚ), (-16 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 35 : ℚ), 0, (16 / 35 : ℚ), (-4 / 5 : ℚ)], ![(-16 / 35 : ℚ), (-32 / 35 : ℚ), (-16 / 35 : ℚ), (-32 / 35 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -1], ![(-3 / 7 : ℚ), (-13 / 14 : ℚ), -2, (-3 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (6 / 7 : ℚ), 0, (-12 / 7 : ℚ)], ![(-3 / 7 : ℚ), (-13 / 14 : ℚ), (-6 / 7 : ℚ), (-5 / 7 : ℚ), (3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![(-4 / 9 : ℚ), (-17 / 18 : ℚ), (-22 / 9 : ℚ), 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, (-16 / 9 : ℚ), (-28 / 27 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ), (-8 / 27 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-32 / 105 : ℚ), (16 / 35 : ℚ), 0, (-16 / 35 : ℚ), (-4 / 21 : ℚ)], ![(-16 / 105 : ℚ), (-128 / 105 : ℚ), (-32 / 35 : ℚ), 0, (4 / 105 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ), (-4 / 3 : ℚ), (-5 / 6 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 31 : ℚ), (12 / 31 : ℚ), (6 / 31 : ℚ), (-52 / 31 : ℚ), (-44 / 31 : ℚ)], ![(-14 / 31 : ℚ), (-22 / 31 : ℚ), 0, (12 / 31 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 11 : ℚ), 0, (-7 / 11 : ℚ), (-6 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-8 / 11 : ℚ), (-4 / 11 : ℚ), (-5 / 11 : ℚ), (-2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .xy), (.xx, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 24 : ℚ), 0], ![0, (-1 / 4 : ℚ), (1 / 12 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy), (.xx, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (1 / 6 : ℚ), (1 / 48 : ℚ), 0, (-7 / 16 : ℚ)], ![(-5 / 48 : ℚ), (-19 / 48 : ℚ), (-7 / 48 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xx, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (12 / 25 : ℚ), (-24 / 25 : ℚ), (-12 / 5 : ℚ), (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-24 / 25 : ℚ), (-36 / 25 : ℚ), (-66 / 25 : ℚ), (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), (-2 / 9 : ℚ), (-5 / 9 : ℚ), (-8 / 9 : ℚ)], ![0, (-4 / 3 : ℚ), (-2 / 3 : ℚ), (-7 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xx, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (8 / 17 : ℚ), (-8 / 17 : ℚ), (-12 / 17 : ℚ), (4 / 17 : ℚ)], ![0, (-24 / 17 : ℚ), (-8 / 17 : ℚ), (-12 / 17 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 12 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 4 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 10 : ℚ), (-7 / 10 : ℚ), 0, (-1 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (1 / 2 : ℚ), 0, (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), 0, (1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (-3 / 20 : ℚ), 0, 0], ![(-1 / 20 : ℚ), (-11 / 20 : ℚ), (1 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), 0], ![0, (-4 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), 0, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0], ![0, (-3 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (1 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 7 : ℚ), 0, (-1 / 14 : ℚ), 0], ![(-1 / 14 : ℚ), (-6 / 7 : ℚ), 0, (-1 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-3 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (1 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-1 / 5 : ℚ)], ![0, (-3 / 10 : ℚ), 0, (-1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, -1], ![(-1 / 2 : ℚ), 0, -2, (-1 / 2 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, -2, (-1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, 0, -1], ![(-1 / 2 : ℚ), 0, -2, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), 0, 0, 0, -4], ![(-4 / 7 : ℚ), 0, -2, (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, 0, 0, -4], ![(-2 / 3 : ℚ), 0, -2, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, -4], ![-1, 0, -2, 0, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), 1, 0, -1], ![-1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 9 : ℚ), (1 / 9 : ℚ), (10 / 9 : ℚ), (-1 / 9 : ℚ), (-8 / 9 : ℚ)], ![(-4 / 9 : ℚ), 0, (-7 / 9 : ℚ), (-1 / 9 : ℚ), (-8 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 11 : ℚ), (1 / 22 : ℚ), (23 / 22 : ℚ), 0, (-43 / 11 : ℚ)], ![(-59 / 88 : ℚ), 0, (-37 / 88 : ℚ), (-51 / 88 : ℚ), (-85 / 44 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 12 : ℚ), (7 / 6 : ℚ), 0, -4], ![(-5 / 12 : ℚ), (1 / 12 : ℚ), (-5 / 6 : ℚ), 0, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (1 / 10 : ℚ), 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-1 / 10 : ℚ), (2 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (2 / 9 : ℚ), (-1 / 3 : ℚ), 0, (1 / 9 : ℚ)], ![(2 / 9 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, -1, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -1], ![0, -1, (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, -1, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), 0], ![0, (-1 / 2 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, 0, 0], ![0, (-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, 0], ![0, (-3 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 6 : ℚ), (-19 / 18 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (1 / 6 : ℚ), (-4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 24 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 8 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), 0, 0], ![(1 / 3 : ℚ), (-5 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (-1 / 8 : ℚ), 0, 0], ![0, (-1 / 2 : ℚ), (-1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (11 / 28 : ℚ), 0, (-1 / 14 : ℚ), (1 / 14 : ℚ)], ![(-1 / 7 : ℚ), (-15 / 28 : ℚ), 0, (-1 / 14 : ℚ), (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 5 : ℚ), (1 / 20 : ℚ), (-8 / 5 : ℚ), (31 / 20 : ℚ), (-1 / 2 : ℚ)], ![(31 / 20 : ℚ), (-17 / 10 : ℚ), (-8 / 5 : ℚ), (31 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-11 / 5 : ℚ)], ![0, (-3 / 5 : ℚ), (-1 / 5 : ℚ), 0, 2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 25 : ℚ), (12 / 25 : ℚ), 0, (12 / 25 : ℚ), 0], ![(2 / 25 : ℚ), (-38 / 25 : ℚ), (-28 / 25 : ℚ), (-38 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 17 : ℚ), 0, (8 / 17 : ℚ), (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-16 / 17 : ℚ), 0, (-16 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 38 : ℚ), (31 / 76 : ℚ), 0, 0, 0], ![(1 / 38 : ℚ), (-3 / 4 : ℚ), (-7 / 19 : ℚ), (-7 / 19 : ℚ), (3 / 38 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (3 / 14 : ℚ), 0, (-12 / 7 : ℚ)], ![(-3 / 7 : ℚ), (-13 / 14 : ℚ), (-3 / 14 : ℚ), (-3 / 7 : ℚ), (3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, 0, (-2 / 3 : ℚ)], ![(-4 / 9 : ℚ), -1, 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), 0, (-8 / 9 : ℚ), (-4 / 27 : ℚ)], ![0, (-4 / 3 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ), (4 / 27 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 17 : ℚ), 0, (-56 / 51 : ℚ), (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-16 / 17 : ℚ), 0, (-16 / 51 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 6 : ℚ), (-7 / 12 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 23 : ℚ), (8 / 23 : ℚ), (-16 / 23 : ℚ), 0, (-4 / 23 : ℚ)], ![(8 / 23 : ℚ), (-32 / 23 : ℚ), (-16 / 23 : ℚ), (8 / 23 : ℚ), (-4 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.xx, .xy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (2 / 5 : ℚ), (-3 / 10 : ℚ), 0, (-1 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-3 / 10 : ℚ), 0, (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (1 / 5 : ℚ), (4 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 16 : ℚ), (-9 / 16 : ℚ), (-1 / 16 : ℚ), (-1 / 16 : ℚ)], ![0, (-1 / 8 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (1 / 20 : ℚ), (-4 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 20 : ℚ)], ![0, (-3 / 20 : ℚ), (1 / 4 : ℚ), (1 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0], ![0, (-2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (-1 / 4 : ℚ), 0, 0], ![0, (-5 / 8 : ℚ), (1 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0], ![0, (-1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 17 : ℚ), (3 / 17 : ℚ), (-1 / 17 : ℚ), 0, 0], ![(2 / 17 : ℚ), (-8 / 17 : ℚ), (2 / 17 : ℚ), (3 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 24 : ℚ), 0, (-1 / 6 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 24 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-1 / 4 : ℚ), (-1 / 6 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 13 : ℚ), (2 / 13 : ℚ), 0, 0, (2 / 13 : ℚ)], ![(1 / 13 : ℚ), (-7 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ), (-7 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (3 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-3 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-2 / 5 : ℚ), (-3 / 20 : ℚ), (1 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 14 : ℚ), (1 / 7 : ℚ), 0, (-1 / 14 : ℚ), (-1 / 7 : ℚ)], ![(1 / 14 : ℚ), (-1 / 2 : ℚ), (1 / 7 : ℚ), 0, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 53 : ℚ), (8 / 53 : ℚ), (-5 / 53 : ℚ), (-6 / 53 : ℚ), 0], ![(-1 / 53 : ℚ), (-23 / 53 : ℚ), (3 / 53 : ℚ), (-4 / 53 : ℚ), (4 / 53 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![0, (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, -1], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0, 0], ![(1 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 1], ![0, -1, 0, 0, -1]] }
]

theorem conicDetC17_checked : conicDetC17.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
