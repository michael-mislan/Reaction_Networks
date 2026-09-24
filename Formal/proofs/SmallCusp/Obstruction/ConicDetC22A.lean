import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC22A : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-43 / 17 : ℚ), (-24 / 17 : ℚ), (32 / 17 : ℚ), (-3 / 17 : ℚ)], ![0, (-3 / 17 : ℚ), (-43 / 17 : ℚ), (-32 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 3 : ℚ), (-7 / 3 : ℚ), (28 / 15 : ℚ), (-2 / 15 : ℚ)], ![0, (-4 / 15 : ℚ), (-7 / 3 : ℚ), (-28 / 15 : ℚ), (-2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), 0], ![0, 0, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-11 / 5 : ℚ), (-6 / 5 : ℚ), (3 / 5 : ℚ), (-1 / 5 : ℚ)], ![(4 / 5 : ℚ), 0, (-12 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 2 : ℚ), (-3 / 2 : ℚ), (-5 / 2 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 16 : ℚ), (-33 / 16 : ℚ), (-35 / 16 : ℚ), (5 / 16 : ℚ), 0], ![(7 / 16 : ℚ), 0, (-35 / 16 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-3 / 2 : ℚ), 0, 0], ![0, 0, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-7 / 2 : ℚ)], ![0, (-1 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-5 / 3 : ℚ), 0, (-13 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 11 : ℚ), 0, 0, (2 / 11 : ℚ), (-58 / 11 : ℚ)], ![(-15 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (9 / 11 : ℚ), (-28 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 16 : ℚ), (-19 / 8 : ℚ), (-19 / 8 : ℚ), (1 / 4 : ℚ), 0], ![(-1 / 16 : ℚ), (-1 / 4 : ℚ), (-19 / 8 : ℚ), (-13 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-9 / 4 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![0, (-1 / 12 : ℚ), (-9 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), 0, 0, (4 / 5 : ℚ), (-16 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, (-4 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-21 / 10 : ℚ), (-3 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-11 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-16 / 5 : ℚ), (-16 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (-16 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-12 / 5 : ℚ), (-16 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![0, 0, (-16 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 16 : ℚ), (-17 / 16 : ℚ), (-1 / 16 : ℚ), (3 / 16 : ℚ), (5 / 16 : ℚ)], ![(7 / 16 : ℚ), 0, 0, (-3 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)], ![(1 / 6 : ℚ), 0, 0, (-1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 7 : ℚ), (-1 / 7 : ℚ), (3 / 7 : ℚ), (1 / 7 : ℚ)], ![0, (-1 / 7 : ℚ), 0, (-3 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-5 / 3 : ℚ), 0, 1, -1], ![(1 / 18 : ℚ), (-1 / 6 : ℚ), 0, -1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-77 / 34 : ℚ), (15 / 34 : ℚ), (49 / 34 : ℚ), (-3 / 34 : ℚ)], ![(1 / 2 : ℚ), (-3 / 34 : ℚ), (33 / 34 : ℚ), (-49 / 34 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-16 / 13 : ℚ), (-6 / 13 : ℚ), (9 / 13 : ℚ), (-6 / 13 : ℚ)], ![0, 0, 0, (-9 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-100 / 93 : ℚ), (-74 / 31 : ℚ), (28 / 31 : ℚ), (59 / 31 : ℚ), (-4 / 31 : ℚ)], ![(100 / 93 : ℚ), (-8 / 31 : ℚ), (64 / 31 : ℚ), (-59 / 31 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-25 / 24 : ℚ), (-1 / 24 : ℚ), (1 / 8 : ℚ), 0], ![(1 / 8 : ℚ), 0, 0, 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-5 / 4 : ℚ), 0, 1, -1], ![1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, (-5 / 4 : ℚ), 0, -1], ![-1, 0, (-9 / 4 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-3 / 8 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, (-1 / 8 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-33 / 16 : ℚ), (7 / 48 : ℚ), (1 / 48 : ℚ), (-1 / 48 : ℚ)], ![(7 / 48 : ℚ), (-1 / 48 : ℚ), (5 / 16 : ℚ), (-13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (-15 / 16 : ℚ), (-5 / 16 : ℚ), (1 / 16 : ℚ), (-7 / 16 : ℚ)], ![(-3 / 16 : ℚ), 0, (-3 / 16 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(15 / 14 : ℚ), 0, (-12 / 7 : ℚ), (1 / 14 : ℚ), (-17 / 4 : ℚ)], ![(-23 / 14 : ℚ), (-1 / 14 : ℚ), (-15 / 7 : ℚ), (13 / 14 : ℚ), (-59 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-32 / 13 : ℚ), (-1 / 13 : ℚ), (-18 / 13 : ℚ), (-2 / 13 : ℚ)], ![0, (-2 / 13 : ℚ), 0, (-20 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-10 / 9 : ℚ), (-1 / 9 : ℚ), (-14 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, 0, 0, (-16 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-17 / 16 : ℚ), (-1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ)], ![(1 / 4 : ℚ), 0, 0, (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), -1, (-1 / 6 : ℚ), 0, 0], ![(1 / 12 : ℚ), 0, (-1 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ), 0], ![(-1 / 3 : ℚ), 0, (-7 / 6 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.y, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-3 / 2 : ℚ), 0, 1, -1], ![1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-17 / 8 : ℚ), (5 / 4 : ℚ), (11 / 8 : ℚ), (-1 / 8 : ℚ)], ![(3 / 2 : ℚ), 0, (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, 0, (1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 16 : ℚ), (-33 / 16 : ℚ), (19 / 16 : ℚ), (21 / 16 : ℚ), (-1 / 16 : ℚ)], ![(23 / 16 : ℚ), 0, (-19 / 16 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 8 : ℚ), -3, 2, 2, 0], ![(17 / 8 : ℚ), 0, -2, 2, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-13 / 3 : ℚ)], ![0, 0, (1 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-13 / 6 : ℚ), (7 / 6 : ℚ), (7 / 6 : ℚ), (-1 / 3 : ℚ)], ![(4 / 3 : ℚ), 0, (-7 / 6 : ℚ), (7 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(39 / 34 : ℚ), 0, (-11 / 17 : ℚ), (3 / 17 : ℚ), (-89 / 17 : ℚ)], ![(-39 / 34 : ℚ), (-3 / 17 : ℚ), (11 / 17 : ℚ), (27 / 34 : ℚ), (-43 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 3 : ℚ), 0, 0, (2 / 3 : ℚ), (-10 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(21 / 17 : ℚ), 0, (-15 / 34 : ℚ), (4 / 17 : ℚ), (-82 / 17 : ℚ)], ![(-21 / 17 : ℚ), (-4 / 17 : ℚ), (15 / 34 : ℚ), (13 / 17 : ℚ), (-80 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 8 : ℚ), (29 / 24 : ℚ), (-1 / 3 : ℚ), (-1 / 24 : ℚ)], ![0, (-1 / 24 : ℚ), (-29 / 24 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 15 : ℚ), (-12 / 5 : ℚ), (29 / 15 : ℚ), (-7 / 5 : ℚ), 0], ![(1 / 15 : ℚ), (-4 / 15 : ℚ), (-29 / 15 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 3 : ℚ), (5 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 136 : ℚ), (-43 / 17 : ℚ), (32 / 17 : ℚ), (-3 / 17 : ℚ), (-3 / 34 : ℚ)], ![(3 / 136 : ℚ), (-3 / 17 : ℚ), (-32 / 17 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 5 : ℚ), (8 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-8 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 40 : ℚ), (-23 / 10 : ℚ), (17 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 10 : ℚ)], ![(1 / 40 : ℚ), (-1 / 5 : ℚ), (-17 / 10 : ℚ), 0, (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-7 / 3 : ℚ), (5 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![(5 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-20 / 9 : ℚ), (5 / 3 : ℚ), 0, (-2 / 9 : ℚ)], ![(5 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-9 / 4 : ℚ), (3 / 2 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ)], ![(3 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), (-9 / 4 : ℚ), (7 / 4 : ℚ), (-7 / 4 : ℚ), 0], ![(7 / 4 : ℚ), 0, 0, (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-8 / 3 : ℚ), 0, (5 / 3 : ℚ), (-1 / 2 : ℚ)], ![(5 / 3 : ℚ), 0, (-5 / 3 : ℚ), (5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, 0, -1, (-16 / 3 : ℚ)], ![-1, 0, 1, -1, (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 3 : ℚ), (-5 / 2 : ℚ), (4 / 3 : ℚ), (-4 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, (-1 / 6 : ℚ), (4 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -1, 0, 0, -4], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-9 / 4 : ℚ), (1 / 12 : ℚ), (-2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-1 / 36 : ℚ), (-1 / 12 : ℚ), (-4 / 3 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (-14 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 4 : ℚ), 0, (1 / 4 : ℚ), (3 / 4 : ℚ), (-19 / 4 : ℚ)], ![(-3 / 2 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-16 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (-11 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 22 : ℚ), 0, (1 / 11 : ℚ), (-51 / 11 : ℚ), (-95 / 22 : ℚ)], ![(-15 / 22 : ℚ), (-1 / 11 : ℚ), (9 / 22 : ℚ), (-25 / 11 : ℚ), (-47 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 5 : ℚ), 0, (2 / 5 : ℚ), (-14 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-6 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), (-28 / 13 : ℚ), (4 / 13 : ℚ), (-4 / 13 : ℚ), (-2 / 13 : ℚ)], ![0, 0, (-19 / 13 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 6 : ℚ), 0, (1 / 6 : ℚ), (-31 / 6 : ℚ), (-5 / 2 : ℚ)], ![(-7 / 2 : ℚ), (-1 / 6 : ℚ), (5 / 6 : ℚ), (-9 / 2 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-41 / 20 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ)], ![0, 0, (-11 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-83 / 40 : ℚ), (-43 / 40 : ℚ), (-11 / 20 : ℚ), (-3 / 20 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-43 / 40 : ℚ), (-9 / 40 : ℚ), (-3 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, 0, (-6 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-11 / 5 : ℚ), (-8 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![0, 0, (-8 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-47 / 20 : ℚ), 0, (3 / 20 : ℚ), (3 / 20 : ℚ)], ![(11 / 10 : ℚ), (-5 / 4 : ℚ), (3 / 20 : ℚ), (-14 / 5 : ℚ), (-31 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 13 : ℚ), (2 / 13 : ℚ), (-6 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-1 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(15 / 11 : ℚ), 0, (2 / 11 : ℚ), (2 / 11 : ℚ), (-18 / 11 : ℚ)], ![(-17 / 11 : ℚ), (-1 / 11 : ℚ), 0, 0, (-16 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), -2], ![(-1 / 2 : ℚ), (-1 / 4 : ℚ), -1, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 10 : ℚ), (1 / 10 : ℚ), (-43 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 20 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-17 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-23 / 19 : ℚ), (6 / 19 : ℚ), 0], ![(-6 / 19 : ℚ), (-6 / 19 : ℚ), (-46 / 19 : ℚ), (-12 / 19 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 40 : ℚ), 0, (3 / 20 : ℚ), (3 / 40 : ℚ), (-19 / 40 : ℚ)], ![(-7 / 40 : ℚ), (-3 / 40 : ℚ), (-1 / 4 : ℚ), 0, (3 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(17 / 13 : ℚ), 0, (2 / 13 : ℚ), 0, (-20 / 13 : ℚ)], ![(-19 / 13 : ℚ), (-1 / 13 : ℚ), 0, (-2 / 13 : ℚ), (-18 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (1 / 8 : ℚ), (1 / 24 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), (1 / 24 : ℚ), (-1 / 4 : ℚ), (-1 / 24 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 7 : ℚ), (4 / 7 : ℚ), 0, (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (8 / 13 : ℚ), 0, (-76 / 13 : ℚ)], ![(-8 / 13 : ℚ), (-4 / 13 : ℚ), (-16 / 13 : ℚ), (-8 / 13 : ℚ), (-72 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-7 / 3 : ℚ), 0, 0, -2], ![1, (-4 / 3 : ℚ), 0, -4, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 13 : ℚ), 0, (-6 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-1 / 13 : ℚ), (-4 / 13 : ℚ), (-2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-20 / 7 : ℚ), (10 / 7 : ℚ), (-11 / 7 : ℚ), 0], ![0, (-11 / 7 : ℚ), (-16 / 7 : ℚ), (-11 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), -1], ![(-1 / 2 : ℚ), (1 / 6 : ℚ), -1, (-1 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 7 : ℚ), (4 / 7 : ℚ), 0, (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (8 / 11 : ℚ), (-4 / 11 : ℚ), (-60 / 11 : ℚ)], ![(-8 / 11 : ℚ), (-4 / 11 : ℚ), (-16 / 11 : ℚ), (-4 / 11 : ℚ), (-60 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 21 : ℚ), 0, (-4 / 3 : ℚ), (2 / 7 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 21 : ℚ), (-1 / 7 : ℚ), (-50 / 21 : ℚ), (-10 / 21 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 5 : ℚ), (1 / 15 : ℚ), (-10 / 9 : ℚ), (11 / 15 : ℚ), (-4 / 5 : ℚ)], ![(-2 / 3 : ℚ), 0, (-97 / 45 : ℚ), (2 / 5 : ℚ), (1 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 18 : ℚ), (-43 / 18 : ℚ), 0, (1 / 6 : ℚ), (-7 / 18 : ℚ)], ![(10 / 9 : ℚ), (-23 / 18 : ℚ), (1 / 6 : ℚ), (-26 / 9 : ℚ), (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 12 : ℚ), (-79 / 36 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)], ![(1 / 2 : ℚ), (-41 / 36 : ℚ), (1 / 12 : ℚ), (-79 / 36 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 23 : ℚ), 0, (-29 / 23 : ℚ), (6 / 23 : ℚ), (-54 / 23 : ℚ)], ![(-4 / 23 : ℚ), 0, (-52 / 23 : ℚ), (-16 / 23 : ℚ), (-27 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(51 / 50 : ℚ), 0, (-57 / 50 : ℚ), (77 / 75 : ℚ), (-63 / 25 : ℚ)], ![(-57 / 50 : ℚ), (-3 / 50 : ℚ), (-54 / 25 : ℚ), (34 / 75 : ℚ), (3 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(17 / 16 : ℚ), 0, (-23 / 16 : ℚ), (3 / 8 : ℚ), (-41 / 8 : ℚ)], ![(-23 / 16 : ℚ), (-3 / 16 : ℚ), (-5 / 2 : ℚ), 0, (-79 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), 0, (3 / 5 : ℚ), -1, -1], ![(-1 / 5 : ℚ), 0, (-4 / 5 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), (1 / 2 : ℚ), 0, (-1 / 3 : ℚ)], ![0, (-1 / 6 : ℚ), -1, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 19 : ℚ), 0, (12 / 19 : ℚ), 0, (-28 / 19 : ℚ)], ![(-2 / 19 : ℚ), (-6 / 19 : ℚ), (-20 / 19 : ℚ), 0, (12 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 51 : ℚ), 0, (8 / 17 : ℚ), (-13 / 17 : ℚ), (-92 / 17 : ℚ)], ![(-4 / 51 : ℚ), (-4 / 17 : ℚ), (-40 / 51 : ℚ), (13 / 17 : ℚ), (-88 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, (5 / 6 : ℚ), 0, 0], ![(1 / 6 : ℚ), -1, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), 0, 0], ![0, (-1 / 2 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 2, 0, 0], ![0, (-1 / 4 : ℚ), (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 7 : ℚ), (1 / 7 : ℚ), (1 / 7 : ℚ), (-4 / 7 : ℚ), (-6 / 7 : ℚ)], ![(-2 / 7 : ℚ), 0, 0, (1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 13 : ℚ), (-6 / 13 : ℚ), (-58 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-1 / 13 : ℚ), (-4 / 13 : ℚ), (2 / 13 : ℚ), (-57 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, (1 / 2 : ℚ), 0, -1], ![-1, 0, 0, 1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-9 / 4 : ℚ), (7 / 4 : ℚ), 0, 0], ![(-1 / 8 : ℚ), (-5 / 4 : ℚ), (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (3 / 16 : ℚ), (-25 / 16 : ℚ), (-27 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (-1 / 2 : ℚ), (-11 / 8 : ℚ), (-27 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 29 : ℚ), (-86 / 29 : ℚ), (48 / 29 : ℚ), 0, (-42 / 29 : ℚ)], ![(2 / 29 : ℚ), (-45 / 29 : ℚ), (-64 / 29 : ℚ), (4 / 29 : ℚ), (-40 / 29 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-2 / 3 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), 0], ![0, (-1 / 3 : ℚ), -2, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 9 : ℚ), (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(101 / 48 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ), (-9 / 2 : ℚ)], ![(-109 / 48 : ℚ), (-1 / 12 : ℚ), 0, 1, (-53 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 4 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (1 / 12 : ℚ), -4, (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(11 / 7 : ℚ), (10 / 7 : ℚ), (20 / 7 : ℚ), (5 / 7 : ℚ), (-30 / 7 : ℚ)], ![(-13 / 7 : ℚ), (4 / 7 : ℚ), 0, (3 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 9 : ℚ), (4 / 9 : ℚ), 0, (-10 / 3 : ℚ)], ![(-4 / 9 : ℚ), -1, -4, 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 19 : ℚ), (-16 / 19 : ℚ), (12 / 19 : ℚ), (-24 / 19 : ℚ), 0], ![0, (-8 / 19 : ℚ), (-48 / 19 : ℚ), (12 / 19 : ℚ), 0]] }
]

theorem conicDetC22A_checked : conicDetC22A.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
