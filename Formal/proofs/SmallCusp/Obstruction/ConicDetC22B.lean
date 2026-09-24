import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC22B : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-41 / 37 : ℚ), 0, (12 / 37 : ℚ), (-172 / 37 : ℚ), (-172 / 37 : ℚ)], ![(-53 / 74 : ℚ), 0, (-106 / 37 : ℚ), (-86 / 37 : ℚ), (-166 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), (-16 / 15 : ℚ), (4 / 15 : ℚ), (-8 / 15 : ℚ), (-8 / 15 : ℚ)], ![0, (-2 / 3 : ℚ), (-16 / 15 : ℚ), (4 / 15 : ℚ), (4 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 8 : ℚ), -4, (1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), -2, (-29 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 11 : ℚ), (-56 / 11 : ℚ), (-36 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-8 / 11 : ℚ), (-54 / 11 : ℚ), (-32 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (2 / 15 : ℚ), (16 / 45 : ℚ), (4 / 15 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 3 : ℚ), 0, (11 / 45 : ℚ), (2 / 15 : ℚ), (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (1 / 8 : ℚ), 0, 0, (-5 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 8 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (1 / 8 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (1 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-8 / 21 : ℚ), (-2 / 7 : ℚ), (-8 / 7 : ℚ)], ![0, (-4 / 7 : ℚ), (-4 / 3 : ℚ), (-6 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), 0, 0, -6], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0, -6]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 8 : ℚ), (-7 / 8 : ℚ), (-3 / 8 : ℚ), 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (-7 / 4 : ℚ), (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-21 / 38 : ℚ), (-79 / 38 : ℚ), 0, (-20 / 19 : ℚ), (6 / 19 : ℚ)], ![(9 / 19 : ℚ), (-41 / 38 : ℚ), 0, (-40 / 19 : ℚ), (3 / 38 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (-7 / 6 : ℚ), 0, (-5 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-7 / 3 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(9 / 17 : ℚ), (3 / 34 : ℚ), (-37 / 34 : ℚ), (1 / 34 : ℚ), (3 / 34 : ℚ)], ![(-21 / 34 : ℚ), 0, (-37 / 17 : ℚ), (1 / 17 : ℚ), (6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), (-1 / 6 : ℚ), (-8 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-7 / 3 : ℚ), (-1 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-76 / 11 : ℚ)], ![(-8 / 11 : ℚ), 0, (-38 / 11 : ℚ), 0, (-72 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 17 : ℚ), (3 / 17 : ℚ), (3 / 34 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ)], ![(-2 / 17 : ℚ), 0, 0, (8 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), 0, (1 / 5 : ℚ), -1, -1], ![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 6 : ℚ), (1 / 4 : ℚ), 0, (-5 / 6 : ℚ)], ![(-1 / 4 : ℚ), (1 / 12 : ℚ), 0, 0, (-5 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 19 : ℚ), (12 / 19 : ℚ), (8 / 19 : ℚ), 0, (-40 / 19 : ℚ)], ![(-8 / 19 : ℚ), 0, (4 / 19 : ℚ), 0, (12 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 17 : ℚ), 0, (-9 / 17 : ℚ), (-84 / 17 : ℚ)], ![0, (-8 / 17 : ℚ), (-8 / 17 : ℚ), (9 / 17 : ℚ), (-80 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, (1 / 12 : ℚ), 0, 0], ![(1 / 4 : ℚ), -1, (-19 / 12 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (3 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![(-2 / 5 : ℚ), 0, (-3 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), 1, 0, 0], ![0, (-2 / 5 : ℚ), (-8 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-4 / 17 : ℚ), (-2 / 17 : ℚ), (-6 / 17 : ℚ), 0], ![0, (-2 / 17 : ℚ), (-7 / 17 : ℚ), (3 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 18 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 12 : ℚ), (-7 / 36 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-151 / 48 : ℚ), (-101 / 24 : ℚ), (-157 / 48 : ℚ), (67 / 48 : ℚ), (-1 / 24 : ℚ)], ![(25 / 16 : ℚ), (-103 / 48 : ℚ), (-53 / 8 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, 0, 0, -1], ![-1, 0, (-1 / 4 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 4 : ℚ), 0, (-7 / 4 : ℚ), (7 / 4 : ℚ)], ![(-7 / 2 : ℚ), 0, (-1 / 4 : ℚ), (-7 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), 0, 0, (-3 / 2 : ℚ), (-20 / 3 : ℚ)], ![(-1 / 9 : ℚ), 0, (-1 / 6 : ℚ), (-4 / 3 : ℚ), (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 72 : ℚ), 0, (1 / 24 : ℚ), (-13 / 8 : ℚ), (-17 / 4 : ℚ)], ![(-7 / 72 : ℚ), (-1 / 24 : ℚ), 0, (-11 / 8 : ℚ), (-101 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), 0, (1 / 8 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), (1 / 24 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (-4 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(101 / 48 : ℚ), 0, 0, (1 / 6 : ℚ), (-9 / 2 : ℚ)], ![(-109 / 48 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), 1, (-53 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), 0, 0, (6 / 7 : ℚ), (-6 / 7 : ℚ)], ![(-3 / 7 : ℚ), 0, (-1 / 7 : ℚ), (-2 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (3 / 7 : ℚ), 0, 1, (-19 / 7 : ℚ)], ![(-13 / 14 : ℚ), 0, (-3 / 7 : ℚ), 0, (3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 6 : ℚ), (13 / 12 : ℚ), 0, (-7 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 2 : ℚ), (-13 / 12 : ℚ), 0, (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 19 : ℚ), 0, 0, (-40 / 19 : ℚ), (-16 / 19 : ℚ)], ![(-8 / 19 : ℚ), 0, (-12 / 19 : ℚ), (12 / 19 : ℚ), (-8 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 11 : ℚ), (-32 / 33 : ℚ), (-16 / 33 : ℚ), (-148 / 33 : ℚ), (-148 / 33 : ℚ)], ![0, (-16 / 33 : ℚ), (-56 / 33 : ℚ), (-74 / 33 : ℚ), (-136 / 33 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 36 : ℚ), (2 / 9 : ℚ), (1 / 12 : ℚ), (-13 / 18 : ℚ), (-19 / 36 : ℚ)], ![(-7 / 36 : ℚ), (1 / 36 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), -4, (11 / 8 : ℚ), 0, 0], ![(1 / 8 : ℚ), -2, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 36 : ℚ), 0, (1 / 12 : ℚ), (-59 / 9 : ℚ), (-31 / 12 : ℚ)], ![(-7 / 36 : ℚ), (-1 / 12 : ℚ), 0, (-49 / 9 : ℚ), (-29 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 53 : ℚ), (-18 / 53 : ℚ), (-4 / 53 : ℚ), (-10 / 53 : ℚ), (-16 / 53 : ℚ)], ![0, (-13 / 53 : ℚ), (-12 / 53 : ℚ), (-14 / 53 : ℚ), (8 / 53 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 12 : ℚ), (-1 / 2 : ℚ), (-5 / 12 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 33 : ℚ), (-12 / 11 : ℚ), (-8 / 33 : ℚ), (-20 / 33 : ℚ), (-32 / 33 : ℚ)], ![0, (-26 / 33 : ℚ), (-8 / 11 : ℚ), (-28 / 33 : ℚ), (16 / 33 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(11 / 14 : ℚ), (15 / 7 : ℚ), (-37 / 14 : ℚ), 0, (-23 / 14 : ℚ)], ![(-11 / 14 : ℚ), 0, (-71 / 14 : ℚ), (-3 / 14 : ℚ), (23 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 12 : ℚ), (-137 / 36 : ℚ), (-1 / 72 : ℚ), (-149 / 72 : ℚ), 1], ![(14 / 9 : ℚ), (-23 / 12 : ℚ), 0, (-151 / 72 : ℚ), (1 / 36 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 6 : ℚ), 0, (-7 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 12 : ℚ)], ![(-5 / 4 : ℚ), (-1 / 24 : ℚ), (-41 / 12 : ℚ), (-7 / 12 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 17 : ℚ), (5 / 17 : ℚ), (3 / 17 : ℚ), (-9 / 17 : ℚ), (-9 / 17 : ℚ)], ![(-3 / 17 : ℚ), (1 / 17 : ℚ), 0, (9 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, (-5 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), -1, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 19 : ℚ), 0, 0, (-24 / 19 : ℚ)], ![0, (-8 / 19 : ℚ), (-12 / 19 : ℚ), 0, (12 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-36 / 7 : ℚ), (-20 / 7 : ℚ), (13 / 7 : ℚ), 0], ![(1 / 7 : ℚ), (-20 / 7 : ℚ), (-20 / 7 : ℚ), (-13 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, (-5 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), -1, (-5 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (3 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![(-2 / 5 : ℚ), 0, (-3 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), 0, 0, 0], ![0, (-2 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-4 / 17 : ℚ), (-3 / 34 : ℚ), (-6 / 17 : ℚ), 0], ![0, (-2 / 17 : ℚ), (-9 / 34 : ℚ), (3 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 15 : ℚ), 0, (1 / 5 : ℚ), (-8 / 15 : ℚ), (-4 / 5 : ℚ)], ![(-4 / 15 : ℚ), (-1 / 15 : ℚ), (1 / 15 : ℚ), (2 / 15 : ℚ), (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 8 : ℚ), (-25 / 6 : ℚ), (-17 / 8 : ℚ), (11 / 8 : ℚ), 0], ![(37 / 24 : ℚ), (-17 / 8 : ℚ), (-17 / 8 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, (-1 / 4 : ℚ), 0, -1], ![-1, 0, (-1 / 4 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-27 / 4 : ℚ)], ![(-3 / 8 : ℚ), (1 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-27 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, (1 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), (2 / 9 : ℚ), (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), 0, (-2 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (-24 / 5 : ℚ), (-13 / 5 : ℚ), (2 / 5 : ℚ), 0], ![(-1 / 10 : ℚ), (-13 / 5 : ℚ), (-13 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), 0, 0, (4 / 7 : ℚ), (-12 / 7 : ℚ)], ![(-6 / 7 : ℚ), 0, (-4 / 7 : ℚ), 0, (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-8 / 7 : ℚ)], ![0, (-4 / 7 : ℚ), (-6 / 7 : ℚ), (-6 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ)], ![(-3 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-14 / 3 : ℚ), -3, (-2 / 3 : ℚ), 0], ![(-2 / 3 : ℚ), (-7 / 3 : ℚ), -3, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 24 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ), (-5 / 12 : ℚ), (-7 / 24 : ℚ)], ![(-1 / 8 : ℚ), (1 / 24 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), -4, (-9 / 4 : ℚ), 0, 0], ![(1 / 8 : ℚ), -2, (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-37 / 68 : ℚ), (-36 / 17 : ℚ), (-3 / 68 : ℚ), (7 / 68 : ℚ), (25 / 68 : ℚ)], ![(37 / 68 : ℚ), (-75 / 68 : ℚ), 0, (-7 / 68 : ℚ), (3 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 0, (-5 / 4 : ℚ), -1, -1], ![(-1 / 12 : ℚ), 0, (-9 / 4 : ℚ), 1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 10 : ℚ), (-13 / 5 : ℚ), 0, (3 / 10 : ℚ), (3 / 10 : ℚ)], ![(3 / 5 : ℚ), (-13 / 10 : ℚ), (3 / 10 : ℚ), 0, (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 44 : ℚ), 0, (-51 / 44 : ℚ), (-13 / 44 : ℚ), 0], ![(-13 / 44 : ℚ), (-3 / 44 : ℚ), (-24 / 11 : ℚ), 0, (13 / 44 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), (1 / 4 : ℚ), (-7 / 4 : ℚ), (-3 / 4 : ℚ), (3 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, (-7 / 2 : ℚ), 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (-7 / 8 : ℚ), 0, 0, 0], ![(3 / 8 : ℚ), (-7 / 16 : ℚ), 0, (3 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (-13 / 17 : ℚ), 0, 0, (6 / 17 : ℚ)], ![(6 / 17 : ℚ), (-8 / 17 : ℚ), 0, (3 / 17 : ℚ), (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-217 / 136 : ℚ), (-287 / 68 : ℚ), (157 / 136 : ℚ), (193 / 136 : ℚ), (-3 / 68 : ℚ)], ![(217 / 136 : ℚ), (-293 / 136 : ℚ), (-157 / 136 : ℚ), (3 / 34 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), -6, 2, 2, 0], ![(5 / 2 : ℚ), -3, -2, 2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-8 / 3 : ℚ)], ![0, (-11 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-4 / 5 : ℚ), (7 / 5 : ℚ), (3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-7 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (-12 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 6 : ℚ), 0, (-13 / 48 : ℚ), (1 / 6 : ℚ), (-9 / 2 : ℚ)], ![(-5 / 6 : ℚ), (-1 / 12 : ℚ), (13 / 48 : ℚ), (1 / 2 : ℚ), (-53 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 5 : ℚ), 0, 0, (3 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(12 / 19 : ℚ), (20 / 19 : ℚ), 0, (12 / 19 : ℚ), (-48 / 19 : ℚ)], ![(-12 / 19 : ℚ), (4 / 19 : ℚ), 0, 0, (12 / 19 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, (-5 / 18 : ℚ), (7 / 18 : ℚ), (-40 / 9 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 9 : ℚ), (5 / 18 : ℚ), (7 / 18 : ℚ), (-40 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 17 : ℚ), 0, (-24 / 17 : ℚ), (-8 / 17 : ℚ)], ![0, (-4 / 17 : ℚ), 0, (12 / 17 : ℚ), (-4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), (-8 / 5 : ℚ), 0, (-18 / 5 : ℚ), (-18 / 5 : ℚ)], ![(3 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-9 / 5 : ℚ), (-33 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 17 : ℚ), 0, (-12 / 17 : ℚ), (-12 / 17 : ℚ)], ![0, (-4 / 17 : ℚ), 0, (6 / 17 : ℚ), (6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 6 : ℚ), -4, (7 / 6 : ℚ), 0, 0], ![(11 / 6 : ℚ), -2, (-7 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 12 : ℚ), (-7 / 8 : ℚ), 0, (-7 / 2 : ℚ), -2], ![(5 / 12 : ℚ), (-1 / 2 : ℚ), 0, (-55 / 16 : ℚ), (-15 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, -1, -1, -6], ![(-1 / 5 : ℚ), 0, 0, -1, -3]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), -2, 0, 0, (-29 / 10 : ℚ)], ![(3 / 10 : ℚ), -1, 0, 0, (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), 0, 0, (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-25 / 14 : ℚ), (-33 / 7 : ℚ), (25 / 14 : ℚ), 0, (-1 / 7 : ℚ)], ![(25 / 14 : ℚ), (-5 / 2 : ℚ), 0, (-25 / 14 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), 0, 0, (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 6 : ℚ), (-14 / 3 : ℚ), (11 / 6 : ℚ), (-11 / 6 : ℚ), 0], ![(11 / 6 : ℚ), (-5 / 2 : ℚ), 0, (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-4 / 17 : ℚ), (-6 / 17 : ℚ), (-6 / 17 : ℚ), 0], ![0, (-2 / 17 : ℚ), (3 / 17 : ℚ), (3 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-55 / 34 : ℚ), (-71 / 17 : ℚ), (23 / 17 : ℚ), 0, 0], ![(26 / 17 : ℚ), (-71 / 34 : ℚ), (3 / 34 : ℚ), 0, (3 / 68 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-103 / 34 : ℚ), -4, (43 / 34 : ℚ), 0, 0], ![(49 / 34 : ℚ), -2, (3 / 34 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 4 : ℚ), (-53 / 12 : ℚ), (3 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 12 : ℚ)], ![(5 / 3 : ℚ), (-9 / 4 : ℚ), (1 / 12 : ℚ), (5 / 24 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, 0, -1, -6], ![-1, 0, 1, -1, -3]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 0, 0, -1, (-19 / 4 : ℚ)], ![-1, 0, 1, -1, (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 1, -6], ![-2, 0, -1, 1, -3]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 4 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (1 / 12 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 9 : ℚ), 0, (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 26 : ℚ), (-56 / 13 : ℚ), (25 / 39 : ℚ), (-16 / 13 : ℚ), 0], ![(-1 / 26 : ℚ), (-29 / 13 : ℚ), (-71 / 78 : ℚ), (-16 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 27 : ℚ), 0, (4 / 9 : ℚ), (-40 / 27 : ℚ), (-16 / 27 : ℚ)], ![(-8 / 27 : ℚ), 0, (-28 / 27 : ℚ), (4 / 9 : ℚ), (-8 / 27 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(9 / 10 : ℚ), 0, (1 / 5 : ℚ), (-22 / 5 : ℚ), (-22 / 5 : ℚ)], ![(-11 / 10 : ℚ), 0, (1 / 2 : ℚ), (-11 / 5 : ℚ), (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 12 : ℚ), (-1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), -4, (2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), -2, (-7 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 121 : ℚ), (-532 / 121 : ℚ), (82 / 121 : ℚ), 0, (-32 / 121 : ℚ)], ![(-2 / 121 : ℚ), (-274 / 121 : ℚ), (-112 / 121 : ℚ), (8 / 121 : ℚ), (-16 / 121 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-16 / 21 : ℚ), (-2 / 7 : ℚ), (-8 / 7 : ℚ), 0], ![0, (-8 / 21 : ℚ), (-6 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (-13 / 3 : ℚ), (-25 / 6 : ℚ)], ![(-1 / 2 : ℚ), 0, (1 / 3 : ℚ), (-13 / 6 : ℚ), (-25 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (1 / 24 : ℚ), (-1 / 3 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 12 : ℚ), 0, (-1 / 24 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .yy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (1 / 3 : ℚ), -4, -4], ![(-5 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, -4]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, -1], ![0, -1, -1, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, (-3 / 8 : ℚ)], ![0, -1, -1, 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (-7 / 18 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), (-7 / 24 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-5 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (3 / 10 : ℚ), (3 / 10 : ℚ), 0, (-3 / 10 : ℚ)], ![(1 / 2 : ℚ), (-11 / 5 : ℚ), (-7 / 5 : ℚ), 1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 11 : ℚ), (6 / 11 : ℚ), (2 / 11 : ℚ), (5 / 11 : ℚ), 0], ![(17 / 11 : ℚ), (-46 / 11 : ℚ), (-23 / 11 : ℚ), (7 / 11 : ℚ), (32 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 11 : ℚ), (4 / 11 : ℚ), (-6 / 11 : ℚ), (-7 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ), (-2 / 11 : ℚ), (-5 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (12 / 25 : ℚ), (12 / 25 : ℚ), (12 / 25 : ℚ), (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-24 / 25 : ℚ), (-24 / 25 : ℚ), (-24 / 25 : ℚ), (-8 / 25 : ℚ)]] }
]

theorem conicDetC22B_checked : conicDetC22B.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
