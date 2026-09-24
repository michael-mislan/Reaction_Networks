import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC00 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![(1 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(1 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 3 : ℚ), (1 / 3 : ℚ), (-5 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, -1, (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 1, (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, 1, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, -1, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 10 : ℚ), 0], ![(1 / 10 : ℚ), (1 / 10 : ℚ), (-19 / 10 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-11 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 13 : ℚ), 0], ![(2 / 13 : ℚ), (2 / 13 : ℚ), (-24 / 13 : ℚ), (-4 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-11 / 6 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ)], ![(2 / 11 : ℚ), (2 / 11 : ℚ), (13 / 11 : ℚ), (2 / 11 : ℚ), (-40 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![0, 0, 1, (1 / 6 : ℚ), (-19 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-11 / 6 : ℚ), 0], ![(1 / 3 : ℚ), (1 / 3 : ℚ), (4 / 3 : ℚ), (-23 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0], ![(2 / 11 : ℚ), (2 / 11 : ℚ), (13 / 11 : ℚ), (-40 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![0, 0, 1, (-19 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 25 : ℚ), (-12 / 25 : ℚ), (-12 / 25 : ℚ), (-86 / 25 : ℚ), 0], ![0, 0, 2, (-184 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (-32 / 9 : ℚ), 0], ![(2 / 9 : ℚ), (2 / 9 : ℚ), (20 / 9 : ℚ), (-68 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-54 / 17 : ℚ), 0], ![0, 0, (30 / 17 : ℚ), (-116 / 17 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (7 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-19 / 11 : ℚ), 0], ![(4 / 11 : ℚ), (4 / 11 : ℚ), (15 / 11 : ℚ), (-21 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (7 / 6 : ℚ), (-5 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-30 / 11 : ℚ), 0], ![0, 0, 2, (-34 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (-28 / 9 : ℚ), 0], ![(2 / 9 : ℚ), (2 / 9 : ℚ), (20 / 9 : ℚ), (-32 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-1 / 4 : ℚ)], ![(1 / 12 : ℚ), (1 / 12 : ℚ), (13 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 4 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-5 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-15 / 11 : ℚ), 0], ![0, 0, 2, (-17 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (1 / 9 : ℚ), (19 / 9 : ℚ), (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), -2, (1 / 4 : ℚ), (-15 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 7 : ℚ), 0, 0], ![(2 / 7 : ℚ), (2 / 7 : ℚ), (-6 / 7 : ℚ), (-10 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), (2 / 3 : ℚ), (-4 / 3 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), -1, (-8 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), 0, (-2 / 3 : ℚ)], ![(1 / 6 : ℚ), (2 / 3 : ℚ), (-2 / 3 : ℚ), (1 / 6 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), 0], ![(-6 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), 0, 0, (-10 / 13 : ℚ)], ![(-6 / 13 : ℚ), (-6 / 13 : ℚ), (-2 / 13 : ℚ), (-2 / 13 : ℚ), (12 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), (-2 / 3 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (-3 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ)], ![(-6 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), (-4 / 13 : ℚ), 0, 0, (-24 / 13 : ℚ)], ![(-12 / 13 : ℚ), (-12 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-10 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, 0, (-28 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ)], ![(-3 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ), 0], ![(4 / 11 : ℚ), (4 / 11 : ℚ), (-10 / 11 : ℚ), (-10 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ), 0], ![0, 0, (-12 / 11 : ℚ), (-12 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), 0, 0, (-20 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (1 / 3 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, 0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), 0, (-1 / 5 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![0, 0, (-2 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, 0, 0], ![0, 0, -1, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-8 / 7 : ℚ), (-8 / 7 : ℚ), 0, (-8 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-17 / 11 : ℚ), (-8 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-32 / 11 : ℚ), (10 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-17 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-5 / 2 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 24 : ℚ), 0, (-9 / 8 : ℚ), (-35 / 24 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 24 : ℚ), (-53 / 24 : ℚ), (5 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-1 / 18 : ℚ), 0, (-7 / 6 : ℚ), (-7 / 9 : ℚ)], ![(-1 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 18 : ℚ), (-41 / 18 : ℚ), (55 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-8 / 11 : ℚ), (-2 / 11 : ℚ), 0], ![(4 / 11 : ℚ), (4 / 11 : ℚ), (-10 / 11 : ℚ), (-7 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (-1 / 22 : ℚ), 0, (-1 / 22 : ℚ), (-24 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 22 : ℚ), (-12 / 11 : ℚ), (-7 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), 0, (-2 / 9 : ℚ), (-28 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-2 / 9 : ℚ), (-13 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 12 : ℚ), 0, (-31 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 2 : ℚ), (-7 / 12 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, 0, (-5 / 8 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-9 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-8 / 11 : ℚ), (-8 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (10 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-8 / 11 : ℚ), 0, 0], ![(4 / 11 : ℚ), (4 / 11 : ℚ), (-10 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-2 / 5 : ℚ), 0, (1 / 2 : ℚ)], ![(1 / 5 : ℚ), (9 / 20 : ℚ), (-2 / 5 : ℚ), (1 / 10 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), 0, 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 3 : ℚ), (-7 / 12 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 3 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0, (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), -1, 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, 0, (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-8 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), 0, 0, (-20 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 5 : ℚ), 0], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-14 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-124 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-32 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (-18 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), 0], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 4 : ℚ), (-5 / 12 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 12 : ℚ), (-11 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)], ![(-6 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 7 : ℚ), (-3 / 7 : ℚ), 0, 0, -7], ![(-9 / 7 : ℚ), (-9 / 7 : ℚ), (-3 / 7 : ℚ), (-3 / 7 : ℚ), (-23 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 17 : ℚ), (-16 / 17 : ℚ), 0, 0, (-112 / 17 : ℚ)], ![(-48 / 17 : ℚ), (-48 / 17 : ℚ), 0, (-16 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), 0, 0, -6], ![(-12 / 7 : ℚ), (-12 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-40 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-6 / 5 : ℚ)], ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), 0, 0, (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (5 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-6 / 5 : ℚ), (-8 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, 0, -6], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, 0, (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, 0, 0, (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, 0, 0, (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-17 / 14 : ℚ), 0], ![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-16 / 7 : ℚ), (5 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 12 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 12 : ℚ), (-5 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-31 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (2 / 3 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 10 : ℚ), 0, (3 / 10 : ℚ)], ![(1 / 5 : ℚ), (7 / 20 : ℚ), 0, (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-55 / 12 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (2 / 3 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-3 / 4 : ℚ), (-4 / 3 : ℚ), (-1 / 12 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, 0, (-3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-62 / 17 : ℚ), 0, 0], ![(4 / 17 : ℚ), (4 / 17 : ℚ), (-33 / 17 : ℚ), (4 / 17 : ℚ), (-64 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-74 / 23 : ℚ), 0, 0], ![(12 / 23 : ℚ), (12 / 23 : ℚ), (-43 / 23 : ℚ), (12 / 23 : ℚ), (-80 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 8 : ℚ), 0, 0], ![(3 / 8 : ℚ), (3 / 8 : ℚ), (-3 / 4 : ℚ), (-21 / 16 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ), (-7 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-62 / 17 : ℚ), 0, 0], ![(4 / 17 : ℚ), (4 / 17 : ℚ), (-33 / 17 : ℚ), (-64 / 17 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), (1 / 3 : ℚ), -1, (-5 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-11 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), -3, (-23 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (-2 / 15 : ℚ), 0, (-8 / 15 : ℚ), 0], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 15 : ℚ), (2 / 15 : ℚ), (-2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), 0, (-20 / 13 : ℚ), 0], ![(-6 / 13 : ℚ), (-6 / 13 : ℚ), (-1 / 13 : ℚ), (-18 / 13 : ℚ), (-2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 37 : ℚ), (-6 / 37 : ℚ), 0, 0, (-30 / 37 : ℚ)], ![(-18 / 37 : ℚ), (-18 / 37 : ℚ), (-3 / 37 : ℚ), (-6 / 37 : ℚ), (36 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (-2 / 15 : ℚ), 0, 0, (-8 / 15 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 15 : ℚ), (-2 / 15 : ℚ), (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), 0, 0, (-20 / 13 : ℚ)], ![(-6 / 13 : ℚ), (-6 / 13 : ℚ), (-1 / 13 : ℚ), (-2 / 13 : ℚ), (-18 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0, -3], ![(-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, 0, (-28 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-12 / 11 : ℚ), (-2 / 11 : ℚ), (-4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 13 : ℚ), (-8 / 13 : ℚ), 0, 0, (-76 / 13 : ℚ)], ![(-24 / 13 : ℚ), (-24 / 13 : ℚ), (-4 / 13 : ℚ), (-8 / 13 : ℚ), (-72 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), 0, (-6 / 13 : ℚ), 0], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-1 / 13 : ℚ), (2 / 13 : ℚ), (-2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 31 : ℚ), (-6 / 31 : ℚ), 0, 0, (-24 / 31 : ℚ)], ![(-12 / 31 : ℚ), (-12 / 31 : ℚ), (-3 / 31 : ℚ), (-6 / 31 : ℚ), (30 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), 0, 0, (-6 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-1 / 13 : ℚ), (-2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-8 / 5 : ℚ), (-8 / 5 : ℚ), 0], ![0, 0, (-4 / 5 : ℚ), (-12 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-12 / 7 : ℚ), (-10 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (2 / 7 : ℚ), (-8 / 7 : ℚ), -2, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-12 / 13 : ℚ), 0, 0], ![(4 / 13 : ℚ), (4 / 13 : ℚ), (-7 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-8 / 11 : ℚ), 0, 0], ![(2 / 11 : ℚ), (2 / 11 : ℚ), (-5 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, 0, (-1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-4 / 11 : ℚ), (-6 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-6 / 25 : ℚ), 0, (-46 / 25 : ℚ), (-18 / 25 : ℚ)], ![(-6 / 25 : ℚ), (-6 / 25 : ℚ), (-3 / 25 : ℚ), (-8 / 5 : ℚ), (24 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 13 : ℚ), (-1 / 13 : ℚ), 0, (-33 / 26 : ℚ), (-2 / 13 : ℚ)], ![(-1 / 13 : ℚ), (-1 / 13 : ℚ), (-1 / 26 : ℚ), (-31 / 26 : ℚ), (3 / 26 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-27 / 10 : ℚ), 0, 0], ![(1 / 10 : ℚ), (1 / 10 : ℚ), (-7 / 5 : ℚ), (1 / 10 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-1 / 9 : ℚ), 0, (-25 / 18 : ℚ), (-14 / 9 : ℚ)], ![(-1 / 9 : ℚ), (-1 / 9 : ℚ), (-1 / 18 : ℚ), (-23 / 18 : ℚ), (10 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-6 / 25 : ℚ), 0, (-32 / 25 : ℚ), (-18 / 25 : ℚ)], ![(-6 / 25 : ℚ), (-6 / 25 : ℚ), (-3 / 25 : ℚ), (-58 / 25 : ℚ), (24 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-40 / 33 : ℚ), (-4 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (-74 / 33 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-23 / 8 : ℚ), 0, 0], ![(3 / 8 : ℚ), (3 / 8 : ℚ), (-13 / 8 : ℚ), (3 / 8 : ℚ), (-5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 16 : ℚ), (-3 / 16 : ℚ), 0, (-39 / 32 : ℚ), (-23 / 12 : ℚ)], ![(-3 / 16 : ℚ), (-3 / 16 : ℚ), (-3 / 32 : ℚ), (-9 / 4 : ℚ), (41 / 48 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-6 / 25 : ℚ), (-36 / 25 : ℚ), (-6 / 25 : ℚ), 0], ![(12 / 25 : ℚ), (12 / 25 : ℚ), (-21 / 25 : ℚ), (-13 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-1 / 11 : ℚ), 0, (-1 / 11 : ℚ), (-2 / 11 : ℚ)], ![(-1 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 22 : ℚ), (-12 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-2 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-1 / 7 : ℚ), (-9 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, 0], ![0, 0, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 12 : ℚ), (-4 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-1 / 16 : ℚ), 0, (-3 / 16 : ℚ), (-1 / 8 : ℚ)], ![(-1 / 16 : ℚ), (-1 / 16 : ℚ), 0, (1 / 4 : ℚ), (-1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-6 / 25 : ℚ), 0, (-18 / 25 : ℚ), (-18 / 25 : ℚ)], ![(-6 / 25 : ℚ), (-6 / 25 : ℚ), (-3 / 25 : ℚ), (24 / 25 : ℚ), (6 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-6 / 25 : ℚ), 0, (-18 / 25 : ℚ), (-118 / 25 : ℚ)], ![(-6 / 25 : ℚ), (-6 / 25 : ℚ), (-3 / 25 : ℚ), (24 / 25 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0], ![0, 0, (-1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-4 / 11 : ℚ), (-6 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-4 / 11 : ℚ), (-50 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (2 / 11 : ℚ), (-49 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), (1 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), (1 / 3 : ℚ), -1, 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-26 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), 0, 0, (-20 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-2 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, (1 / 3 : ℚ), -4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, (1 / 3 : ℚ), 4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, (-1 / 3 : ℚ), 4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 0, (-1 / 3 : ℚ), -4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-56 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-76 / 17 : ℚ), (-24 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), 0, (-44 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-24 / 5 : ℚ), (-12 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-25 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-32 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-44 / 9 : ℚ), 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 12 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ)], ![0, (12 / 11 : ℚ), (4 / 11 : ℚ), (-28 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-1 / 16 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 16 : ℚ)], ![(-3 / 16 : ℚ), (-3 / 16 : ℚ), (13 / 16 : ℚ), (-1 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), 0, 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (-1 / 14 : ℚ), (-2 / 7 : ℚ), 0, 0], ![(-3 / 14 : ℚ), (-3 / 14 : ℚ), (1 / 14 : ℚ), (-3 / 2 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-16 / 11 : ℚ), 0, (-24 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-12 / 11 : ℚ), (4 / 11 : ℚ), (-4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-18 / 11 : ℚ), (2 / 11 : ℚ), (-32 / 11 : ℚ)], ![(-14 / 11 : ℚ), (-16 / 11 : ℚ), (4 / 11 : ℚ), 0, (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-16 / 11 : ℚ), 0, (-20 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-12 / 11 : ℚ), (4 / 11 : ℚ), (-4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-5 / 4 : ℚ)], ![(-3 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 6 : ℚ)], ![0, 0, (1 / 6 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-3 / 8 : ℚ), 0, (-3 / 8 : ℚ)], ![(-3 / 8 : ℚ), (-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), 0, (2 / 3 : ℚ)], ![-1, (-5 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, -1, 0], ![0, 0, (1 / 3 : ℚ), (-7 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-7 / 4 : ℚ)], ![(-3 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-5 / 6 : ℚ), 0], ![(-1 / 6 : ℚ), (2 / 3 : ℚ), (1 / 6 : ℚ), -2, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (-6 / 17 : ℚ), (-12 / 17 : ℚ), 0, (-30 / 17 : ℚ)], ![(-18 / 17 : ℚ), (-18 / 17 : ℚ), (-24 / 17 : ℚ), 0, (36 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, (-16 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-6 / 7 : ℚ)], ![(-6 / 7 : ℚ), (-6 / 7 : ℚ), (-8 / 7 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-2 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, 0, -3], ![(-3 / 2 : ℚ), (-3 / 2 : ℚ), -2, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, 0, (-7 / 2 : ℚ)], ![(-3 / 2 : ℚ), (-3 / 2 : ℚ), -2, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), 0], ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-11 / 6 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), 2]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ)], ![(-6 / 11 : ℚ), (-6 / 11 : ℚ), (-28 / 11 : ℚ), (-2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), (-4 / 15 : ℚ), (-4 / 15 : ℚ), 0, (-28 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-14 / 5 : ℚ), (-4 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), 0, (-64 / 9 : ℚ)], ![(-4 / 3 : ℚ), (-4 / 3 : ℚ), (-10 / 3 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 17 : ℚ), (-2 / 17 : ℚ), (-2 / 17 : ℚ), 0, (-78 / 17 : ℚ)], ![(-6 / 17 : ℚ), (-6 / 17 : ℚ), (-40 / 17 : ℚ), (-2 / 17 : ℚ), (-26 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-6 / 7 : ℚ), 0], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-1 / 18 : ℚ), 0, (-23 / 18 : ℚ), (-5 / 9 : ℚ)], ![(-1 / 18 : ℚ), (-1 / 18 : ℚ), (-13 / 9 : ℚ), (-47 / 18 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-6 / 25 : ℚ), 0, (-116 / 75 : ℚ), (-326 / 75 : ℚ)], ![(-6 / 25 : ℚ), (-6 / 25 : ℚ), (-68 / 75 : ℚ), (-10 / 3 : ℚ), (-154 / 75 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (22 / 9 : ℚ), (4 / 9 : ℚ), (-68 / 9 : ℚ)], ![(-10 / 3 : ℚ), (-52 / 9 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 6 : ℚ), (-31 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-7 / 3 : ℚ), -2, -5]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0], ![(2 / 3 : ℚ), (2 / 3 : ℚ), (-11 / 3 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-7 / 3 : ℚ)], ![-1, -1, (-1 / 3 : ℚ), 2, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-5 / 3 : ℚ)], ![-1, -1, (-1 / 3 : ℚ), 2, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, (-16 / 11 : ℚ), (-24 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-14 / 11 : ℚ), (-2 / 11 : ℚ), 0], ![(2 / 11 : ℚ), (2 / 11 : ℚ), (-32 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, (-16 / 11 : ℚ), (-20 / 11 : ℚ)], ![(-12 / 11 : ℚ), (-12 / 11 : ℚ), (-4 / 11 : ℚ), (4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), -1, 0, 0], ![0, 0, (-7 / 3 : ℚ), (1 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), -1, 0, (-1 / 3 : ℚ)], ![0, 0, (-7 / 3 : ℚ), (1 / 3 : ℚ), (10 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-3 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), 0, 0], ![(2 / 5 : ℚ), (2 / 5 : ℚ), (-16 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, (2 / 11 : ℚ), (-12 / 11 : ℚ)], ![(-6 / 11 : ℚ), (-8 / 11 : ℚ), (-29 / 22 : ℚ), (-1 / 2 : ℚ), (-5 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), 0, 0, (-14 / 11 : ℚ)], ![(-6 / 11 : ℚ), (-6 / 11 : ℚ), -1, (-13 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 6 : ℚ), (-1 / 2 : ℚ), 0], ![(-1 / 6 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 2 : ℚ), 0, (-2 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (1 / 3 : ℚ), (-2 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xx), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0], ![0, 0, 1, (-1 / 2 : ℚ), 0]] }
]

theorem conicDetC00_checked : conicDetC00.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
