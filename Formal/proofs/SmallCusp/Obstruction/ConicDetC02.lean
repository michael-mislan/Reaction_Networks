import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC02 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-44 / 9 : ℚ), 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-3 / 2 : ℚ)], ![0, 0, (-3 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ)], ![(1 / 4 : ℚ), 0, -2, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-14 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, (-14 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 29 : ℚ), (-44 / 29 : ℚ), (-43 / 29 : ℚ), 0, 0], ![0, (-2 / 29 : ℚ), (-88 / 29 : ℚ), (11 / 29 : ℚ), (38 / 29 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, -1, (-5 / 3 : ℚ)], ![-1, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 13 : ℚ), (-14 / 13 : ℚ), 0, 0], ![(6 / 13 : ℚ), (-8 / 13 : ℚ), (-36 / 13 : ℚ), (-22 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, 0, 2, -6], ![(-10 / 3 : ℚ), (-8 / 3 : ℚ), (-2 / 3 : ℚ), 2, -6]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .y), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), 0], ![0, 0, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (-7 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 7 : ℚ), 0, 0, 0], ![(2 / 7 : ℚ), (4 / 7 : ℚ), (-12 / 7 : ℚ), (-20 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 3 : ℚ), (-1 / 2 : ℚ), (-5 / 3 : ℚ), (-8 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ)], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 10 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(1 / 10 : ℚ), (1 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 10 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), (-5 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 16 : ℚ), 0, (-5 / 16 : ℚ), (-1 / 16 : ℚ)], ![0, (1 / 2 : ℚ), (-5 / 8 : ℚ), (3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 8 : ℚ), (3 / 8 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0], ![(1 / 10 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![0, (-1 / 4 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ), 0, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 7 : ℚ), 0, 0, 0], ![(2 / 7 : ℚ), (4 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 3 : ℚ), 0, (-5 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 1, -1], ![-1, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 7 : ℚ), 0, 0, 0], ![0, (1 / 7 : ℚ), -1, (-3 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 13 : ℚ), 0, 0, (-14 / 13 : ℚ)], ![(-4 / 13 : ℚ), 0, (-17 / 13 : ℚ), (-4 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), (-3 / 4 : ℚ), 0, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (3 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (3 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, 0, 0], ![(1 / 8 : ℚ), (5 / 8 : ℚ), (-7 / 8 : ℚ), (1 / 8 : ℚ), (15 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-23 / 16 : ℚ), 0, (11 / 16 : ℚ), 0], ![(13 / 16 : ℚ), (21 / 16 : ℚ), (-25 / 16 : ℚ), (13 / 16 : ℚ), (5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 7 : ℚ), 0, 0, 0], ![(2 / 7 : ℚ), (4 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (2 / 3 : ℚ), (4 / 3 : ℚ), (1 / 3 : ℚ), (-11 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (5 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (2 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-10 / 3 : ℚ), 0, 0, 0], ![(4 / 9 : ℚ), (8 / 9 : ℚ), (22 / 9 : ℚ), (-68 / 9 : ℚ), (8 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-37 / 44 : ℚ), (-15 / 44 : ℚ), 0, (-41 / 22 : ℚ)], ![(1 / 11 : ℚ), (2 / 11 : ℚ), (12 / 11 : ℚ), (1 / 11 : ℚ), (-42 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 21 : ℚ), (-1 / 7 : ℚ), (-11 / 21 : ℚ), 0, (-12 / 7 : ℚ)], ![(1 / 7 : ℚ), (1 / 21 : ℚ), (4 / 7 : ℚ), (2 / 21 : ℚ), (-74 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-23 / 17 : ℚ), (-3 / 17 : ℚ), (-32 / 17 : ℚ), 0], ![(6 / 17 : ℚ), (23 / 17 : ℚ), (23 / 17 : ℚ), (-67 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 22 : ℚ), (-59 / 88 : ℚ), (-37 / 88 : ℚ), (-85 / 44 : ℚ), 0], ![(1 / 22 : ℚ), (1 / 11 : ℚ), (23 / 22 : ℚ), (-43 / 11 : ℚ), (1 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 21 : ℚ), 0, (-11 / 21 : ℚ), (-11 / 7 : ℚ), (-1 / 7 : ℚ)], ![0, (-2 / 21 : ℚ), (3 / 7 : ℚ), (-68 / 21 : ℚ), (-1 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), 0, (-68 / 75 : ℚ), (-68 / 25 : ℚ), -2], ![0, (-6 / 25 : ℚ), (2 / 3 : ℚ), (-142 / 25 : ℚ), (-22 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-29 / 18 : ℚ), (-13 / 18 : ℚ), (-34 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (2 / 9 : ℚ), (19 / 9 : ℚ), (-70 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 57 : ℚ), 0, (-62 / 57 : ℚ), (-62 / 19 : ℚ), (-28 / 57 : ℚ)], ![(-22 / 57 : ℚ), (-16 / 57 : ℚ), (46 / 57 : ℚ), (-388 / 57 : ℚ), (-20 / 57 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-7 / 24 : ℚ), (-19 / 24 : ℚ), 0, (-15 / 8 : ℚ)], ![(1 / 24 : ℚ), (1 / 12 : ℚ), (25 / 24 : ℚ), (1 / 24 : ℚ), (-23 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-6 / 5 : ℚ), (-1 / 10 : ℚ), (-7 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), (6 / 5 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-7 / 24 : ℚ), (-19 / 24 : ℚ), (-15 / 8 : ℚ), 0], ![(1 / 24 : ℚ), (1 / 12 : ℚ), (25 / 24 : ℚ), (-23 / 12 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 23 : ℚ), 0, (-32 / 23 : ℚ), (-64 / 23 : ℚ), (-14 / 23 : ℚ)], ![(-7 / 23 : ℚ), (-6 / 23 : ℚ), (26 / 23 : ℚ), (-70 / 23 : ℚ), (-4 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-5 / 9 : ℚ), (-29 / 18 : ℚ), (-34 / 9 : ℚ), 0], ![(1 / 18 : ℚ), (1 / 9 : ℚ), (37 / 18 : ℚ), (-35 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 3 : ℚ), (2 / 3 : ℚ), 1, (1 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 15 : ℚ), (-7 / 15 : ℚ), (-2 / 3 : ℚ), 0, (-4 / 5 : ℚ)], ![(1 / 15 : ℚ), (2 / 15 : ℚ), (16 / 15 : ℚ), (1 / 15 : ℚ), (-13 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-1 / 10 : ℚ), 0, (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), 0, (-11 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), 2, -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 46 : ℚ), (-7 / 92 : ℚ), (-31 / 23 : ℚ), (-163 / 92 : ℚ), 0], ![0, (1 / 92 : ℚ), (125 / 92 : ℚ), (-169 / 92 : ℚ), (3 / 92 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-14 / 9 : ℚ), (-11 / 18 : ℚ), (-16 / 9 : ℚ), 0], ![(1 / 18 : ℚ), (1 / 9 : ℚ), (37 / 18 : ℚ), (-17 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 3 : ℚ), 0, 0], ![(1 / 6 : ℚ), (1 / 3 : ℚ), (-2 / 3 : ℚ), (1 / 6 : ℚ), (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), 0], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-13 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 3 : ℚ), 0, 0], ![(1 / 6 : ℚ), (1 / 3 : ℚ), (-2 / 3 : ℚ), (-7 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), -1, (-8 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 17 : ℚ), 0, (3 / 17 : ℚ), (-9 / 17 : ℚ), (1 / 17 : ℚ)], ![(-7 / 17 : ℚ), (-3 / 17 : ℚ), (-2 / 17 : ℚ), (4 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), 0, (-1 / 10 : ℚ), (-3 / 20 : ℚ), (-1 / 10 : ℚ)], ![0, 0, (-3 / 20 : ℚ), (-7 / 20 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (-2 / 15 : ℚ), (-1 / 15 : ℚ), 0, (-8 / 15 : ℚ)], ![(-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-2 / 5 : ℚ), (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), -1, (-1 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, 0, (1 / 13 : ℚ), (-14 / 13 : ℚ)], ![(-7 / 13 : ℚ), (-3 / 13 : ℚ), (-2 / 13 : ℚ), 0, (6 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-6 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, 0, (-6 / 5 : ℚ), (-14 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, (-1 / 2 : ℚ)], ![(-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-5 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 8 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, 0, (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, 0, -1], ![(-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, 0, (-6 / 5 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ)], ![0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (-3 / 7 : ℚ), (1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 14 : ℚ), 0, (-17 / 28 : ℚ), 0], ![(-1 / 7 : ℚ), (-1 / 14 : ℚ), 0, (11 / 28 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 3 : ℚ), 0, 0], ![(1 / 6 : ℚ), (1 / 3 : ℚ), (-2 / 3 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (-3 / 7 : ℚ), (1 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-3 / 14 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), 0], ![0, 0, (-3 / 7 : ℚ), (1 / 7 : ℚ), (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 12 : ℚ), (-5 / 12 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, (-2 / 7 : ℚ), (-3 / 7 : ℚ), (-3 / 14 : ℚ)], ![0, (-1 / 7 : ℚ), (-2 / 7 : ℚ), (1 / 7 : ℚ), (-3 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (1 / 3 : ℚ), 0, (-4 / 9 : ℚ), (-8 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-1 / 3 : ℚ), 0, (-4 / 9 : ℚ), (8 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-3 / 10 : ℚ), (-3 / 10 : ℚ), 0, 0], ![(1 / 10 : ℚ), (1 / 5 : ℚ), (-3 / 10 : ℚ), 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![(2 / 5 : ℚ), 0, (-6 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), -3, (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 12 : ℚ), 0, (-3 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-17 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 10 : ℚ), (1 / 20 : ℚ), (-6 / 5 : ℚ), 0], ![(-7 / 20 : ℚ), (-7 / 20 : ℚ), 0, (-47 / 20 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 48 : ℚ), 0, (-9 / 8 : ℚ), (-35 / 24 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 48 : ℚ), (-1 / 24 : ℚ), (-53 / 24 : ℚ), (5 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 29 : ℚ), (-2 / 29 : ℚ), 0, (-41 / 29 : ℚ), (-56 / 29 : ℚ)], ![(-8 / 29 : ℚ), (-2 / 29 : ℚ), (-4 / 29 : ℚ), (-78 / 29 : ℚ), (48 / 29 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, 0, (-1 / 10 : ℚ), (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-1 / 10 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), 0, 0, (-1 / 11 : ℚ), (-26 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-1 / 11 : ℚ), (-13 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, 0, (-2 / 9 : ℚ), (-28 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ), (-13 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (1 / 6 : ℚ), 1, -1], ![-1, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 6 : ℚ), (-2 / 3 : ℚ), (-1 / 4 : ℚ), (-1 / 12 : ℚ)], ![(1 / 6 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (4 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, (-4 / 5 : ℚ), -1], ![(-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (4 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, (-1 / 9 : ℚ), (-7 / 9 : ℚ), (-4 / 9 : ℚ)], ![(-1 / 3 : ℚ), 0, (-1 / 9 : ℚ), (7 / 9 : ℚ), (-4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 8 : ℚ), (-7 / 24 : ℚ)], ![0, (-1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (-3 / 7 : ℚ), (1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (-13 / 10 : ℚ)], ![(-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, (7 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 4 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 4 : ℚ), 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, -1, 0, 0], ![(1 / 2 : ℚ), (1 / 2 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, 0, (-8 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), -1, -1, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0], ![0, 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-8 / 5 : ℚ), 0], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-14 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-124 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), (-3 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-32 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-2 / 3 : ℚ), -1], ![0, (-1 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, 0, (-17 / 11 : ℚ), (1 / 11 : ℚ)], ![(-7 / 11 : ℚ), (-3 / 11 : ℚ), (-2 / 11 : ℚ), (-15 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, 0, 0, (-5 / 7 : ℚ)], ![(-3 / 7 : ℚ), 0, (-1 / 7 : ℚ), (-1 / 7 : ℚ), (5 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, 0, (-14 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-12 / 25 : ℚ), (2 / 25 : ℚ), 0, (6 / 25 : ℚ), (-184 / 25 : ℚ)], ![(-42 / 25 : ℚ), (-14 / 25 : ℚ), (-12 / 25 : ℚ), 0, (-86 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-16 / 17 : ℚ), (-16 / 17 : ℚ), (-16 / 17 : ℚ), (-48 / 17 : ℚ), (-16 / 17 : ℚ)], ![0, 0, 0, (-112 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, 0, (-58 / 11 : ℚ)], ![(-12 / 11 : ℚ), 0, (-4 / 11 : ℚ), (-12 / 11 : ℚ), (-56 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, 0, 0, 0, (-6 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (3 / 10 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ), (-1 / 2 : ℚ)], ![(-3 / 10 : ℚ), (-3 / 10 : ℚ), (-1 / 10 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (-8 / 5 : ℚ)], ![(-6 / 5 : ℚ), (-4 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, 0, -6], ![(-4 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-20 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ)], ![0, 0, 0, (-3 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ)], ![0, 0, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 2 : ℚ), 0, (-5 / 6 : ℚ), (1 / 6 : ℚ)], ![(-1 / 2 : ℚ), (-2 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-7 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (-23 / 20 : ℚ), 0], ![(-3 / 10 : ℚ), (-3 / 10 : ℚ), (-1 / 20 : ℚ), (-11 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 5 : ℚ), (-3 / 10 : ℚ), -1, 0], ![(1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 10 : ℚ), (-19 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 16 : ℚ), 0, (-19 / 16 : ℚ), 0], ![(-9 / 16 : ℚ), (-9 / 16 : ℚ), (-1 / 8 : ℚ), (-9 / 4 : ℚ), (5 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, 0, (-1 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), 0, (-1 / 10 : ℚ), (-11 / 10 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), 0, 0, (-11 / 17 : ℚ), (-89 / 17 : ℚ)], ![(-3 / 17 : ℚ), 0, (-3 / 17 : ℚ), (11 / 17 : ℚ), (-43 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![0, 0, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, 0, (-3 / 5 : ℚ), (-47 / 10 : ℚ)], ![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (3 / 5 : ℚ), (-23 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-47 / 10 : ℚ)], ![(-3 / 5 : ℚ), (-3 / 5 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ), (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ)], ![0, 0, 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-59 / 13 : ℚ)], ![(-17 / 26 : ℚ), (-17 / 26 : ℚ), (-2 / 13 : ℚ), (9 / 26 : ℚ), (-58 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (13 / 24 : ℚ), 0, (7 / 12 : ℚ), (-55 / 12 : ℚ)], ![(-3 / 4 : ℚ), (-5 / 8 : ℚ), (-1 / 12 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ)], ![0, 0, 0, (-3 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-6 / 13 : ℚ), 0], ![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-1 / 13 : ℚ), (2 / 13 : ℚ), (-2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-16 / 9 : ℚ), 0], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-1 / 9 : ℚ), (-14 / 9 : ℚ), (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-20 / 13 : ℚ), 0], ![(-6 / 13 : ℚ), (-6 / 13 : ℚ), (-3 / 13 : ℚ), (-34 / 13 : ℚ), (-6 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 16 : ℚ), 0, 0, (-9 / 16 : ℚ)], ![(-3 / 16 : ℚ), (3 / 16 : ℚ), (-15 / 16 : ℚ), (-3 / 4 : ℚ), (9 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-1 / 13 : ℚ), (-2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 9 : ℚ)], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-1 / 9 : ℚ), (-2 / 9 : ℚ), (-14 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![-1, -1, 0, -1, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 7 : ℚ), (-12 / 7 : ℚ), 0, 0], ![(4 / 7 : ℚ), (4 / 7 : ℚ), (-8 / 7 : ℚ), (-20 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-8 / 9 : ℚ), (-56 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-1 / 9 : ℚ), 0, (-4 / 9 : ℚ), 0], ![(-1 / 3 : ℚ), 0, (-2 / 9 : ℚ), (1 / 9 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, 0, (-20 / 13 : ℚ), 0], ![(-6 / 13 : ℚ), (-2 / 13 : ℚ), (-1 / 13 : ℚ), (-18 / 13 : ℚ), (-2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, (-2 / 7 : ℚ), (-3 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (-3 / 14 : ℚ), -1, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-3 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), 0], ![(1 / 7 : ℚ), (2 / 7 : ℚ), (-4 / 7 : ℚ), (-9 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, 0, 0, (-20 / 13 : ℚ)], ![(-6 / 13 : ℚ), (-2 / 13 : ℚ), (-1 / 13 : ℚ), (-2 / 13 : ℚ), (-18 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 12 : ℚ), 0, 0, (-3 / 2 : ℚ)], ![(-3 / 4 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-6 / 7 : ℚ), (-8 / 7 : ℚ), (-12 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, (2 / 7 : ℚ), (-6 / 7 : ℚ), -4, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 13 : ℚ), 0, 0, 0, (-76 / 13 : ℚ)], ![(-24 / 13 : ℚ), (-8 / 13 : ℚ), (-4 / 13 : ℚ), (-8 / 13 : ℚ), (-72 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (1 / 5 : ℚ), (2 / 15 : ℚ), (-3 / 5 : ℚ), (-1 / 15 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 3 : ℚ), 0, (2 / 15 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (1 / 42 : ℚ), 0, (-1 / 7 : ℚ), (-3 / 7 : ℚ)], ![(-1 / 7 : ℚ), (-1 / 42 : ℚ), (-1 / 14 : ℚ), (-2 / 7 : ℚ), (3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (1 / 6 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 2, (8 / 3 : ℚ), (2 / 3 : ℚ), (-16 / 3 : ℚ)], ![-2, (-8 / 3 : ℚ), (4 / 3 : ℚ), 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), -1, -1, -1], ![0, 0, (-3 / 4 : ℚ), (-3 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ)], ![0, 0, (-3 / 13 : ℚ), (2 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ)], ![0, 0, (-3 / 13 : ℚ), (2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-5 / 6 : ℚ), 0, 0], ![(1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (-3 / 14 : ℚ), (1 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-1 / 17 : ℚ), 0, (-8 / 17 : ℚ), (-6 / 17 : ℚ)], ![(-3 / 17 : ℚ), (-2 / 17 : ℚ), 0, (3 / 17 : ℚ), (-3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-1 / 2 : ℚ), (-2 / 3 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 6 : ℚ), 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-5 / 32 : ℚ), (-7 / 16 : ℚ), -1, 0], ![(5 / 32 : ℚ), (5 / 32 : ℚ), (-1 / 4 : ℚ), (-15 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 12 : ℚ), 0, (-19 / 12 : ℚ), (-5 / 12 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (-17 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (11 / 40 : ℚ), 0, (-47 / 40 : ℚ), 0], ![(-13 / 40 : ℚ), (-13 / 40 : ℚ), (-1 / 40 : ℚ), (-9 / 8 : ℚ), (9 / 40 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (1 / 12 : ℚ), (1 / 18 : ℚ), (-11 / 9 : ℚ), (-23 / 6 : ℚ)], ![(-1 / 12 : ℚ), (-67 / 36 : ℚ), 0, (-7 / 6 : ℚ), (1 / 18 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, (-2 / 7 : ℚ), (-43 / 42 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (-3 / 14 : ℚ), (-40 / 21 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (2 / 15 : ℚ), 0, (-52 / 45 : ℚ), (-8 / 15 : ℚ)], ![(-2 / 15 : ℚ), (-4 / 15 : ℚ), (-1 / 15 : ℚ), (-98 / 45 : ℚ), (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (19 / 48 : ℚ), 0, (-55 / 48 : ℚ), 0], ![(-25 / 48 : ℚ), (-25 / 48 : ℚ), (-1 / 16 : ℚ), (-13 / 6 : ℚ), (13 / 48 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 16 : ℚ), 0, 0, (-39 / 32 : ℚ), (-23 / 12 : ℚ)], ![(-3 / 16 : ℚ), (-3 / 16 : ℚ), (-3 / 32 : ℚ), (-9 / 4 : ℚ), (41 / 48 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 11 : ℚ), 0, 0, (-3 / 11 : ℚ), (-9 / 11 : ℚ)], ![(-3 / 11 : ℚ), 0, (-3 / 11 : ℚ), (-14 / 11 : ℚ), (9 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), 0, (-1 / 7 : ℚ), (-2 / 7 : ℚ)], ![(-1 / 7 : ℚ), 0, (-2 / 7 : ℚ), (-8 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, 0, (-2 / 7 : ℚ), (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-1 / 7 : ℚ), (-9 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (1 / 3 : ℚ), 1, -1], ![-1, -1, 0, 0, 0]] }
]

theorem conicDetC02_checked : conicDetC02.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
