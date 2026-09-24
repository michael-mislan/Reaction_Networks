import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC03 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (1 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), 0, (-3 / 5 : ℚ), (-3 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, 0, (-3 / 10 : ℚ), (3 / 5 : ℚ), (-1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, 0, (-3 / 7 : ℚ), (4 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (1 / 21 : ℚ), 0, (-6 / 7 : ℚ), (-34 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-1 / 21 : ℚ), (-1 / 7 : ℚ), (6 / 7 : ℚ), (-33 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-9 / 17 : ℚ), (-16 / 17 : ℚ), 0, 0], ![(3 / 17 : ℚ), (6 / 17 : ℚ), (-8 / 17 : ℚ), (3 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), (1 / 5 : ℚ), (2 / 15 : ℚ), (-3 / 5 : ℚ), (-14 / 15 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 3 : ℚ), 0, (2 / 15 : ℚ), (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (1 / 2 : ℚ), (1 / 12 : ℚ), (-3 / 4 : ℚ), (-13 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-7 / 12 : ℚ), 0, (1 / 12 : ℚ), (-103 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 7 : ℚ), (-12 / 7 : ℚ), 0, 0], ![(4 / 7 : ℚ), (4 / 7 : ℚ), (-8 / 7 : ℚ), (-12 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 5 : ℚ), 0, 0, (-23 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, 0, 0, (-8 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-2 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (-1 / 2 : ℚ), -1, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (4 / 3 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![0, 0, (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(1 / 5 : ℚ), (7 / 5 : ℚ), (6 / 5 : ℚ), (-17 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 8 : ℚ), 0, (3 / 8 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (-13 / 4 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (-7 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (-7 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 8 : ℚ), (-3 / 8 : ℚ), 0, 0], ![(1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 4 : ℚ), -1, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (4 / 3 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-5 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)], ![(-1 / 2 : ℚ), -1, (-1 / 2 : ℚ), -3, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), 0, (2 / 3 : ℚ), (-10 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), 0, (2 / 3 : ℚ), (-10 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (4 / 3 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (-1 / 6 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ), (-10 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), 0, (2 / 3 : ℚ), (-10 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (4 / 3 : ℚ), 0, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, (-7 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), (2 / 3 : ℚ), 0, (-10 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 0, 0], ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), -4, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), (-5 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![-1, -1, -1, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 7 : ℚ), 0, (-3 / 7 : ℚ)], ![(-3 / 7 : ℚ), (-2 / 7 : ℚ), (-3 / 7 : ℚ), (-22 / 7 : ℚ), (-1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-28 / 17 : ℚ), (-28 / 17 : ℚ), 0, 0], ![(20 / 17 : ℚ), 0, (-8 / 17 : ℚ), (-132 / 17 : ℚ), (4 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), 0, (-44 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 5 : ℚ), (-7 / 5 : ℚ), 0, 0], ![(3 / 5 : ℚ), (3 / 5 : ℚ), (-4 / 5 : ℚ), (-38 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, (2 / 3 : ℚ), -2, (2 / 3 : ℚ), 2]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, (-1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (1 / 2 : ℚ), (-4 / 3 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), -2], ![(-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), (4 / 3 : ℚ), (4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 32 : ℚ), 0, (-3 / 32 : ℚ), 0], ![(1 / 32 : ℚ), (1 / 32 : ℚ), (-1 / 4 : ℚ), (1 / 16 : ℚ), (1 / 32 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), 0, (-7 / 8 : ℚ), (-5 / 4 : ℚ)], ![(-3 / 8 : ℚ), (-3 / 8 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 6 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (7 / 12 : ℚ), (-23 / 12 : ℚ), (1 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, (-1 / 6 : ℚ), (-2 / 3 : ℚ)], ![0, (3 / 2 : ℚ), (-7 / 2 : ℚ), 0, (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, 0], ![(2 / 3 : ℚ), 0, (-10 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 3 : ℚ), 0, (-8 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 3 : ℚ), (-1 / 2 : ℚ), (-8 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-25 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-17 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-44 / 9 : ℚ), 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), 0, (-8 / 13 : ℚ), (-12 / 13 : ℚ), (-8 / 13 : ℚ)], ![0, 0, (4 / 13 : ℚ), (-28 / 13 : ℚ), (8 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), 0, (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, (-4 / 15 : ℚ), (4 / 15 : ℚ), (-28 / 15 : ℚ), (4 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-13 / 10 : ℚ), 0, (-11 / 10 : ℚ), (-1 / 10 : ℚ)], ![(1 / 10 : ℚ), (6 / 5 : ℚ), (11 / 10 : ℚ), (-14 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), 0, (-11 / 12 : ℚ), 0, (19 / 24 : ℚ)], ![(-7 / 8 : ℚ), (-5 / 6 : ℚ), (1 / 24 : ℚ), (-11 / 24 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-8 / 13 : ℚ), (-12 / 13 : ℚ), (-4 / 13 : ℚ)], ![0, 0, (4 / 13 : ℚ), (-28 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-8 / 13 : ℚ), (-12 / 13 : ℚ), (-8 / 13 : ℚ)], ![0, 0, (4 / 13 : ℚ), (-28 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-16 / 13 : ℚ), 0, (-20 / 13 : ℚ)], ![(-12 / 13 : ℚ), 0, (4 / 13 : ℚ), (-12 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-2 / 7 : ℚ)], ![(2 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ), (-18 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), 0, (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, (-4 / 15 : ℚ), (-2 / 15 : ℚ), (-28 / 15 : ℚ), (4 / 15 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-3 / 8 : ℚ), 0, (-3 / 8 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0, (5 / 3 : ℚ)], ![-2, (-10 / 3 : ℚ), (-5 / 3 : ℚ), (-1 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), 0, (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-28 / 45 : ℚ)], ![0, (-4 / 15 : ℚ), (-2 / 15 : ℚ), (-28 / 15 : ℚ), (-8 / 45 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, (-4 / 9 : ℚ), (-2 / 3 : ℚ), (-8 / 9 : ℚ)], ![0, (-2 / 9 : ℚ), 0, (-14 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 2 : ℚ), 0, -1, 0], ![0, (1 / 6 : ℚ), (1 / 3 : ℚ), (-7 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 4 : ℚ), 0, (-15 / 8 : ℚ)], ![(-9 / 8 : ℚ), (-1 / 8 : ℚ), (-3 / 2 : ℚ), 0, (15 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-4 / 15 : ℚ), 0, (-4 / 5 : ℚ), (-2 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 15 : ℚ), 0, (-8 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), -1, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -1, 0, -3], ![(-3 / 2 : ℚ), (-1 / 2 : ℚ), -2, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (8 / 27 : ℚ), (-8 / 3 : ℚ), (-16 / 9 : ℚ)], ![0, 0, (16 / 27 : ℚ), (-16 / 3 : ℚ), (8 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 7 : ℚ), 0, (-4 / 7 : ℚ), (-18 / 7 : ℚ), (-32 / 21 : ℚ)], ![0, (-6 / 7 : ℚ), (-8 / 7 : ℚ), (-36 / 7 : ℚ), (-22 / 21 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), 0, (-3 / 17 : ℚ), 0, (-32 / 17 : ℚ)], ![(-9 / 17 : ℚ), 0, (-43 / 17 : ℚ), (-3 / 17 : ℚ), (32 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, (-2 / 11 : ℚ), 0, (-19 / 11 : ℚ)], ![(-6 / 11 : ℚ), (-2 / 11 : ℚ), (-28 / 11 : ℚ), (-2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-1 / 12 : ℚ), 0, (-5 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (-1 / 12 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), 0, (-4 / 15 : ℚ), 0, (-28 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 15 : ℚ), (-14 / 5 : ℚ), (-4 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), 0, (-4 / 9 : ℚ), 0, (-64 / 9 : ℚ)], ![(-4 / 3 : ℚ), (-4 / 9 : ℚ), (-10 / 3 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 17 : ℚ), 0, (-4 / 17 : ℚ), 0, (-88 / 17 : ℚ)], ![(-12 / 17 : ℚ), (-4 / 17 : ℚ), (-46 / 17 : ℚ), (-4 / 17 : ℚ), (-52 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-6 / 7 : ℚ), 0], ![0, 0, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 18 : ℚ), (-1 / 18 : ℚ), 0, (-23 / 18 : ℚ), (-5 / 9 : ℚ)], ![(-1 / 18 : ℚ), 0, (-13 / 9 : ℚ), (-47 / 18 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 25 : ℚ), (-6 / 25 : ℚ), 0, (-116 / 75 : ℚ), (-326 / 75 : ℚ)], ![(-6 / 25 : ℚ), 0, (-68 / 75 : ℚ), (-10 / 3 : ℚ), (-154 / 75 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 3 : ℚ), (-8 / 9 : ℚ)], ![0, 0, 0, (-20 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), 0, (4 / 5 : ℚ), (2 / 15 : ℚ), (-22 / 3 : ℚ)], ![(-16 / 15 : ℚ), (-2 / 5 : ℚ), (-8 / 3 : ℚ), 0, (-36 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (-12 / 17 : ℚ), (-30 / 17 : ℚ), 0, 0], ![(12 / 17 : ℚ), (12 / 17 : ℚ), (-66 / 17 : ℚ), 0, (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), 0, (-18 / 17 : ℚ), (-12 / 17 : ℚ), (-12 / 17 : ℚ)], ![0, 0, (-42 / 17 : ℚ), (12 / 17 : ℚ), (6 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 17 : ℚ), (-12 / 17 : ℚ), (-30 / 17 : ℚ), 0, 0], ![(12 / 17 : ℚ), (12 / 17 : ℚ), (-66 / 17 : ℚ), 0, (3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), (-4 / 13 : ℚ), 0, (-16 / 13 : ℚ), (-24 / 13 : ℚ)], ![(-12 / 13 : ℚ), 0, (-12 / 13 : ℚ), (4 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-12 / 13 : ℚ), (-8 / 13 : ℚ), (-8 / 13 : ℚ)], ![0, 0, (-28 / 13 : ℚ), (4 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 15 : ℚ), 0, (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-7 / 15 : ℚ)], ![0, (-4 / 15 : ℚ), (-28 / 15 : ℚ), (4 / 15 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-3 / 4 : ℚ), (-3 / 8 : ℚ), 0, 0], ![0, (5 / 8 : ℚ), (-15 / 8 : ℚ), (1 / 8 : ℚ), (15 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-25 / 18 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ), (-17 / 18 : ℚ)], ![(5 / 6 : ℚ), (11 / 9 : ℚ), (-17 / 6 : ℚ), 0, (29 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, -1, (-5 / 3 : ℚ)], ![-1, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, -1, 0, 0], ![(1 / 3 : ℚ), (1 / 3 : ℚ), (-8 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 15 : ℚ), 0, 0, (2 / 15 : ℚ), (-4 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 15 : ℚ), (-37 / 30 : ℚ), (-19 / 30 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (1 / 2 : ℚ), 0, 1, (-24 / 7 : ℚ)], ![(-11 / 7 : ℚ), (-11 / 14 : ℚ), (-2 / 7 : ℚ), 0, (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, 0, 2, -6], ![(-10 / 3 : ℚ), (-14 / 3 : ℚ), (-2 / 3 : ℚ), 2, -6]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, 0, (2 / 7 : ℚ), (-6 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, 0, (2 / 7 : ℚ), (-6 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 8 : ℚ), (-1 / 4 : ℚ), 0], ![0, 0, (1 / 2 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, (-3 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-1 / 2 : ℚ), (-7 / 12 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, 0, (2 / 7 : ℚ), (-6 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-8 / 11 : ℚ), (-6 / 11 : ℚ), 0], ![(-2 / 11 : ℚ), 0, (4 / 11 : ℚ), (-6 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (2 / 9 : ℚ), (-8 / 9 : ℚ), 0, (-16 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-2 / 9 : ℚ), (-8 / 9 : ℚ), 0, (16 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, 0, (-1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -1, 0, -2], ![-1, (-1 / 2 : ℚ), -1, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-8 / 5 : ℚ), (-16 / 5 : ℚ)], ![0, (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-8 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (13 / 8 : ℚ), (-19 / 8 : ℚ), 0, (-15 / 8 : ℚ)], ![(-13 / 8 : ℚ), (-13 / 8 : ℚ), (-37 / 8 : ℚ), (-1 / 8 : ℚ), (15 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), (-17 / 22 : ℚ), (-1 / 22 : ℚ), (-49 / 22 : ℚ), (1 / 2 : ℚ)], ![(13 / 22 : ℚ), (15 / 22 : ℚ), 0, (-51 / 22 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), (-1 / 10 : ℚ), (-5 / 2 : ℚ), 0], ![(1 / 10 : ℚ), (-9 / 10 : ℚ), 0, (-27 / 10 : ℚ), (-7 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (13 / 5 : ℚ), (-29 / 10 : ℚ), 0, (-59 / 10 : ℚ)], ![(-13 / 5 : ℚ), (-29 / 10 : ℚ), (-11 / 2 : ℚ), (-3 / 10 : ℚ), (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-2 / 11 : ℚ), (-32 / 11 : ℚ), (-8 / 11 : ℚ)], ![0, 0, 0, (-36 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0, (-9 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, (-12 / 5 : ℚ), (-1 / 5 : ℚ), (9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), 0, (-2 / 11 : ℚ), 0, (-52 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-2 / 11 : ℚ), (-26 / 11 : ℚ), (-2 / 11 : ℚ), (-14 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), 0, (-4 / 9 : ℚ), 0, (-56 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-4 / 9 : ℚ), (-26 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 2, (1 / 3 : ℚ), -2], ![-2, -2, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 21 : ℚ), (1 / 21 : ℚ), (4 / 7 : ℚ), (2 / 21 : ℚ), (-158 / 21 : ℚ)], ![(-2 / 3 : ℚ), (-1 / 7 : ℚ), (-32 / 21 : ℚ), 0, (-26 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-4 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, 0, 0, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-2 / 5 : ℚ)], ![0, 0, (-6 / 5 : ℚ), (4 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), 0, 0, (-8 / 5 : ℚ), -2], ![(-4 / 5 : ℚ), 0, (-2 / 5 : ℚ), (8 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-1 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), 0], ![0, (1 / 9 : ℚ), (-8 / 9 : ℚ), (8 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, -1, (-4 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, 0, (-6 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-6 / 11 : ℚ), (-8 / 11 : ℚ), 0], ![(-2 / 11 : ℚ), 0, (-6 / 11 : ℚ), (4 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 2 : ℚ), 0, -1, (-13 / 4 : ℚ)], ![-1, -1, 0, -1, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, 0, (-2 / 3 : ℚ), (-10 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), (7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), 0, 0], ![(4 / 7 : ℚ), (4 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-14 / 33 : ℚ), (-8 / 11 : ℚ), (-8 / 11 : ℚ), 0], ![0, (2 / 33 : ℚ), (-12 / 11 : ℚ), (-12 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![0, 0, (-6 / 5 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![(1 / 10 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 5 : ℚ), 0, 0, 0], ![(1 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-1 / 7 : ℚ)], ![0, 0, (1 / 7 : ℚ), (-3 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (-1 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ)], ![0, 0, (1 / 7 : ℚ), (-3 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, (-3 / 10 : ℚ), 0, (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), 0, (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ)], ![0, 0, 0, (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, -1, (-1 / 4 : ℚ)], ![0, 0, 0, -1, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, 0, 0, (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![(1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![(1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-3 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-1 / 48 : ℚ), (-9 / 8 : ℚ), 0, (-35 / 24 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 48 : ℚ), (-53 / 24 : ℚ), (-1 / 24 : ℚ), (5 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (-2 / 9 : ℚ), (-1 / 18 : ℚ), (-23 / 18 : ℚ), 0], ![(1 / 18 : ℚ), (1 / 9 : ℚ), 0, (-25 / 18 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 11 : ℚ), 0, (-1 / 11 : ℚ), 0, (-26 / 11 : ℚ)], ![(-2 / 11 : ℚ), (-1 / 11 : ℚ), (-13 / 11 : ℚ), (-1 / 11 : ℚ), (-7 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, (-2 / 9 : ℚ), 0, (-28 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-2 / 9 : ℚ), (-13 / 9 : ℚ), (-2 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (-17 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, 0, (-5 / 12 : ℚ), (-31 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-7 / 12 : ℚ), (-1 / 2 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(1 / 4 : ℚ), -1, 1, (1 / 4 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(1 / 3 : ℚ), -1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(1 / 4 : ℚ), -1, 1, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 4 : ℚ), -1, 1, (-9 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 4 : ℚ), -1, 1, (-9 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 3 : ℚ), -1, 1, (-7 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![(1 / 4 : ℚ), -2, 2, (-9 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![(1 / 4 : ℚ), -2, 2, (-9 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![(1 / 4 : ℚ), -2, 2, (-9 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(1 / 3 : ℚ), -1, 1, (1 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(1 / 4 : ℚ), -1, 1, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 4 : ℚ), -1, 1, (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 3 : ℚ), -1, 1, (-4 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 4 : ℚ), -1, 1, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![(2 / 7 : ℚ), -2, 2, (-18 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![(1 / 4 : ℚ), -2, 2, (-5 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![(1 / 2 : ℚ), -2, 2, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 1, (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, -1, (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, -1, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 1, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 7 : ℚ), -1, 1, (-1 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 3 : ℚ), -1, 1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 7 : ℚ), -1, 1, (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 7 : ℚ), -1, 1, (-1 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 4 : ℚ), -1, 1, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 3 : ℚ), -1, 1, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 4 : ℚ), -1, -1, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), -1, -1, (-8 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), -1, -1, (-8 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, -1, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), -1, (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 7 : ℚ), (-6 / 7 : ℚ), 0], ![(2 / 7 : ℚ), (-10 / 7 : ℚ), (-10 / 7 : ℚ), (-10 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), 0], ![0, (-1 / 3 : ℚ), 0, (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 8 : ℚ), 0, 0], ![0, -1, (-1 / 4 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), (-2 / 3 : ℚ), 0], ![(1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, 0, -2, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, 0, -2, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -2, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-5 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, 0, -2, (5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-3 / 8 : ℚ)], ![(-1 / 8 : ℚ), 0, 0, -2, (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-9 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, -2, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-43 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (-21 / 20 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), -3]] }
]

theorem conicDetC03_checked : conicDetC03.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
