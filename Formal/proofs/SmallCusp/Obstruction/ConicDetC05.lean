import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC05 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (-11 / 6 : ℚ), -3, (-5 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (-11 / 6 : ℚ), (-10 / 3 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-8 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-8 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), -2, (-5 / 4 : ℚ)], ![(-3 / 4 : ℚ), (-1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-8 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .xy), (.xx, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (-7 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .xy), (.xx, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 8 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xx, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ), (-7 / 8 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xx, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xx, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ)], ![(-1 / 3 : ℚ), -1, -1, (-1 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xx, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (5 / 4 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 6 : ℚ), 0], ![0, -1, (1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![0, -1, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, -2, (-1 / 4 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), 0, -2, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, -2, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-2 / 7 : ℚ), 0, -2, (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, -2, (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, -2, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (1 / 4 : ℚ), -1], ![-1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, 0, -1], ![-1, 0, -1, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-37 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-21 / 20 : ℚ), (-17 / 40 : ℚ), (-13 / 8 : ℚ), (-9 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (11 / 10 : ℚ), 0, -4], ![(-6 / 5 : ℚ), 0, (-9 / 10 : ℚ), 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 8 : ℚ), 0, 0], ![0, -1, (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (1 / 8 : ℚ)], ![(1 / 8 : ℚ), (-3 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 16 : ℚ), (-1 / 16 : ℚ), 0], ![(1 / 16 : ℚ), (-5 / 16 : ℚ), (-5 / 16 : ℚ), (3 / 16 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![0, -1, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 8 : ℚ), (-1 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (-5 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (3 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (17 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 6 : ℚ), (-5 / 6 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)], ![0, (-5 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), -1, (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, -1, -1, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), -1, (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .xy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![0, -1, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 0, 0, 1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 1, (-5 / 2 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 6 : ℚ)], ![0, -1, (1 / 6 : ℚ), (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 6 : ℚ)], ![0, -1, (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, (1 / 2 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 4 : ℚ)], ![0, -1, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![0, -1, 0, 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xy, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, (1 / 3 : ℚ), (1 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![0, -1, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 5 : ℚ)], ![0, -1, 0, 0, (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (-11 / 6 : ℚ), (1 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 13 : ℚ), 0], ![(2 / 13 : ℚ), (-24 / 13 : ℚ), (2 / 13 : ℚ), (-4 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 7 : ℚ), -1, -1, (-1 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 4 : ℚ), -1, -1, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-1 / 3 : ℚ), -1, -1, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 0, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, (-1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, -1], ![-1, 0, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 2 : ℚ)], ![0, -1, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, (-5 / 2 : ℚ)], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, (-16 / 5 : ℚ)], ![-1, 0, 0, 0, (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 9 : ℚ)], ![0, -1, (-2 / 9 : ℚ), (5 / 9 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, -4], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 12 : ℚ)], ![0, -1, (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-17 / 13 : ℚ), (-4 / 13 : ℚ), (-17 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-27 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-13 / 10 : ℚ), (-3 / 10 : ℚ), (-3 / 4 : ℚ), (-13 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 5 : ℚ), 0, -2], ![(-2 / 5 : ℚ), -1, (-4 / 5 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 5 : ℚ), (-7 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-13 / 4 : ℚ), (-7 / 4 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (7 / 6 : ℚ), (-17 / 6 : ℚ), (-17 / 6 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 10 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (-1 / 4 : ℚ), 0], ![(1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(1 / 12 : ℚ), (-17 / 12 : ℚ), (-5 / 12 : ℚ), (-5 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 6 : ℚ), (-11 / 6 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (6 / 5 : ℚ), -3, (-8 / 5 : ℚ)], ![(-7 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, (1 / 6 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, (-3 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 4 : ℚ), -1, 1, 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-13 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 4 : ℚ), -1, 1, (-9 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 4 : ℚ), -1, 1, (-9 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 4 : ℚ), -2, 2, (-9 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 4 : ℚ), -2, 2, (-9 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-10 / 3 : ℚ), 0, 0, 0], ![(4 / 9 : ℚ), (-10 / 3 : ℚ), (22 / 9 : ℚ), (-68 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, (-7 / 6 : ℚ)], ![(1 / 6 : ℚ), -1, 1, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-7 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![0, (-7 / 5 : ℚ), 1, 0, (-17 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -1, 0, (-9 / 8 : ℚ), 0], ![(1 / 4 : ℚ), -1, 1, (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, (-7 / 6 : ℚ), 0], ![(1 / 6 : ℚ), -1, 1, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-7 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ), 0], ![0, (-7 / 5 : ℚ), 1, (-17 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, (-9 / 4 : ℚ), 0], ![0, -2, 2, (-19 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), -2, 0, (-12 / 5 : ℚ), 0], ![(1 / 5 : ℚ), -2, 2, (-26 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-19 / 8 : ℚ), (-1 / 4 : ℚ), (-21 / 8 : ℚ), 0], ![0, (-19 / 8 : ℚ), (15 / 8 : ℚ), (-11 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, (-7 / 6 : ℚ)], ![(1 / 6 : ℚ), -1, 1, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -1, 0, (-9 / 8 : ℚ), 0], ![(1 / 4 : ℚ), -1, 1, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, (-7 / 6 : ℚ), 0], ![(1 / 6 : ℚ), -1, 1, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, 0, (-5 / 2 : ℚ), 0], ![0, -2, 2, -3, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), -2, 0, (-14 / 5 : ℚ), 0], ![(2 / 5 : ℚ), -2, 2, (-18 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -1, 0, 0, 0], ![(1 / 4 : ℚ), -1, 1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, -1, -1], ![(-1 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![(1 / 4 : ℚ), -1, 1, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), -1, 0, 0, (-3 / 5 : ℚ)], ![(1 / 5 : ℚ), -1, 1, 0, (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-10 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-9 / 8 : ℚ), 0, 0, (1 / 8 : ℚ)], ![(3 / 8 : ℚ), (-9 / 8 : ℚ), (9 / 8 : ℚ), 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-7 / 6 : ℚ), 0, 0, (1 / 6 : ℚ)], ![(1 / 3 : ℚ), (-7 / 6 : ℚ), (7 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, 0], ![(1 / 8 : ℚ), (-5 / 4 : ℚ), (9 / 8 : ℚ), 0, (-3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, (1 / 4 : ℚ), 0], ![(1 / 4 : ℚ), -2, 2, (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), -2, 0, (1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), -2, 2, (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-5 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)], ![(1 / 2 : ℚ), (-5 / 4 : ℚ), (5 / 4 : ℚ), (1 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, (-1 / 3 : ℚ), 0], ![(1 / 6 : ℚ), -1, 1, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-5 / 2 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -2, 0, 0, 0], ![0, -2, 2, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, 0, 0], ![(1 / 8 : ℚ), -2, 2, (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, 0, (-1 / 8 : ℚ), -1], ![(-1 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ), -1], ![(-1 / 3 : ℚ), 0, 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), -4], ![(-1 / 2 : ℚ), 0, 0, (-3 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, 0, (-1 / 10 : ℚ), -4], ![(-1 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 1, -1], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, (-9 / 8 : ℚ), 0], ![0, -2, 2, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, 1, -4], ![(-7 / 6 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -2, 0, 1, 0], ![(5 / 4 : ℚ), -2, 2, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), -1, 0, 0, -2], ![(1 / 4 : ℚ), -1, 1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-33 / 16 : ℚ), 0, (17 / 16 : ℚ), 0], ![(21 / 16 : ℚ), (-33 / 16 : ℚ), (33 / 16 : ℚ), (-17 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), -1, 0, 0, -2], ![(1 / 6 : ℚ), -1, 1, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, -1, -4], ![(-1 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-13 / 6 : ℚ), 0, (7 / 6 : ℚ), 0], ![(3 / 2 : ℚ), (-13 / 6 : ℚ), (13 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 3 : ℚ), -2, 2, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(1 / 3 : ℚ), -2, 2, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, 0], ![(1 / 6 : ℚ), (-5 / 2 : ℚ), (13 / 6 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), -2, 0, (-5 / 4 : ℚ), 0], ![0, -2, 2, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), -2, 0, (-7 / 5 : ℚ), 0], ![(1 / 5 : ℚ), -2, 2, (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), (4 / 3 : ℚ), 0, 0, (-11 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-8 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 4 : ℚ), 1, 0, (-9 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), (4 / 3 : ℚ), 0, (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-124 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-10 / 3 : ℚ), 0, 0], ![(4 / 9 : ℚ), (22 / 9 : ℚ), 0, (-68 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-32 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), 0, (-7 / 5 : ℚ)], ![(1 / 10 : ℚ), (11 / 10 : ℚ), 0, 0, (-29 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-11 / 8 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 4 : ℚ), (-5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, -1, (-9 / 8 : ℚ), 0], ![(1 / 4 : ℚ), 1, 0, (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), (-7 / 5 : ℚ), 0], ![(1 / 10 : ℚ), (11 / 10 : ℚ), 0, (-29 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-1 / 4 : ℚ), (-11 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-5 / 8 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 20 : ℚ), (-16 / 15 : ℚ), 0, (-13 / 10 : ℚ), (-101 / 20 : ℚ)], ![(-3 / 20 : ℚ), (-59 / 60 : ℚ), (-3 / 20 : ℚ), (-11 / 4 : ℚ), (-49 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-46 / 17 : ℚ), (-62 / 17 : ℚ), 0], ![(4 / 17 : ℚ), (38 / 17 : ℚ), 0, (-132 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), 0, (-8 / 11 : ℚ), (-58 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-4 / 11 : ℚ), (-20 / 11 : ℚ), (-56 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ), 0, (-8 / 5 : ℚ)], ![(1 / 5 : ℚ), (6 / 5 : ℚ), 0, 0, (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, (-7 / 6 : ℚ), 0], ![(1 / 3 : ℚ), 1, 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ), (-8 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (6 / 5 : ℚ), 0, (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-23 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-11 / 4 : ℚ), (-13 / 4 : ℚ), 0], ![(1 / 4 : ℚ), (9 / 4 : ℚ), 0, (-15 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), 0, (1 / 6 : ℚ)], ![(1 / 2 : ℚ), (7 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (5 / 4 : ℚ), 0, 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), 0, (-3 / 10 : ℚ)], ![(1 / 10 : ℚ), (11 / 10 : ℚ), 0, 0, (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-4 / 3 : ℚ), -1], ![(-1 / 6 : ℚ), 0, 0, (-7 / 6 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-6 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, 0, (-7 / 6 : ℚ), -1], ![(-1 / 6 : ℚ), 0, 0, (-13 / 6 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 4 : ℚ), 0], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 4 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, (-1 / 6 : ℚ), 0], ![(1 / 3 : ℚ), 1, 0, (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, 0, (-5 / 2 : ℚ)], ![(1 / 3 : ℚ), 1, 0, 0, (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, 0, (-13 / 6 : ℚ)], ![(1 / 3 : ℚ), 1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, 0, (-9 / 4 : ℚ)], ![(1 / 3 : ℚ), 1, 0, 0, (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 2 : ℚ), 0, 0], ![(1 / 6 : ℚ), (13 / 6 : ℚ), 0, (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, (7 / 8 : ℚ), (-39 / 8 : ℚ)], ![(-9 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (3 / 4 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-19 / 8 : ℚ), (-13 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (17 / 8 : ℚ), 0, (-15 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(1 / 3 : ℚ), 1, -1, 0, (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-31 / 17 : ℚ), 0], ![(-2 / 17 : ℚ), (-2 / 17 : ℚ), (-2 / 17 : ℚ), (-27 / 17 : ℚ), (-2 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-2 / 9 : ℚ), (-8 / 3 : ℚ), (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(1 / 3 : ℚ), 1, -1, (-13 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(1 / 3 : ℚ), 1, -1, (-13 / 6 : ℚ), 0]] }
]

theorem conicDetC05_checked : conicDetC05.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
