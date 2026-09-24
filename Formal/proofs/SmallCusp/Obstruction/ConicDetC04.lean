import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC04 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![0, -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, 0], ![0, -1, (-1 / 3 : ℚ), (-5 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 14 : ℚ), 0, (-25 / 14 : ℚ)], ![(-1 / 14 : ℚ), (-15 / 14 : ℚ), (-19 / 28 : ℚ), (-11 / 28 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 4 : ℚ), (-9 / 4 : ℚ)], ![(-1 / 3 : ℚ), (-5 / 6 : ℚ), 0, (-5 / 6 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 16 : ℚ), (-1 / 16 : ℚ), 0], ![(1 / 16 : ℚ), (-5 / 16 : ℚ), (-5 / 16 : ℚ), (3 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 16 : ℚ), (-1 / 16 : ℚ), 0], ![(1 / 16 : ℚ), (-5 / 16 : ℚ), (-5 / 16 : ℚ), (3 / 16 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), -1, -1, 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-4 / 7 : ℚ), 0, (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![(1 / 6 : ℚ), (-11 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -1, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -2, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, 0, 0, -1, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (1 / 6 : ℚ)], ![(-1 / 3 : ℚ), 0, 0, -1, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 6 : ℚ), -1], ![(-1 / 3 : ℚ), 0, 0, (-1 / 6 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (2 / 5 : ℚ), -4], ![(-4 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (2 / 5 : ℚ), -4], ![(-4 / 5 : ℚ), 0, 0, (-2 / 5 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-2 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 4 : ℚ), -4], ![(-1 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, -1, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (-3 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![0, -1, 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, 0, -1, (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (1 / 6 : ℚ)], ![(1 / 3 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 4 : ℚ), 0, 0, -1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -1, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 1], ![-1, 0, 0, -1, 1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, -1, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (-1 / 8 : ℚ)], ![(1 / 8 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, -1, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, 0, -2, (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-1 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 4 : ℚ), 0, 0, -2, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -2, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, -2, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, (-1 / 8 : ℚ)], ![(1 / 4 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, -2, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 6 : ℚ), 0, 0, (-7 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 6 : ℚ), 0, 0, (-7 / 6 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), 1, -1], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![0, -1, 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, (-3 / 4 : ℚ), 0], ![(1 / 8 : ℚ), -2, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (11 / 10 : ℚ), -4], ![(-6 / 5 : ℚ), 0, 0, (-1 / 10 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), -4], ![(-1 / 8 : ℚ), 0, 0, (3 / 8 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (1 / 4 : ℚ)], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), -4], ![(-1 / 4 : ℚ), 0, 0, (3 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 3 : ℚ), -4], ![(-1 / 3 : ℚ), 0, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-2 / 3 : ℚ), -4], ![(-1 / 3 : ℚ), 0, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, -1, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (5 / 4 : ℚ), -4], ![(-3 / 2 : ℚ), 0, 0, (3 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -4], ![(-5 / 3 : ℚ), 0, 0, 1, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(1 / 3 : ℚ), -1, -1, 0, (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(1 / 3 : ℚ), -1, -1, 0, (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-7 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-7 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(1 / 3 : ℚ), -1, -1, (-13 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![(1 / 3 : ℚ), -1, -1, (-5 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -4, 0, 0], ![(1 / 4 : ℚ), -2, -2, (-17 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (1 / 6 : ℚ)], ![(-1 / 3 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 16 : ℚ), (-1 / 8 : ℚ), 0], ![(1 / 16 : ℚ), (-3 / 16 : ℚ), (-1 / 8 : ℚ), (-5 / 16 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), (-2 / 5 : ℚ), 0], ![(1 / 5 : ℚ), (-3 / 5 : ℚ), (-2 / 5 : ℚ), -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), 0, (-5 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), -1, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-2 / 3 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), (-4 / 3 : ℚ)], ![(-1 / 3 : ℚ), -1, (-1 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 5 : ℚ), 0, (-16 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 11 : ℚ), 0], ![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-1 / 11 : ℚ), (2 / 11 : ℚ), (-2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, -1], ![(1 / 4 : ℚ), -1, -1, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 4 : ℚ), (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 10 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-3 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), -1, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-2 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-2 / 7 : ℚ), (-4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 4 : ℚ), 0, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), 0, 0], ![(1 / 5 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![0, -1, (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), 0, 0], ![(2 / 9 : ℚ), (-4 / 9 : ℚ), (-1 / 3 : ℚ), (2 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), (-7 / 10 : ℚ), 0], ![(1 / 5 : ℚ), (-3 / 10 : ℚ), (-3 / 10 : ℚ), (-7 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-1 / 3 : ℚ)], ![(-1 / 9 : ℚ), 0, 0, -1, (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 3 : ℚ), 0, 0, -1, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 6 : ℚ), 0, 0, -1, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![0, -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-10 / 3 : ℚ)], ![(-1 / 3 : ℚ), 0, 0, -1, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-1 / 2 : ℚ)], ![(-1 / 12 : ℚ), 0, 0, -1, (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 3 : ℚ), 0, 0, -1, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-3 / 10 : ℚ)], ![(-1 / 10 : ℚ), 0, 0, -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-1 / 3 : ℚ)], ![(-1 / 9 : ℚ), 0, 0, -2, (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 3 : ℚ), 0, 0, -2, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(1 / 3 : ℚ), -1, -1, 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-22 / 9 : ℚ)], ![(-1 / 3 : ℚ), 0, 0, -2, (-11 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-3 / 2 : ℚ)], ![(-1 / 12 : ℚ), 0, 0, -2, (7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 3 : ℚ), 0, 0, -2, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 20 : ℚ)], ![(-1 / 20 : ℚ), (-1 / 20 : ℚ), (-1 / 20 : ℚ), (-21 / 20 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![(1 / 3 : ℚ), -1, -1, (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![0, -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![0, -1, -1, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (7 / 36 : ℚ), (-20 / 9 : ℚ)], ![(-1 / 4 : ℚ), (-31 / 36 : ℚ), 0, (-31 / 72 : ℚ), (-10 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -4, (-3 / 5 : ℚ), 0], ![(1 / 5 : ℚ), -2, -2, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-2 / 3 : ℚ), (-1 / 2 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-2 / 3 : ℚ), (-1 / 6 : ℚ), 0], ![(1 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 10 : ℚ), -4], ![(-1 / 10 : ℚ), 0, 0, (1 / 2 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 9 : ℚ), (-1 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (-1 / 3 : ℚ), (-2 / 9 : ℚ), (2 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ)], ![0, (-1 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), -4], ![(-1 / 9 : ℚ), 0, 0, (2 / 9 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, -2], ![(1 / 3 : ℚ), -1, -1, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -4, 0, 0], ![(1 / 4 : ℚ), -2, -2, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), (-1 / 4 : ℚ), 0], ![(1 / 12 : ℚ), (-17 / 12 : ℚ), (-1 / 4 : ℚ), (-5 / 12 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, -2], ![(-1 / 3 : ℚ), -1, -1, 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), -1, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-8 / 3 : ℚ), (-8 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-8 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (1 / 3 : ℚ), -4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, (1 / 3 : ℚ), 4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![0, 1, (-1 / 3 : ℚ), 4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![0, -1, (-1 / 3 : ℚ), -4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-21 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-13 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-17 / 13 : ℚ), (-4 / 13 : ℚ), (-56 / 13 : ℚ), (-12 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-7 / 6 : ℚ), (-25 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-13 / 3 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-13 / 3 : ℚ), 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .y), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), 0, -1]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .yy), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 5 : ℚ), (-1 / 10 : ℚ)], ![(1 / 10 : ℚ), (-3 / 10 : ℚ), (11 / 10 : ℚ), (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 3 : ℚ), 0], ![0, -1, (1 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), -1, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![0, -1, 0, (-9 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![(1 / 8 : ℚ), (-3 / 8 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), -1, 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, -1, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), 0, -1, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), -1, 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 8 : ℚ), (-3 / 8 : ℚ), 0], ![(1 / 8 : ℚ), (-5 / 8 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ), (5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), -1, 0, (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, (-3 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, -2, (-1 / 4 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, -2, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 6 : ℚ), 0, -2, (-1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, -2, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, -2, (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, -2, (-1 / 2 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), 0], ![0, -1, 0, -4, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![0, -1, -1, -3, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-17 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-11 / 10 : ℚ), (-7 / 20 : ℚ), (-15 / 4 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-13 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 13 : ℚ), (-20 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-15 / 13 : ℚ), (-17 / 26 : ℚ), (-7 / 2 : ℚ), (-19 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![(1 / 8 : ℚ), (-3 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (1 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-3 / 4 : ℚ), -2, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![0, -1, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 2 : ℚ), (-3 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 2 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![0, -1, (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), (-1 / 9 : ℚ), 0], ![(1 / 9 : ℚ), (-5 / 9 : ℚ), (-8 / 9 : ℚ), 1, (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![(1 / 8 : ℚ), (-3 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ), (31 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), 0, 0], ![(1 / 8 : ℚ), (-3 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ), (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, 0], ![(1 / 3 : ℚ), (-5 / 3 : ℚ), (-8 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), 0, 0], ![(1 / 6 : ℚ), (-5 / 6 : ℚ), (-4 / 3 : ℚ), 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![(-2 / 3 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .x), (.x, .zero), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 3 : ℚ), (-4 / 3 : ℚ), (-11 / 6 : ℚ), (-1 / 2 : ℚ), (-1 / 3 : ℚ)]] }
]

theorem conicDetC04_checked : conicDetC04.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
