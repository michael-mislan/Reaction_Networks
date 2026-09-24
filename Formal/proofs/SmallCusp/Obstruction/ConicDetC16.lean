import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC16 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -1], ![(1 / 3 : ℚ), -1, 1, (1 / 6 : ℚ), (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 6 : ℚ), 0, 0, (-1 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -1], ![(3 / 4 : ℚ), -1, 1, 0, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, -1, 0], ![1, -1, 1, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, -1, 0], ![(1 / 3 : ℚ), -1, 1, (-13 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, -2, 0], ![(1 / 2 : ℚ), -2, 2, (-9 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -1], ![(1 / 3 : ℚ), -1, 1, (1 / 6 : ℚ), (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -1], ![(3 / 4 : ℚ), -1, 1, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, -1, 0], ![1, -1, 1, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, -1, 0], ![(1 / 3 : ℚ), -1, 1, (-7 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, -1, 0], ![0, -1, 1, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![(-2 / 7 : ℚ), 0, 0, (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, -2, 0], ![(1 / 2 : ℚ), -2, 2, (-5 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, -2, 0], ![0, -2, 2, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, 0, 0, (1 / 4 : ℚ), 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 6 : ℚ), 0, 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![(5 / 6 : ℚ), -1, 1, (2 / 3 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![(2 / 3 : ℚ), -1, 1, (1 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![0, -1, 1, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![(1 / 3 : ℚ), -1, 1, (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 6 : ℚ), 0, 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![(1 / 3 : ℚ), -1, 1, (1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, 0, 0, 0, 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![(1 / 3 : ℚ), -1, 1, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![0, -1, 1, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![-1, -1, 1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![0, -1, 1, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![0, -1, 1, (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![0, 0, 0, 0, 1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![(1 / 3 : ℚ), -1, 1, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -1], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![0, -1, 1, (1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![1, -1, 1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![(2 / 3 : ℚ), -1, 1, 0, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![(1 / 2 : ℚ), -2, 2, (1 / 4 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .yy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![1, 0, 0, 0, 0], ![-1, 1, -1, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -1], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, 0], ![0, -1, 1, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, -1, 0], ![0, -2, 2, (-1 / 7 : ℚ), (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -4], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, -1, 0], ![0, -2, 2, (-1 / 7 : ℚ), (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![1, -1, 1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![1, -1, 1, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![1, -1, 1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![(1 / 3 : ℚ), -1, 1, (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 6 : ℚ), 0, 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![(1 / 3 : ℚ), -1, 1, (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -4], ![(-1 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![0, -1, 1, (1 / 4 : ℚ), (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, -2], ![0, -1, 1, (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, 0, 0], ![(1 / 2 : ℚ), -2, 2, -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 1, -4], ![(-7 / 4 : ℚ), 0, 0, (17 / 28 : ℚ), (-27 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, -1, 0], ![(1 / 6 : ℚ), -2, 2, (-4 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, 0, -1, 0], ![(-1 / 2 : ℚ), -2, 2, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (1 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (1 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, -1, (3 / 10 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (1 / 6 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), 0], ![0, (-3 / 5 : ℚ), (-1 / 5 : ℚ), (-4 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 7 : ℚ), 0, (3 / 7 : ℚ), -1], ![(-3 / 7 : ℚ), (-6 / 7 : ℚ), (-3 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0], ![(2 / 5 : ℚ), (-8 / 5 : ℚ), (-8 / 5 : ℚ), (-12 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 17 : ℚ), 0, (8 / 17 : ℚ), (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-16 / 17 : ℚ), 0, (-16 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (-1 / 2 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, -1, 0], ![(-3 / 5 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (1 / 18 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 18 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (1 / 10 : ℚ), (-1 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 7 : ℚ), 0, 0, -1], ![(-3 / 7 : ℚ), (-6 / 7 : ℚ), (-3 / 7 : ℚ), (-3 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), 0, (-5 / 6 : ℚ)], ![(-1 / 3 : ℚ), (1 / 12 : ℚ), 0, (-1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(16 / 17 : ℚ), (8 / 17 : ℚ), 0, 0, (-44 / 17 : ℚ)], ![(-24 / 17 : ℚ), 0, 0, (-8 / 17 : ℚ), (-44 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (1 / 8 : ℚ), 0, 0, (-5 / 16 : ℚ)], ![(1 / 4 : ℚ), (-5 / 8 : ℚ), (-3 / 4 : ℚ), (1 / 8 : ℚ), (-7 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 8 : ℚ), 0, 0, (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 10 : ℚ), (-3 / 5 : ℚ), 0, (-7 / 10 : ℚ)], ![(-3 / 10 : ℚ), (-3 / 5 : ℚ), (-9 / 10 : ℚ), (-3 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), (-2 / 9 : ℚ), 0, (-8 / 9 : ℚ)], ![0, (-4 / 3 : ℚ), (-2 / 3 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(16 / 17 : ℚ), (8 / 17 : ℚ), 0, 0, (-44 / 17 : ℚ)], ![(-24 / 17 : ℚ), 0, 0, 0, (-44 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0], ![0, (-2 / 5 : ℚ), (-1 / 5 : ℚ), (1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 8 : ℚ), 0, (-5 / 8 : ℚ), (-5 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, (-1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 17 : ℚ), (2 / 17 : ℚ), 0, (-10 / 17 : ℚ), 0], ![(-1 / 17 : ℚ), (-5 / 17 : ℚ), 0, (7 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (1 / 8 : ℚ), 0, 0, (1 / 8 : ℚ)], ![(1 / 4 : ℚ), (-5 / 8 : ℚ), (-3 / 4 : ℚ), (1 / 8 : ℚ), (-5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (1 / 40 : ℚ), (-3 / 20 : ℚ), 0], ![(-1 / 20 : ℚ), (-11 / 20 : ℚ), (-1 / 40 : ℚ), (1 / 20 : ℚ), (-1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 12 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (1 / 7 : ℚ), (1 / 7 : ℚ), (-5 / 7 : ℚ), (-8 / 7 : ℚ)], ![(-3 / 7 : ℚ), 0, 0, (1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, (1 / 6 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (2 / 9 : ℚ), (-2 / 9 : ℚ), 0, 0], ![(1 / 9 : ℚ), (-5 / 9 : ℚ), (-2 / 9 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), (-1 / 2 : ℚ), (-5 / 6 : ℚ)], ![(-1 / 2 : ℚ), 0, (1 / 3 : ℚ), (-1 / 2 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0], ![0, (-3 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (1 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (1 / 7 : ℚ), (-1 / 14 : ℚ), 0, 0], ![(-1 / 14 : ℚ), (-6 / 7 : ℚ), (-1 / 14 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-2 / 5 : ℚ)], ![0, (-3 / 5 : ℚ), (-1 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 8 : ℚ), 0, 0, -1, (-1 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, 0, -2, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 0, 0, -1, (-5 / 6 : ℚ)], ![(-2 / 3 : ℚ), 0, 0, -2, (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-2 / 3 : ℚ), 0], ![0, (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(15 / 34 : ℚ), 0, 0, -1, (3 / 34 : ℚ)], ![(-9 / 17 : ℚ), 0, 0, -2, (9 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, 0, -1, (-31 / 24 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, -2, (13 / 24 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 4 : ℚ), 0, -1, 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), -1, -1, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, -1, (-23 / 10 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, -2, (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 6 : ℚ), 0, 0], ![(1 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), (-11 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-9 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), -3]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 1, -1], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 18 : ℚ), 0, (5 / 18 : ℚ), (-1 / 9 : ℚ)], ![(-1 / 18 : ℚ), (-7 / 9 : ℚ), 0, (-7 / 9 : ℚ), (-1 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 13 : ℚ), (1 / 13 : ℚ), (-5 / 13 : ℚ), 0, (-22 / 13 : ℚ)], ![0, (-14 / 13 : ℚ), (-37 / 52 : ℚ), (-19 / 52 : ℚ), (-21 / 26 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (1 / 16 : ℚ), 0, (17 / 16 : ℚ), (-61 / 16 : ℚ)], ![(-5 / 16 : ℚ), 0, 0, (-13 / 16 : ℚ), (-61 / 16 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ)], ![(-2 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -1], ![0, -1, (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(16 / 15 : ℚ), (8 / 15 : ℚ), 0, 0, (-12 / 5 : ℚ)], ![(-16 / 15 : ℚ), 0, 0, 0, (-12 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-7 / 12 : ℚ), (-5 / 9 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (1 / 6 : ℚ), (-7 / 36 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (1 / 7 : ℚ), (1 / 7 : ℚ), (-5 / 7 : ℚ), (-8 / 7 : ℚ)], ![(-3 / 7 : ℚ), 0, 0, (1 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), 0], ![0, (-1 / 4 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 9 : ℚ), (2 / 9 : ℚ), (-4 / 9 : ℚ), (4 / 9 : ℚ), (-14 / 9 : ℚ)], ![(1 / 3 : ℚ), -1, (-4 / 9 : ℚ), (4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 9 : ℚ), (2 / 9 : ℚ), 0, 0, (-20 / 9 : ℚ)], ![(-1 / 9 : ℚ), (-5 / 9 : ℚ), 0, 0, (16 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-3 / 10 : ℚ)], ![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-1 / 5 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 7 : ℚ), 0, (3 / 7 : ℚ), -1], ![(-3 / 7 : ℚ), (-6 / 7 : ℚ), (-3 / 7 : ℚ), (-6 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 17 : ℚ), 0, (8 / 17 : ℚ), (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-16 / 17 : ℚ), 0, (-16 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -1], ![(-3 / 7 : ℚ), (-13 / 14 : ℚ), (-3 / 7 : ℚ), (-3 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (11 / 24 : ℚ), (-1 / 24 : ℚ), 0, (-1 / 6 : ℚ)], ![0, (-5 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (4 / 9 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0], ![(-1 / 9 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, (1 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, -1, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, 0, -1, (1 / 8 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, -2, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 8 : ℚ), (1 / 8 : ℚ), (-7 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), 0, (-3 / 8 : ℚ), (-7 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ), -4], ![(-1 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 4 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ), -4], ![(-1 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), 0], ![(-3 / 5 : ℚ), 0, 0, 0, (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, 0, -1, (1 / 6 : ℚ)], ![(-1 / 3 : ℚ), 0, 0, -1, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, -1, 0], ![(-3 / 5 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ), (-4 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, -1, (-1 / 3 : ℚ), 0], ![0, -1, 0, (-13 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -2, 0, 0], ![0, -2, 0, (-9 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 8 : ℚ), (-7 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), 0, -2, (-3 / 5 : ℚ), 0], ![(-1 / 10 : ℚ), -2, 0, (-22 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-1 / 5 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, 0], ![(-1 / 2 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-1 / 5 : ℚ)], ![0, (-3 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -1, -1, 0], ![0, -1, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -2, (-3 / 4 : ℚ), 0], ![0, -2, 0, (-9 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, (-3 / 4 : ℚ), 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -2, -2, 0], ![0, -2, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), 0], ![(-1 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(19 / 22 : ℚ), (9 / 11 : ℚ), (1 / 22 : ℚ), (-21 / 22 : ℚ), (5 / 22 : ℚ)], ![(-10 / 11 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (-7 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 3 : ℚ), 0, 0, -1, (-1 / 6 : ℚ)], ![(-1 / 3 : ℚ), 0, 0, -1, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), 0, -1, 0, (1 / 8 : ℚ)], ![(1 / 4 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, -1], ![(-3 / 2 : ℚ), 0, 0, -1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), 0, 0, -1, (1 / 10 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, -1, 0, 0], ![(-1 / 3 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, -4], ![(-3 / 2 : ℚ), 0, 0, -1, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -1, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, -4], ![(-3 / 2 : ℚ), 0, 0, -1, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 8 : ℚ), 0, 0, -1, (-1 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, 0, -2, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 16 : ℚ), 0, -1, 0, (1 / 16 : ℚ)], ![(1 / 8 : ℚ), -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, -1], ![(-3 / 2 : ℚ), 0, 0, -2, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(15 / 34 : ℚ), 0, 0, -1, (3 / 34 : ℚ)], ![(-9 / 17 : ℚ), 0, 0, -2, (9 / 34 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, -1, -4], ![(-21 / 10 : ℚ), 0, 0, -2, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, -1, 0, (-1 / 4 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, -1, -4], ![(-21 / 10 : ℚ), 0, 0, -2, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![0, (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 8 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, 0, 0, -1], ![(-1 / 4 : ℚ), 0, 0, (-9 / 8 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, 0, 0, -4], ![(-1 / 3 : ℚ), 0, 0, (-7 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, 0, 0, -4], ![(-1 / 3 : ℚ), 0, 0, (-7 / 6 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .yy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 1, -1], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .yy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 0, 0, (13 / 12 : ℚ), -1], ![(-1 / 3 : ℚ), 0, 0, (-5 / 6 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, 0, (9 / 8 : ℚ), -4], ![(-7 / 8 : ℚ), 0, 0, (-3 / 8 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), (4 / 3 : ℚ), (-11 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), 0, 0, (11 / 10 : ℚ), -4], ![(-7 / 20 : ℚ), 0, 0, (-17 / 20 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, -2, (11 / 8 : ℚ), 0], ![(1 / 8 : ℚ), -2, 0, (-11 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ), 0, (-10 / 3 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), 0, -2, (7 / 5 : ℚ), 0], ![(1 / 10 : ℚ), -2, 0, (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 8 : ℚ), 0, -2, (9 / 8 : ℚ), 0], ![(5 / 4 : ℚ), -2, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-4 / 5 : ℚ), (-7 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, -2, (5 / 4 : ℚ), 0], ![(3 / 2 : ℚ), -2, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, -4], ![(-3 / 2 : ℚ), 0, 0, -1, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), 0, 0, (1 / 4 : ℚ), -4], ![-1, 0, 0, (1 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), -4], ![(-9 / 5 : ℚ), 0, 0, (3 / 5 : ℚ), -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), 0, -2, (-3 / 8 : ℚ), 0], ![0, -2, 0, (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), 0, (-17 / 5 : ℚ)], ![(-8 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![(-1 / 2 : ℚ), -1, 0, 0, -2]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 13 : ℚ), 0, (-6 / 13 : ℚ), (2 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-4 / 13 : ℚ), (-1 / 13 : ℚ), (2 / 13 : ℚ), (-4 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, (1 / 4 : ℚ)], ![(-1 / 2 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), (-7 / 10 : ℚ), (3 / 10 : ℚ)], ![(-3 / 10 : ℚ), (-3 / 10 : ℚ), (-3 / 10 : ℚ), (-7 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 13 : ℚ), 0, (2 / 13 : ℚ), (-6 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-4 / 13 : ℚ), (-1 / 13 : ℚ), (-4 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), 0, 0, (1 / 4 : ℚ), -1], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-2 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 8 : ℚ), 0, 0, (1 / 2 : ℚ), -4], ![(-17 / 8 : ℚ), 0, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 4 : ℚ), 0], ![(-1 / 12 : ℚ), (-1 / 6 : ℚ), 0, (1 / 12 : ℚ), (-1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-7 / 8 : ℚ), 0], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-7 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.xx, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, -1, 0], ![(-3 / 5 : ℚ), 0, 0, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 13 : ℚ), 0, 0, (-6 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-4 / 13 : ℚ), (-1 / 13 : ℚ), (-2 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 4 : ℚ), 0, 0, (1 / 4 : ℚ), -1], ![-1, 0, 0, 0, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (-3 / 2 : ℚ)], ![(-3 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ), -2], ![(-3 / 5 : ℚ), (-4 / 5 : ℚ), (-1 / 5 : ℚ), 0, (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(13 / 8 : ℚ), 0, 0, (1 / 2 : ℚ), -4], ![(-17 / 8 : ℚ), 0, 0, 0, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ), 0], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, (1 / 6 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.xx, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, 0], ![(-1 / 2 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 24 : ℚ), (1 / 12 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ), (-7 / 24 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (1 / 24 : ℚ), 0, (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, -2, -1, 0], ![0, -1, -1, -1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 6 : ℚ), 0, (-1 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 12 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)], ![-1, 0, (-1 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 4 : ℚ), 0, -4, -2, 0], ![(-1 / 4 : ℚ), -2, -2, -2, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 15 : ℚ), (2 / 15 : ℚ), 0, (-8 / 15 : ℚ), 0], ![(-4 / 15 : ℚ), 0, (-1 / 15 : ℚ), (2 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 6 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 22 : ℚ), (1 / 22 : ℚ), 0, 0, (1 / 22 : ℚ)], ![(1 / 11 : ℚ), (-5 / 22 : ℚ), (-4 / 11 : ℚ), (1 / 22 : ℚ), (-5 / 22 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, (-3 / 20 : ℚ), 0], ![(-1 / 20 : ℚ), (-11 / 20 : ℚ), (-1 / 40 : ℚ), (1 / 20 : ℚ), (-1 / 20 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 9 : ℚ), (-1 / 3 : ℚ), 0], ![0, (-1 / 2 : ℚ), (-1 / 9 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (1 / 12 : ℚ), (-1 / 12 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (-7 / 8 : ℚ), 0], ![0, (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-7 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 7 : ℚ), 0, 0, -1, (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), 0, 0, -1, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, -1], ![(-1 / 2 : ℚ), 0, 0, -1, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 5 : ℚ), (-3 / 5 : ℚ), (1 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-2 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), 0, -2, 0, 0], ![(-1 / 3 : ℚ), -1, -1, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, 0, -1, (-9 / 4 : ℚ)], ![(-1 / 4 : ℚ), 0, 0, -1, (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 9 : ℚ), 0, -2, 0, (-4 / 3 : ℚ)], ![(-4 / 9 : ℚ), -1, -1, 0, (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, -4], ![(-1 / 2 : ℚ), 0, 0, -1, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 8 : ℚ), 0, 0, -1, (-1 / 8 : ℚ)], ![(-3 / 8 : ℚ), 0, 0, -2, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 7 : ℚ), 0, 0, -1, (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), 0, 0, -2, (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, -1, -1], ![(-3 / 2 : ℚ), 0, 0, -2, -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-15 / 17 : ℚ), (-19 / 34 : ℚ), (3 / 34 : ℚ)], ![(-3 / 34 : ℚ), (-15 / 34 : ℚ), (-15 / 34 : ℚ), (-19 / 17 : ℚ), (-3 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, -1, (-11 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, 0, -2, (-11 / 10 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 0, 0, -1, (-3 / 2 : ℚ)], ![(-1 / 6 : ℚ), 0, 0, -2, (13 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), 0, 0, -1, -4], ![(-3 / 5 : ℚ), 0, 0, -2, -4]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 14 : ℚ)], ![0, (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-15 / 14 : ℚ), (3 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-6 / 13 : ℚ)], ![(-2 / 13 : ℚ), (-2 / 13 : ℚ), (-1 / 13 : ℚ), (-14 / 13 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, 0, 0, -1], ![-1, 0, 0, (-5 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-14 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (-6 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-8 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-1 / 6 : ℚ), (-7 / 6 : ℚ), (1 / 3 : ℚ)]] }
]

theorem conicDetC16_checked : conicDetC16.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
