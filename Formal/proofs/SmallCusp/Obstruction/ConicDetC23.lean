import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC23 : List RationalConicRecord := [
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), (4 / 9 : ℚ), (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (16 / 35 : ℚ), (16 / 35 : ℚ), (16 / 35 : ℚ), 0], ![(-2 / 35 : ℚ), (-12 / 7 : ℚ), (-46 / 35 : ℚ), (-46 / 35 : ℚ), (8 / 35 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-14 / 37 : ℚ), (12 / 37 : ℚ), (12 / 37 : ℚ), 0, 0], ![(2 / 37 : ℚ), -4, -2, (-28 / 37 : ℚ), (6 / 37 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, (1 / 4 : ℚ), 0, -1], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), -2, (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 9 : ℚ), (8 / 9 : ℚ), 0, (-4 / 3 : ℚ)], ![(-8 / 9 : ℚ), -4, -2, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), 0, 0], ![(1 / 4 : ℚ), (-3 / 2 : ℚ), -1, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0], ![(1 / 2 : ℚ), -2, (-3 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 16 : ℚ), (1 / 2 : ℚ), 0, 0, 0], ![(3 / 16 : ℚ), (-11 / 8 : ℚ), (-17 / 16 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), (-8 / 27 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ)], ![0, (-16 / 9 : ℚ), (-28 / 27 : ℚ), (4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), (-8 / 5 : ℚ), (-12 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), 0, (-8 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, (-16 / 9 : ℚ), (-4 / 3 : ℚ), (4 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-173 / 292 : ℚ), (6 / 73 : ℚ), (-257 / 584 : ℚ), 0, 0], ![(149 / 292 : ℚ), (-197 / 146 : ℚ), (-781 / 584 : ℚ), (149 / 146 : ℚ), (3 / 73 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 5 : ℚ), (2 / 5 : ℚ), (-43 / 25 : ℚ), (11 / 25 : ℚ), 0], ![(39 / 25 : ℚ), (-106 / 25 : ℚ), (-92 / 25 : ℚ), (17 / 25 : ℚ), (72 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, (-2 / 3 : ℚ), (-7 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-2 / 9 : ℚ), (-5 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (12 / 25 : ℚ), 0, (12 / 25 : ℚ), (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-24 / 25 : ℚ), (-12 / 25 : ℚ), (-24 / 25 : ℚ), (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 9 : ℚ), (4 / 9 : ℚ), 0, (4 / 9 : ℚ), 0], ![(4 / 9 : ℚ), (-8 / 3 : ℚ), (-8 / 3 : ℚ), (-16 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 35 : ℚ), 0, (16 / 35 : ℚ), (-4 / 5 : ℚ)], ![(-16 / 35 : ℚ), (-32 / 35 : ℚ), (-16 / 35 : ℚ), (-32 / 35 : ℚ), (-4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, 0, -1], ![(-3 / 7 : ℚ), (-17 / 7 : ℚ), -2, (-3 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, (3 / 2 : ℚ), 0, -3], ![(-5 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, 0, (-4 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-26 / 9 : ℚ), (-26 / 9 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (8 / 11 : ℚ), 0, 0, 0], ![(4 / 11 : ℚ), (-24 / 11 : ℚ), (-16 / 11 : ℚ), 0, (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -1], ![0, -1, (-1 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (-1 / 8 : ℚ), 0, (-1 / 8 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 8 : ℚ), 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 7 : ℚ), (2 / 7 : ℚ), 0, (-8 / 7 : ℚ), (-12 / 7 : ℚ)], ![(-4 / 7 : ℚ), 0, (-2 / 7 : ℚ), (2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (-2 / 3 : ℚ), -1], ![(-1 / 3 : ℚ), 0, 0, (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 10 : ℚ), (2 / 5 : ℚ), (-3 / 10 : ℚ), (-9 / 10 : ℚ), 0], ![(-1 / 10 : ℚ), (-7 / 5 : ℚ), (-3 / 10 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (1 / 6 : ℚ), (-9 / 4 : ℚ), (25 / 12 : ℚ), 0], ![(25 / 12 : ℚ), (-29 / 6 : ℚ), (-9 / 4 : ℚ), (25 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, (-1 / 6 : ℚ), (-5 / 2 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 3 : ℚ), 0, (-1 / 6 : ℚ), 2]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), 0, (-2 / 3 : ℚ), -1], ![(-2 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-2 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (12 / 25 : ℚ), 0, (12 / 25 : ℚ), (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-24 / 25 : ℚ), (-12 / 25 : ℚ), (-24 / 25 : ℚ), (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), 0, (4 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 17 : ℚ), 0, (8 / 17 : ℚ), (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-16 / 17 : ℚ), 0, (-16 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, 0, -1], ![(-3 / 7 : ℚ), (-17 / 7 : ℚ), (-3 / 7 : ℚ), (-3 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, (1 / 8 : ℚ), 0, -1], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, 0, (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 7 : ℚ), (4 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (-16 / 7 : ℚ)], ![(-4 / 7 : ℚ), 0, (12 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ)], ![0, (-8 / 7 : ℚ), (8 / 7 : ℚ), (4 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), (4 / 7 : ℚ), 0, 0, (-2 / 7 : ℚ)], ![(8 / 7 : ℚ), (-24 / 7 : ℚ), 0, (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 5 : ℚ), (3 / 5 : ℚ), 0, 0, (-3 / 5 : ℚ)], ![(4 / 5 : ℚ), (-14 / 5 : ℚ), 0, 1, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 6 : ℚ), (1 / 6 : ℚ), 0, (1 / 6 : ℚ), 0], ![(11 / 6 : ℚ), -4, 0, (1 / 3 : ℚ), (7 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 3 : ℚ), (2 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (-11 / 6 : ℚ)], ![(-2 / 3 : ℚ), 0, (4 / 3 : ℚ), (-2 / 3 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 7 : ℚ), (8 / 7 : ℚ), (4 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), (-8 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (16 / 31 : ℚ), (32 / 31 : ℚ), (16 / 31 : ℚ), (-12 / 31 : ℚ)], ![0, (-32 / 31 : ℚ), (-32 / 31 : ℚ), (-32 / 31 : ℚ), (-4 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (4 / 11 : ℚ), (6 / 11 : ℚ), 0, 0], ![(2 / 11 : ℚ), -4, (-6 / 11 : ℚ), (-8 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), (9 / 4 : ℚ), (1 / 4 : ℚ), 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, 0], ![(1 / 4 : ℚ), (-3 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, (-3 / 8 : ℚ), (-1 / 2 : ℚ)], ![0, -1, 0, (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), (3 / 28 : ℚ), (-1 / 4 : ℚ), (-12 / 7 : ℚ), (-3 / 28 : ℚ)], ![(-1 / 28 : ℚ), (-5 / 14 : ℚ), (3 / 28 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-22 / 9 : ℚ)], ![0, (-16 / 9 : ℚ), (4 / 9 : ℚ), 0, 2]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 9 : ℚ), (-4 / 3 : ℚ), (-8 / 9 : ℚ), (-7 / 9 : ℚ)], ![(-4 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ), 0, (-5 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, -1], ![0, -1, 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (1 / 2 : ℚ), (1 / 16 : ℚ), 0, (-1 / 4 : ℚ)], ![(1 / 16 : ℚ), (-9 / 8 : ℚ), 0, (-1 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, 0, (-1 / 2 : ℚ)], ![0, (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, 0, -1], ![0, (-5 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, 0, (-1 / 4 : ℚ)], ![0, (-5 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (4 / 9 : ℚ), (-8 / 9 : ℚ), (-4 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, (-16 / 9 : ℚ), (4 / 9 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 9 : ℚ), (4 / 9 : ℚ), (-16 / 9 : ℚ), (-28 / 9 : ℚ), (-16 / 9 : ℚ)], ![(-8 / 9 : ℚ), 0, (4 / 9 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 8 : ℚ), (1 / 4 : ℚ), 0, (15 / 8 : ℚ), 0], ![(15 / 8 : ℚ), (-17 / 4 : ℚ), (-15 / 8 : ℚ), (15 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), 0, 0, (-1 / 2 : ℚ)], ![0, -1, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (3 / 2 : ℚ), 0, 0, (-11 / 8 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 2 : ℚ), 0, 0, (5 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 2 : ℚ), 0, 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (3 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-5 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ), (-17 / 14 : ℚ), (-3 / 14 : ℚ)], ![(-1 / 7 : ℚ), (-6 / 7 : ℚ), 0, (11 / 14 : ℚ), (-1 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 7 : ℚ), (-6 / 7 : ℚ), -1, (-6 / 7 : ℚ)], ![(-4 / 7 : ℚ), (-8 / 7 : ℚ), (-2 / 7 : ℚ), (-5 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 7 : ℚ), (3 / 7 : ℚ), 0, -1], ![(-3 / 7 : ℚ), -4, (-6 / 7 : ℚ), (-3 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (8 / 17 : ℚ), (8 / 17 : ℚ), 0, (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), -4, (-16 / 17 : ℚ), 0, (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (3 / 7 : ℚ), (3 / 7 : ℚ), 0, 0], ![(1 / 14 : ℚ), (-13 / 7 : ℚ), (-19 / 14 : ℚ), (3 / 14 : ℚ), (3 / 14 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ), (5 / 11 : ℚ), 0], ![(2 / 11 : ℚ), (-20 / 11 : ℚ), (-14 / 11 : ℚ), (7 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 16 : ℚ), (3 / 4 : ℚ), (-9 / 16 : ℚ), (-5 / 8 : ℚ), 0], ![(-3 / 16 : ℚ), (-41 / 8 : ℚ), (-9 / 16 : ℚ), (1 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, 0, (-3 / 4 : ℚ), (-1 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-5 / 2 : ℚ), 0, (-3 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, 0, 0, (-3 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 2 : ℚ), 0, 0, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (3 / 20 : ℚ), (3 / 40 : ℚ), (-7 / 20 : ℚ), (-3 / 5 : ℚ)], ![(-1 / 5 : ℚ), (9 / 40 : ℚ), 0, (3 / 40 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-6 / 5 : ℚ), (-3 / 5 : ℚ)], ![(-2 / 5 : ℚ), (-2 / 5 : ℚ), 0, (2 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (-2 / 3 : ℚ), (-10 / 3 : ℚ)], ![(-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), 0, (-2 / 3 : ℚ), -1], ![(-2 / 3 : ℚ), (-1 / 3 : ℚ), 0, (-2 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (12 / 25 : ℚ), (-28 / 25 : ℚ)], ![(-12 / 25 : ℚ), (-12 / 25 : ℚ), (-12 / 25 : ℚ), (-24 / 25 : ℚ), (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 17 : ℚ), 0, (8 / 17 : ℚ), (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-4 / 17 : ℚ), 0, (-16 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 46 : ℚ), (-1 / 46 : ℚ), (56 / 69 : ℚ), (-15 / 23 : ℚ)], ![(-21 / 46 : ℚ), 0, (-3 / 46 : ℚ), (-55 / 138 : ℚ), (-7 / 23 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 3 : ℚ)], ![(-8 / 9 : ℚ), (-26 / 9 : ℚ), 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 7 : ℚ), (-8 / 7 : ℚ), 0, 0, (-4 / 7 : ℚ)], ![(8 / 7 : ℚ), (-20 / 7 : ℚ), 0, (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-8 / 7 : ℚ), (-8 / 7 : ℚ), (-4 / 7 : ℚ)], ![0, (-4 / 7 : ℚ), (8 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 16 : ℚ), (-31 / 48 : ℚ), (-5 / 32 : ℚ)], ![0, (-1 / 16 : ℚ), (1 / 16 : ℚ), (7 / 12 : ℚ), (3 / 32 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), (-1 / 2 : ℚ), (-3 / 8 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 2 : ℚ), 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(32 / 31 : ℚ), 0, 0, (16 / 31 : ℚ), (-76 / 31 : ℚ)], ![(-32 / 31 : ℚ), (-16 / 31 : ℚ), 0, 0, (-68 / 31 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(8 / 9 : ℚ), (19 / 9 : ℚ), 0, (4 / 9 : ℚ), (-20 / 9 : ℚ)], ![(-8 / 9 : ℚ), (-1 / 3 : ℚ), 0, (4 / 9 : ℚ), (-20 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 8 : ℚ), (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, (-1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, (-23 / 25 : ℚ), (7 / 25 : ℚ), (23 / 75 : ℚ), 0], ![(19 / 25 : ℚ), (-52 / 25 : ℚ), (6 / 25 : ℚ), (91 / 75 : ℚ), (3 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 25 : ℚ), 0, (-32 / 25 : ℚ), (-14 / 25 : ℚ), (-4 / 5 : ℚ)], ![(-8 / 25 : ℚ), (-12 / 25 : ℚ), (12 / 25 : ℚ), (-2 / 25 : ℚ), 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 2 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-3 / 8 : ℚ)], ![0, (-1 / 2 : ℚ), 0, 0, (-1 / 8 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, 0, (-1 / 2 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, 0, (-1 / 4 : ℚ)], ![0, (-3 / 2 : ℚ), 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(2 / 25 : ℚ), (6 / 25 : ℚ), (-38 / 25 : ℚ), (-44 / 25 : ℚ), (-4 / 5 : ℚ)], ![(-14 / 25 : ℚ), 0, (12 / 25 : ℚ), 0, (-8 / 25 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 8 : ℚ)], ![0, (-1 / 8 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), 0, 0, 0, -2], ![(-1 / 2 : ℚ), -2, 0, 0, 0]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (7 / 8 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)], ![(-1 / 2 : ℚ), (-7 / 8 : ℚ), (-1 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), 0, (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ)], ![0, (-12 / 11 : ℚ), (2 / 11 : ℚ), 0, (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, (2 / 17 : ℚ), 2, (-71 / 17 : ℚ)], ![(-123 / 34 : ℚ), (-2 / 17 : ℚ), (9 / 34 : ℚ), 2, (-71 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 11 : ℚ), (-7 / 11 : ℚ), (-6 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-8 / 11 : ℚ), (-5 / 11 : ℚ), (-2 / 11 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 3 : ℚ), (1 / 3 : ℚ), (7 / 3 : ℚ), (-17 / 3 : ℚ), -3], ![-3, 0, (7 / 3 : ℚ), (-17 / 3 : ℚ), -3]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .xy), (.xx, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .xy), (.xx, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-3 / 5 : ℚ), (-4 / 5 : ℚ), (1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (-3 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .xy), (.xx, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (8 / 17 : ℚ), (-12 / 17 : ℚ)], ![(-8 / 17 : ℚ), 0, 0, (-16 / 17 : ℚ), (-12 / 17 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-2 / 9 : ℚ), (-8 / 9 : ℚ), (-8 / 9 : ℚ), (-2 / 9 : ℚ)], ![0, (-2 / 9 : ℚ), (8 / 9 : ℚ), (4 / 9 : ℚ), (-2 / 9 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (-1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (1 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-2 / 5 : ℚ), (-4 / 5 : ℚ), 0, (1 / 5 : ℚ)], ![0, (-2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.zero, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, 1, (1 / 3 : ℚ), -4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![1, -1, (1 / 3 : ℚ), 4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![1, -1, (-1 / 3 : ℚ), 4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, 1, (-1 / 3 : ℚ), -4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (-2 / 7 : ℚ), (-30 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, 0, -5, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (-2 / 7 : ℚ), (-30 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (-30 / 7 : ℚ), (-2 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (-9 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, -5, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (2 / 3 : ℚ), (-8 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (2 / 3 : ℚ), (-8 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 1, (-7 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (2 / 3 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (1 / 3 : ℚ), -3, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (2 / 3 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (2 / 3 : ℚ), (-8 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (2 / 3 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 0, -3, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (1 / 3 : ℚ), (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 0, -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 0, -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 0, -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 1, 0], ![1, -1, 0, 2, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, 0, -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, -1, (-5 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, -1, (-8 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, -1, (-7 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![-2, 2, 0, (-9 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![-2, 2, 0, (-9 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![-2, 2, 0, (-9 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, 0, -1], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, -1, -3, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (-11 / 28 : ℚ), (-15 / 4 : ℚ), (-13 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, 0, -5, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (-7 / 10 : ℚ), (-37 / 10 : ℚ), (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-9 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-9 / 4 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-7 / 3 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-8 / 3 : ℚ), (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-8 / 3 : ℚ), (2 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-8 / 3 : ℚ), (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-7 / 3 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-7 / 3 : ℚ), (1 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-7 / 3 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![-2, 2, (-17 / 4 : ℚ), (-1 / 4 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![-2, 2, (-9 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![-2, 2, (-9 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, -1, 0], ![-2, 2, -5, (-9 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, -1, 0], ![-2, 2, -5, (-3 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, -1, 0], ![-2, 2, (-17 / 3 : ℚ), -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (1 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (1 / 3 : ℚ), (-4 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 1, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (1 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, (1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (1 / 3 : ℚ), (-4 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -4], ![0, 0, (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, 1, -1, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 0, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 0, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, 0, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 1, 0], ![1, -1, 1, 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 1, 0], ![1, -1, (1 / 6 : ℚ), (1 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 1, 2], ![1, -1, 1, 1, 2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, -1, (-5 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, -1, (-4 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![-2, 2, 0, (-18 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, 0], ![-2, 2, 0, (-5 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, 0], ![-1, 1, -1, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, (-7 / 20 : ℚ), (-37 / 20 : ℚ), (-9 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, 0, -4], ![0, 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, -2], ![-1, 1, -1, -1, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-7 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-7 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, -1, (1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-4 / 3 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, (-7 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, -1, (1 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, -1, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, 0, -2], ![-1, 1, -1, 0, 3]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![-2, 2, (-18 / 7 : ℚ), (-4 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![-2, 2, (-5 / 2 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, 0, 0], ![-2, 2, -2, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, -1, 0], ![-2, 2, (-16 / 7 : ℚ), (-9 / 7 : ℚ), (1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -2, -1, 0], ![-2, 2, (-9 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, 0], ![-2, 2, (5 / 9 : ℚ), (-11 / 9 : ℚ), (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (1 / 6 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, 0], ![-2, 2, 1, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, 0], ![-2, 2, 1, -1, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, -1, 1, 0], ![2, -2, -1, 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, -1, (-1 / 7 : ℚ), (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, -1, (-1 / 2 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 1, -1, 0], ![2, -2, 0, 2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (-1 / 4 : ℚ), (1 / 2 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, 0, 1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (-1 / 6 : ℚ), (1 / 6 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (-2 / 7 : ℚ), -1, (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (-4 / 7 : ℚ), -1, (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, (-1 / 2 : ℚ), (-1 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, 0, -1, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![-1, 1, -1, 0, -2]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 6 : ℚ), (1 / 6 : ℚ)], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (7 / 4 : ℚ), (1 / 4 : ℚ)], ![-1, -1, 0, (-3 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)], ![-1, -1, 0, -2, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -1, (1 / 6 : ℚ), (1 / 6 : ℚ)], ![0, 0, -2, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (1 / 4 : ℚ), 0], ![-1, -1, 0, -2, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (11 / 6 : ℚ), 0], ![-1, -1, 0, (-1 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, (2 / 3 : ℚ), (-2 / 3 : ℚ)], ![-1, -1, 0, -2, (-2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), 0, 0, 0], ![(-3 / 8 : ℚ), (-3 / 8 : ℚ), (-7 / 8 : ℚ), (-5 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 4 : ℚ)], ![(-1 / 8 : ℚ), 0, (-9 / 8 : ℚ), (-1 / 8 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-23 / 10 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), -3]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), -1, 0, (1 / 5 : ℚ), (3 / 5 : ℚ)], ![(-6 / 5 : ℚ), -1, (-1 / 5 : ℚ), (-24 / 5 : ℚ), (3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 13 : ℚ), (-5 / 13 : ℚ), 0, (1 / 13 : ℚ), (-22 / 13 : ℚ)], ![(-14 / 13 : ℚ), (-37 / 52 : ℚ), (-19 / 52 : ℚ), (-53 / 13 : ℚ), (-21 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), 0, (1 / 2 : ℚ), (1 / 8 : ℚ), (-19 / 8 : ℚ)], ![(-5 / 8 : ℚ), 0, (-5 / 8 : ℚ), (-25 / 8 : ℚ), (-19 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, (1 / 4 : ℚ)], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, (1 / 2 : ℚ)], ![-1, -1, 0, -2, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 4 : ℚ), 0], ![(-3 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, (1 / 6 : ℚ)], ![-1, -1, 0, -2, 0]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (5 / 6 : ℚ), (1 / 6 : ℚ), (5 / 6 : ℚ), 0], ![(5 / 6 : ℚ), (5 / 6 : ℚ), (1 / 3 : ℚ), (5 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, 0], ![-1, -1, 0, -2, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, 0], ![-1, -1, 0, -2, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, -1, (-1 / 2 : ℚ)], ![-1, -1, 0, -2, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 10 : ℚ), 0, 0, -1], ![0, (1 / 10 : ℚ), -2, (-1 / 5 : ℚ), (6 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 8 : ℚ), 0, 0, -1], ![0, (1 / 4 : ℚ), -2, (-1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), 0, 0, -1], ![0, (1 / 4 : ℚ), -2, (-1 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (17 / 18 : ℚ), 0, 0, -4], ![0, (8 / 9 : ℚ), -2, (-1 / 18 : ℚ), (-11 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .zero), (.x, .y), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (2 / 3 : ℚ), 0, 0, -4], ![0, (1 / 3 : ℚ), -2, (-1 / 3 : ℚ), (1 / 3 : ℚ)]] }
]

theorem conicDetC23_checked : conicDetC23.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
