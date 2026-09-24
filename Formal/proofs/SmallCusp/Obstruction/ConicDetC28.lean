import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC28 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-17 / 3 : ℚ), (-11 / 6 : ℚ), -3, 0], ![(8 / 3 : ℚ), (-17 / 6 : ℚ), (-5 / 6 : ℚ), (-19 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-2 / 3 : ℚ), -4], ![0, 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-13 / 9 : ℚ), 0, (-22 / 9 : ℚ)], ![1, -1, (-17 / 9 : ℚ), 0, (-11 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-5 / 4 : ℚ), 0, -2], ![1, -1, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-5 / 3 : ℚ), 0, (-8 / 3 : ℚ)], ![1, -1, (-5 / 3 : ℚ), 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-7 / 6 : ℚ), 0, (-13 / 6 : ℚ)], ![1, -1, (-4 / 3 : ℚ), 0, (-13 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 6 : ℚ), -1, -4], ![0, 0, (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-3 / 2 : ℚ), 0, (-5 / 2 : ℚ)], ![1, -1, (-3 / 2 : ℚ), 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-5 / 4 : ℚ), -7], ![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-5 / 4 : ℚ), (-7 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-44 / 9 : ℚ), (-8 / 3 : ℚ), 0, 0], ![(20 / 9 : ℚ), (-22 / 9 : ℚ), (-28 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (-13 / 6 : ℚ), 0, 0], ![2, -2, (-7 / 3 : ℚ), (-13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -5, (-11 / 4 : ℚ), 0, 0], ![(9 / 4 : ℚ), (-11 / 4 : ℚ), (-11 / 4 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-23 / 5 : ℚ), (-11 / 5 : ℚ), (-6 / 5 : ℚ), 0], ![2, (-23 / 10 : ℚ), (-23 / 10 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (-12 / 5 : ℚ), (-7 / 5 : ℚ), 0], ![2, -2, (-14 / 5 : ℚ), (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 9 : ℚ), (-19 / 9 : ℚ), (19 / 9 : ℚ), 0, (-10 / 9 : ℚ)], ![0, (-38 / 9 : ℚ), 0, 0, (10 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, 0, 1], ![(-3 / 2 : ℚ), 0, 0, -4, -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, 0, (-7 / 3 : ℚ), 1], ![(-3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ), -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, (-13 / 6 : ℚ), 0], ![-2, 0, 0, (-13 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 6 : ℚ), (7 / 6 : ℚ), 0, 0], ![(-1 / 12 : ℚ), (-7 / 3 : ℚ), 0, (-5 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 12 : ℚ), 0, 0, (-13 / 6 : ℚ), 0], ![(-11 / 4 : ℚ), 0, 0, (-9 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 9 : ℚ), (-20 / 9 : ℚ), (19 / 9 : ℚ), 0, (-4 / 3 : ℚ)], ![(5 / 9 : ℚ), (-40 / 9 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), 0, 0, 0, (8 / 9 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, -4, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (-7 / 5 : ℚ), (11 / 10 : ℚ), (-9 / 10 : ℚ), (-2 / 5 : ℚ)], ![0, (-27 / 10 : ℚ), 0, -1, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), (-1 / 3 : ℚ), (1 / 6 : ℚ), (-11 / 6 : ℚ), 0], ![(-5 / 6 : ℚ), (-2 / 3 : ℚ), (-1 / 6 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), 0, 0, 0, (1 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, -4, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), -1, (-17 / 4 : ℚ)], ![0, 0, (-9 / 4 : ℚ), 1, (-17 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), -1, -4], ![0, 0, (-9 / 4 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-34 / 9 : ℚ), 0, (8 / 9 : ℚ), -2], ![(17 / 9 : ℚ), (-17 / 9 : ℚ), (8 / 9 : ℚ), (-8 / 9 : ℚ), (-14 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), -1, (-14 / 3 : ℚ)], ![0, 0, (-8 / 3 : ℚ), 0, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), -1, -4], ![0, 0, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 5 : ℚ), -1, (-28 / 5 : ℚ)], ![0, 0, (-14 / 5 : ℚ), 0, (-26 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, (-14 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-29 / 12 : ℚ), (5 / 6 : ℚ), (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 5 : ℚ), 0, 0, (-6 / 5 : ℚ)], ![(7 / 5 : ℚ), (-7 / 5 : ℚ), (2 / 5 : ℚ), (-3 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, (-9 / 2 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (5 / 12 : ℚ), (-53 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 34 : ℚ), 0, (-55 / 34 : ℚ), (6 / 17 : ℚ), (-71 / 17 : ℚ)], ![(-3 / 34 : ℚ), 0, (-107 / 34 : ℚ), (9 / 34 : ℚ), (-71 / 34 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-52 / 17 : ℚ), 0, (-23 / 17 : ℚ), (-16 / 17 : ℚ)], ![(26 / 17 : ℚ), (-26 / 17 : ℚ), (2 / 17 : ℚ), (-25 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 3 : ℚ), 0, (-7 / 3 : ℚ)], ![1, -1, (-1 / 3 : ℚ), 0, (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 3 : ℚ), 0, -2], ![1, -1, (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 3 : ℚ), 0, (-8 / 3 : ℚ)], ![1, -1, (-1 / 3 : ℚ), 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 2 : ℚ), 0, (-5 / 2 : ℚ)], ![1, -1, (-1 / 2 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 4 : ℚ), 0, -2], ![1, -1, (-1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 2 : ℚ), 0, -3], ![1, -1, (-1 / 2 : ℚ), 0, (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -5, 0, 0, 0], ![(9 / 4 : ℚ), (-5 / 2 : ℚ), (1 / 4 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, 0, 0, 0], ![2, -2, (1 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-26 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (4 / 5 : ℚ), -5]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-22 / 5 : ℚ), (-1 / 5 : ℚ), (-7 / 5 : ℚ), 0], ![2, (-11 / 5 : ℚ), 0, (-8 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (-1 / 4 : ℚ), (-13 / 8 : ℚ), 0], ![2, -2, (1 / 8 : ℚ), (-15 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-14 / 3 : ℚ), (-4 / 3 : ℚ), (4 / 3 : ℚ), 0], ![(7 / 3 : ℚ), (-7 / 3 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, (-28 / 5 : ℚ)], ![0, 0, 0, 0, (-26 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, -1, (-1 / 2 : ℚ), 4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-25 / 6 : ℚ), -1, 0, 0], ![2, (-25 / 12 : ℚ), (-1 / 6 : ℚ), -2, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, -1, 0, 0], ![2, -2, 0, -2, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-35 / 8 : ℚ), -1, 0, 0], ![2, (-9 / 4 : ℚ), (-1 / 8 : ℚ), -2, (1 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-41 / 8 : ℚ), (-25 / 16 : ℚ), (-29 / 16 : ℚ), 0], ![(5 / 2 : ℚ), (-41 / 16 : ℚ), (-3 / 4 : ℚ), (-15 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (1 / 2 : ℚ), -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, (1 / 3 : ℚ), 4, 2, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .x), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, (-1 / 3 : ℚ), 4, 2, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![1, (-1 / 3 : ℚ), -4, -2, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 2 : ℚ)], ![(5 / 6 : ℚ), (-1 / 6 : ℚ), (-25 / 6 : ℚ), (-13 / 6 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 0, 0], ![(13 / 6 : ℚ), 0, (-22 / 3 : ℚ), (-23 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -3], ![(2 / 3 : ℚ), (-1 / 3 : ℚ), (-13 / 3 : ℚ), (-7 / 3 : ℚ), -1]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(21 / 10 : ℚ), (-34 / 5 : ℚ), (-7 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-10 / 7 : ℚ), 0], ![(15 / 7 : ℚ), (-50 / 7 : ℚ), (-26 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(13 / 6 : ℚ), (-22 / 3 : ℚ), (-23 / 6 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), -3, -3], ![0, 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), -3, -3], ![0, 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), -3, -3], ![0, 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (6 / 5 : ℚ), 0, -3, -3], ![0, 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, -4, (-13 / 4 : ℚ)], ![0, 0, 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(11 / 10 : ℚ), (21 / 10 : ℚ), (1 / 10 : ℚ), (-24 / 5 : ℚ), (-24 / 5 : ℚ)], ![(9 / 10 : ℚ), 0, 0, 0, (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(11 / 10 : ℚ), (21 / 10 : ℚ), (1 / 5 : ℚ), (-24 / 5 : ℚ), (-24 / 5 : ℚ)], ![(9 / 10 : ℚ), 0, 0, 0, (-23 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 5 : ℚ), (21 / 10 : ℚ), (1 / 10 : ℚ), (-9 / 2 : ℚ), (-9 / 2 : ℚ)], ![(1 / 2 : ℚ), 0, 0, 0, (-11 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(4 / 3 : ℚ), 0, (-11 / 3 : ℚ), (-10 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(4 / 3 : ℚ), 0, (-11 / 3 : ℚ), (-10 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(5 / 4 : ℚ), 0, (-13 / 4 : ℚ), -3, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(4 / 3 : ℚ), 0, (-11 / 3 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (-17 / 6 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (-17 / 6 : ℚ), (-8 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-4 / 3 : ℚ), (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (-17 / 6 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(4 / 3 : ℚ), (-2 / 3 : ℚ), (-11 / 3 : ℚ), (-11 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-11 / 7 : ℚ), 0], ![(9 / 7 : ℚ), (-5 / 7 : ℚ), (-24 / 7 : ℚ), (-24 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 5 : ℚ), 0], ![(6 / 5 : ℚ), (-4 / 5 : ℚ), -3, -3, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-25 / 8 : ℚ), 0], ![(19 / 8 : ℚ), (3 / 8 : ℚ), -7, -7, (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-16 / 5 : ℚ), 0], ![(12 / 5 : ℚ), (2 / 5 : ℚ), (-36 / 5 : ℚ), (-36 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-38 / 13 : ℚ), 0], ![(30 / 13 : ℚ), (4 / 13 : ℚ), (-84 / 13 : ℚ), (-84 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 6 : ℚ), 0], ![1, 0, -4, -4, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (21 / 16 : ℚ), 0, 0, (-21 / 16 : ℚ)], ![(-5 / 16 : ℚ), (-7 / 8 : ℚ), (-11 / 8 : ℚ), (-9 / 16 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-25 / 7 : ℚ)], ![(5 / 7 : ℚ), (-19 / 28 : ℚ), (-30 / 7 : ℚ), (-101 / 28 : ℚ), (-23 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0], ![(20 / 9 : ℚ), 0, (-70 / 9 : ℚ), (-70 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-37 / 10 : ℚ)], ![(4 / 5 : ℚ), (-17 / 10 : ℚ), (-21 / 5 : ℚ), (-5 / 2 : ℚ), (-18 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), (-17 / 6 : ℚ), (-17 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 6 : ℚ), 0, (-23 / 12 : ℚ)], ![(13 / 12 : ℚ), (-29 / 12 : ℚ), (-29 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), (-17 / 6 : ℚ), (-17 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-11 / 7 : ℚ), 0, (-12 / 7 : ℚ)], ![(9 / 7 : ℚ), (-24 / 7 : ℚ), (-24 / 7 : ℚ), (2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-11 / 7 : ℚ), 0, (-12 / 7 : ℚ)], ![(9 / 7 : ℚ), (-24 / 7 : ℚ), (-24 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 7 : ℚ), 0, (-13 / 7 : ℚ)], ![(8 / 7 : ℚ), (-19 / 7 : ℚ), (-19 / 7 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), 0, (-19 / 10 : ℚ)], ![(11 / 10 : ℚ), (-5 / 2 : ℚ), (-5 / 2 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 5 : ℚ), 0, (-9 / 5 : ℚ)], ![(6 / 5 : ℚ), -3, -3, (1 / 5 : ℚ), 2]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), 0, (-19 / 10 : ℚ)], ![(11 / 10 : ℚ), (-5 / 2 : ℚ), (-5 / 2 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, 0], ![(7 / 3 : ℚ), (-20 / 3 : ℚ), (-20 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, 0], ![(7 / 3 : ℚ), (-20 / 3 : ℚ), (-20 / 3 : ℚ), (-5 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-38 / 13 : ℚ), 0, 0], ![(30 / 13 : ℚ), (-84 / 13 : ℚ), (-84 / 13 : ℚ), (-20 / 13 : ℚ), (4 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-23 / 10 : ℚ), (-13 / 10 : ℚ), 0], ![(21 / 10 : ℚ), (-34 / 5 : ℚ), (-28 / 5 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-17 / 7 : ℚ), (-10 / 7 : ℚ), 0], ![(15 / 7 : ℚ), (-50 / 7 : ℚ), (-41 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(13 / 6 : ℚ), (-22 / 3 : ℚ), (-19 / 3 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (13 / 9 : ℚ), (4 / 9 : ℚ), (-32 / 9 : ℚ), (-10 / 3 : ℚ)], ![0, 0, 0, 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 3 : ℚ), (1 / 3 : ℚ), (-19 / 6 : ℚ), -3], ![0, 0, 0, 0, -3]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (13 / 9 : ℚ), 0, (-32 / 9 : ℚ), (-10 / 3 : ℚ)], ![0, 0, 0, 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (13 / 9 : ℚ), 0, (-32 / 9 : ℚ), (-10 / 3 : ℚ)], ![0, 0, 0, 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, -4, -3], ![0, 0, 0, 0, -3]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 9 : ℚ), (20 / 9 : ℚ), (2 / 9 : ℚ), (-46 / 9 : ℚ), (-44 / 9 : ℚ)], ![(7 / 9 : ℚ), 0, 0, 0, (-44 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (13 / 9 : ℚ), (4 / 9 : ℚ), (-32 / 9 : ℚ), (-10 / 3 : ℚ)], ![0, 0, (-14 / 9 : ℚ), 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (20 / 9 : ℚ), 0, (-43 / 9 : ℚ), (-14 / 3 : ℚ)], ![(1 / 2 : ℚ), 0, 0, 0, (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-13 / 12 : ℚ)], ![(-1 / 24 : ℚ), -4, 0, 0, (9 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, (1 / 4 : ℚ)], ![(11 / 8 : ℚ), 0, -4, -2, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-9 / 5 : ℚ)], ![(-2 / 5 : ℚ), -4, 0, 0, (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![(-1 / 4 : ℚ), -4, 0, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-19 / 4 : ℚ)], ![(-1 / 4 : ℚ), -4, 0, 0, -1]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -2, (-3 / 8 : ℚ)], ![(15 / 8 : ℚ), 0, -4, -2, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-11 / 2 : ℚ)], ![(-1 / 2 : ℚ), -4, 0, 0, (-11 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-11 / 7 : ℚ), 0], ![(9 / 7 : ℚ), (-5 / 7 : ℚ), (-24 / 7 : ℚ), (-13 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 5 : ℚ), 0], ![(6 / 5 : ℚ), (-4 / 5 : ℚ), -3, (-8 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(4 / 3 : ℚ), (-2 / 3 : ℚ), (-11 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 5 : ℚ), 0], ![(11 / 5 : ℚ), (1 / 5 : ℚ), (-28 / 5 : ℚ), -3, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-20 / 7 : ℚ), 0], ![(16 / 7 : ℚ), (2 / 7 : ℚ), (-44 / 7 : ℚ), (-24 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-10 / 3 : ℚ), 0], ![(22 / 9 : ℚ), (4 / 9 : ℚ), (-68 / 9 : ℚ), (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 4 : ℚ), 0], ![1, 0, -4, -2, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-9 / 5 : ℚ), 0], ![1, (-3 / 5 : ℚ), -4, (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, -1, (-37 / 10 : ℚ)], ![(4 / 5 : ℚ), (-31 / 40 : ℚ), (-21 / 5 : ℚ), (-57 / 40 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, (-5 / 2 : ℚ), 0], ![(13 / 6 : ℚ), 0, (-22 / 3 : ℚ), (-23 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, (-8 / 3 : ℚ), 0], ![(20 / 9 : ℚ), (-13 / 9 : ℚ), (-70 / 9 : ℚ), (-8 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-21 / 8 : ℚ), (-11 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-11 / 7 : ℚ), 0, (-12 / 7 : ℚ)], ![(9 / 7 : ℚ), (-24 / 7 : ℚ), (-13 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), (-17 / 6 : ℚ), (-4 / 3 : ℚ), (1 / 6 : ℚ), (-11 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), 0, (-19 / 10 : ℚ)], ![(11 / 10 : ℚ), (-5 / 2 : ℚ), (-13 / 10 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-6 / 5 : ℚ), 0, (-19 / 10 : ℚ)], ![(11 / 10 : ℚ), (-5 / 2 : ℚ), (-13 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, (-7 / 4 : ℚ)], ![(5 / 4 : ℚ), (-13 / 4 : ℚ), (-3 / 2 : ℚ), (1 / 4 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, (-7 / 4 : ℚ)], ![(5 / 4 : ℚ), (-13 / 4 : ℚ), (-3 / 2 : ℚ), 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 2 : ℚ), (5 / 6 : ℚ), 0], ![(13 / 6 : ℚ), (-16 / 3 : ℚ), (-5 / 2 : ℚ), (5 / 6 : ℚ), (8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), (-17 / 6 : ℚ), (-4 / 3 : ℚ), 0, (-11 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 5 : ℚ), 0, 0], ![(11 / 5 : ℚ), (-28 / 5 : ℚ), -3, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-17 / 7 : ℚ), 0, 0], ![(15 / 7 : ℚ), (-36 / 7 : ℚ), (-19 / 7 : ℚ), (-5 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, 0], ![(7 / 3 : ℚ), (-20 / 3 : ℚ), -3, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-23 / 10 : ℚ), (-13 / 10 : ℚ), 0], ![(21 / 10 : ℚ), (-34 / 5 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-17 / 7 : ℚ), (-10 / 7 : ℚ), 0], ![(15 / 7 : ℚ), (-50 / 7 : ℚ), (-19 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0], ![(20 / 9 : ℚ), (-70 / 9 : ℚ), (-8 / 3 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (1 / 2 : ℚ), -1, 0, 4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, (1 / 2 : ℚ), -1, 0, 4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, 0, -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, 0, -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, (-1 / 2 : ℚ), 0, -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 4 : ℚ), (9 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (-13 / 2 : ℚ)], ![(5 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, (2 / 3 : ℚ), 0, -4], ![0, 0, (-8 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 3 : ℚ), (8 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-22 / 3 : ℚ)], ![(5 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, (1 / 3 : ℚ), (1 / 3 : ℚ), 4, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, 1, 4, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(21 / 10 : ℚ), (1 / 10 : ℚ), (-34 / 5 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-10 / 7 : ℚ), 0], ![(15 / 7 : ℚ), (1 / 7 : ℚ), (-50 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-5 / 3 : ℚ), 0], ![(20 / 9 : ℚ), (2 / 9 : ℚ), (-70 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, 0, 4, (1 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, (-1 / 3 : ℚ), 4, (1 / 3 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, (-1 / 2 : ℚ), 4, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![1, 0, -4, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, 0, 4, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, 0, 0, 0], ![-1, 0, 4, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, (5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), 0, (-13 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, -1, -5], ![0, 0, -2, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, (3 / 2 : ℚ), 0], ![(5 / 2 : ℚ), 0, -7, 0, (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, 0], ![1, -1, -4, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-16 / 7 : ℚ)], ![1, (-2 / 7 : ℚ), -4, (3 / 7 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 4 : ℚ), 0, (7 / 4 : ℚ), 0], ![(11 / 4 : ℚ), 0, (-15 / 2 : ℚ), (9 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 12 : ℚ), 0, (13 / 12 : ℚ), 0], ![(25 / 12 : ℚ), (-1 / 6 : ℚ), (-37 / 6 : ℚ), (5 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![1, (-1 / 7 : ℚ), (-29 / 7 : ℚ), -1, (-3 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -2], ![1, (-4 / 7 : ℚ), (-32 / 7 : ℚ), -1, (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-1 / 4 : ℚ), (-63 / 20 : ℚ)], ![(19 / 20 : ℚ), (-3 / 4 : ℚ), (-91 / 20 : ℚ), (-3 / 10 : ℚ), (-31 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0], ![(20 / 9 : ℚ), (-13 / 9 : ℚ), (-70 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-10 / 3 : ℚ), (-10 / 3 : ℚ)], ![(5 / 9 : ℚ), (-4 / 9 : ℚ), (-40 / 9 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, (1 / 3 : ℚ), 0], ![(7 / 3 : ℚ), (-1 / 3 : ℚ), (-23 / 3 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (-13 / 2 : ℚ), (-5 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), (-4 / 3 : ℚ), 0], ![(7 / 3 : ℚ), (-20 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(5 / 2 : ℚ), -7, (-3 / 2 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (-13 / 2 : ℚ), 0, (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), (-4 / 3 : ℚ), 0], ![(7 / 3 : ℚ), (-20 / 3 : ℚ), 0, (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(5 / 2 : ℚ), -7, 0, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (-13 / 2 : ℚ), (5 / 4 : ℚ), (-5 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (-13 / 2 : ℚ), (5 / 4 : ℚ), (-5 / 4 : ℚ), (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(5 / 2 : ℚ), -7, (3 / 2 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(21 / 10 : ℚ), (-34 / 5 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-10 / 7 : ℚ), 0], ![(15 / 7 : ℚ), (-50 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(13 / 6 : ℚ), (-22 / 3 : ℚ), (-11 / 6 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), 0, 0], ![(21 / 10 : ℚ), (-34 / 5 : ℚ), (-3 / 2 : ℚ), (1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(13 / 6 : ℚ), (-22 / 3 : ℚ), (-3 / 2 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 10 : ℚ), 0, (-1 / 10 : ℚ)], ![(21 / 10 : ℚ), (-34 / 5 : ℚ), (-3 / 2 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-8 / 5 : ℚ), 0, 0], ![(11 / 5 : ℚ), (-38 / 5 : ℚ), (-8 / 5 : ℚ), (2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, (-1 / 6 : ℚ)], ![(13 / 6 : ℚ), (-22 / 3 : ℚ), (-3 / 2 : ℚ), 0, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, (1 / 2 : ℚ), (-19 / 6 : ℚ), (-5 / 2 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-3 / 2 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, (2 / 11 : ℚ), (-36 / 11 : ℚ), (-28 / 11 : ℚ)], ![0, (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-17 / 11 : ℚ), (-28 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, (-17 / 5 : ℚ), (-13 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (5 / 4 : ℚ), 0, (-13 / 4 : ℚ), (-11 / 4 : ℚ)], ![0, 0, 0, (-3 / 2 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (5 / 6 : ℚ), 0, (-10 / 3 : ℚ), (-13 / 6 : ℚ)], ![0, (-1 / 6 : ℚ), 0, (-4 / 3 : ℚ), (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 2, (1 / 20 : ℚ), (-26 / 5 : ℚ), (-43 / 10 : ℚ)], ![1, (-1 / 10 : ℚ), 0, (-23 / 10 : ℚ), (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(21 / 20 : ℚ), (41 / 20 : ℚ), (1 / 10 : ℚ), (-53 / 10 : ℚ), (-22 / 5 : ℚ)], ![(21 / 20 : ℚ), (-1 / 10 : ℚ), 0, (-47 / 20 : ℚ), (-22 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![1, 2, 0, (-26 / 5 : ℚ), (-43 / 10 : ℚ)], ![1, (-1 / 10 : ℚ), 0, (-23 / 10 : ℚ), (-43 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 13 : ℚ), 0, (-28 / 13 : ℚ), (-28 / 13 : ℚ), (7 / 26 : ℚ)], ![(37 / 26 : ℚ), 0, (-56 / 13 : ℚ), (-29 / 13 : ℚ), (-5 / 26 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (-7 / 3 : ℚ), (-13 / 6 : ℚ), (5 / 12 : ℚ)], ![(3 / 2 : ℚ), 0, (-14 / 3 : ℚ), (-9 / 4 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-5 / 2 : ℚ), (-9 / 4 : ℚ), (3 / 4 : ℚ)], ![(7 / 4 : ℚ), 0, -5, (-9 / 4 : ℚ), (3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 2 : ℚ), (-5 / 2 : ℚ), 0], ![(5 / 4 : ℚ), 0, -5, (-11 / 4 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 13 : ℚ), 0, (-28 / 13 : ℚ), (-28 / 13 : ℚ), (-41 / 13 : ℚ)], ![(12 / 13 : ℚ), 0, (-56 / 13 : ℚ), (-29 / 13 : ℚ), (-20 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-15 / 44 : ℚ), 0, (-24 / 11 : ℚ), (-24 / 11 : ℚ), (-36 / 11 : ℚ)], ![(9 / 22 : ℚ), 0, (-48 / 11 : ℚ), (-25 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-7 / 3 : ℚ), (-13 / 6 : ℚ), (-19 / 6 : ℚ)], ![(11 / 6 : ℚ), 0, (-14 / 3 : ℚ), (-13 / 6 : ℚ), (-19 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-11 / 6 : ℚ), (-5 / 3 : ℚ), 0], ![(4 / 3 : ℚ), (-2 / 3 : ℚ), (-23 / 6 : ℚ), (-11 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 3 : ℚ), (-3 / 2 : ℚ), 0], ![(7 / 6 : ℚ), (-5 / 6 : ℚ), (-7 / 2 : ℚ), (-5 / 3 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ), (-7 / 5 : ℚ), 0], ![1, -1, (-17 / 5 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-34 / 11 : ℚ), (-30 / 11 : ℚ), 0], ![2, 0, (-72 / 11 : ℚ), (-34 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (-32 / 9 : ℚ), (-28 / 9 : ℚ), 0], ![(20 / 9 : ℚ), (2 / 9 : ℚ), (-68 / 9 : ℚ), (-32 / 9 : ℚ), (4 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-1 / 2 : ℚ), (-13 / 4 : ℚ), (-11 / 4 : ℚ), 0], ![(7 / 4 : ℚ), (-1 / 4 : ℚ), -7, (-11 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 2, (1 / 14 : ℚ), (1 / 7 : ℚ), -2], ![-1, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 7 : ℚ), 0, (-9 / 7 : ℚ), (-8 / 7 : ℚ), 0], ![(13 / 14 : ℚ), (-13 / 14 : ℚ), (-22 / 7 : ℚ), (-8 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 13 : ℚ), 2, (1 / 13 : ℚ), 0, -6], ![(-15 / 13 : ℚ), (-2 / 13 : ℚ), 0, (-2 / 13 : ℚ), (-32 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xx, .xy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-9 / 8 : ℚ), (-21 / 8 : ℚ), (-19 / 8 : ℚ), 0], ![(15 / 8 : ℚ), -1, (-11 / 2 : ℚ), (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-17 / 12 : ℚ), (-4 / 3 : ℚ), 0, (-5 / 3 : ℚ)], ![(7 / 6 : ℚ), (-35 / 12 : ℚ), (-17 / 12 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-11 / 6 : ℚ), (-5 / 3 : ℚ), 0, (-3 / 2 : ℚ)], ![(4 / 3 : ℚ), (-23 / 6 : ℚ), (-11 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-17 / 12 : ℚ), (-4 / 3 : ℚ), 0, (-19 / 12 : ℚ)], ![(7 / 6 : ℚ), (-35 / 12 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), (-19 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-4 / 3 : ℚ), (-5 / 4 : ℚ), 0, (-11 / 6 : ℚ)], ![(13 / 12 : ℚ), (-11 / 4 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 4 : ℚ), (-1 / 6 : ℚ), (-13 / 12 : ℚ), (-49 / 12 : ℚ)], ![0, (-7 / 12 : ℚ), (-1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-19 / 11 : ℚ), (-17 / 11 : ℚ), 0, (-16 / 11 : ℚ)], ![(13 / 11 : ℚ), (-40 / 11 : ℚ), (-17 / 11 : ℚ), (2 / 11 : ℚ), (-16 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-8 / 5 : ℚ), (-7 / 5 : ℚ), 0, -2], ![1, (-17 / 5 : ℚ), (-7 / 5 : ℚ), 0, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-8 / 5 : ℚ), (-7 / 5 : ℚ), 0, (-11 / 5 : ℚ)], ![1, (-17 / 5 : ℚ), (-7 / 5 : ℚ), 0, 2]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-8 / 5 : ℚ), (-7 / 5 : ℚ), 0, (-9 / 5 : ℚ)], ![1, (-17 / 5 : ℚ), (-7 / 5 : ℚ), 0, (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), (-13 / 5 : ℚ), 0, 0], ![(11 / 5 : ℚ), (-28 / 5 : ℚ), -3, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 7 : ℚ), (-17 / 7 : ℚ), 0, 0], ![(15 / 7 : ℚ), (-36 / 7 : ℚ), (-19 / 7 : ℚ), (-5 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -3, -3, 0, 0], ![(7 / 3 : ℚ), (-20 / 3 : ℚ), -3, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-28 / 11 : ℚ), (-26 / 11 : ℚ), (-15 / 11 : ℚ), 0], ![2, (-65 / 11 : ℚ), (-28 / 11 : ℚ), (-17 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-25 / 9 : ℚ), (-23 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(19 / 9 : ℚ), (-19 / 3 : ℚ), (-25 / 9 : ℚ), (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .y), (.xx, .xy), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-17 / 6 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0], ![(11 / 6 : ℚ), (-20 / 3 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 17 : ℚ), 0, 1, (9 / 17 : ℚ), (-52 / 17 : ℚ)], ![0, 0, (-3 / 17 : ℚ), (-6 / 17 : ℚ), (-26 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-2 / 5 : ℚ), 0, (1 / 20 : ℚ), (-9 / 5 : ℚ)], ![(-5 / 8 : ℚ), (-1 / 5 : ℚ), (-17 / 40 : ℚ), (-21 / 20 : ℚ), (-9 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), 0, 1, (1 / 5 : ℚ), (-16 / 5 : ℚ)], ![0, 0, (-1 / 5 : ℚ), 0, (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, (5 / 4 : ℚ), 0, -3], ![0, 0, 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 10 : ℚ), (1 / 2 : ℚ), 2, (1 / 40 : ℚ), (-43 / 10 : ℚ)], ![(1 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 20 : ℚ), 0, (-43 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), 0, 0, (1 / 18 : ℚ), (-29 / 9 : ℚ)], ![(-5 / 18 : ℚ), 0, (-7 / 9 : ℚ), (-73 / 18 : ℚ), (-29 / 18 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 10 : ℚ), (-12 / 5 : ℚ), (-3 / 10 : ℚ), (-7 / 10 : ℚ), 0], ![(-13 / 10 : ℚ), (-6 / 5 : ℚ), (-1 / 10 : ℚ), (-23 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (21 / 17 : ℚ), (1 / 34 : ℚ), -4], ![0, 0, (-3 / 34 : ℚ), (1 / 17 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-3 / 10 : ℚ), (1 / 10 : ℚ), 0], ![-2, 0, (-1 / 10 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (6 / 5 : ℚ), (3 / 10 : ℚ), -4], ![0, 0, (-1 / 10 : ℚ), (1 / 5 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-1 / 4 : ℚ), -4], ![0, 0, 0, 0, -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 2 : ℚ), 2, (1 / 12 : ℚ), -5], ![(1 / 2 : ℚ), 0, (-1 / 6 : ℚ), 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (3 / 2 : ℚ), (1 / 6 : ℚ), -4], ![0, 0, (-1 / 6 : ℚ), (-7 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (1 / 2 : ℚ), 2, (1 / 6 : ℚ), -5], ![(1 / 2 : ℚ), 0, (-1 / 6 : ℚ), 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 9 : ℚ), (4 / 3 : ℚ), 0, (1 / 9 : ℚ), (-31 / 9 : ℚ)], ![0, (-1 / 9 : ℚ), (1 / 9 : ℚ), 0, (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 12 : ℚ), 1, (1 / 4 : ℚ), (1 / 12 : ℚ), (-31 / 12 : ℚ)], ![0, (-1 / 12 : ℚ), (-1 / 6 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 5 : ℚ), (6 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), -3], ![0, 0, 0, 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 1, 0, 0, (-7 / 2 : ℚ)], ![0, 0, 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 12 : ℚ), 2, (1 / 24 : ℚ), (-1 / 4 : ℚ), (-55 / 12 : ℚ)], ![(1 / 2 : ℚ), (-1 / 12 : ℚ), 0, (1 / 3 : ℚ), (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(5 / 8 : ℚ), (49 / 24 : ℚ), (1 / 12 : ℚ), (-7 / 24 : ℚ), (-14 / 3 : ℚ)], ![(13 / 24 : ℚ), (-1 / 12 : ℚ), 0, (3 / 8 : ℚ), (-55 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (17 / 12 : ℚ), (-1 / 2 : ℚ), (1 / 3 : ℚ), (-41 / 12 : ℚ)], ![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-7 / 12 : ℚ), (-1 / 4 : ℚ), (-5 / 3 : ℚ)]] }
]

theorem conicDetC28_checked : conicDetC28.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
