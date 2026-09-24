import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC30 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 5 : ℚ), 0, 0], ![(6 / 5 : ℚ), (-4 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-4 / 3 : ℚ), 0, 0], ![1, -1, (-5 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (-5 / 4 : ℚ), 0, (-11 / 6 : ℚ)], ![(13 / 12 : ℚ), (-11 / 12 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ), (-29 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-7 / 3 : ℚ), (-1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-8 / 5 : ℚ), 0, (-7 / 5 : ℚ)], ![(6 / 5 : ℚ), (-4 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(5 / 4 : ℚ), (-3 / 4 : ℚ), (-3 / 2 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), 0, -2], ![1, -1, (-3 / 2 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-7 / 3 : ℚ), (1 / 2 : ℚ), (-1 / 6 : ℚ)], ![2, 0, (-7 / 3 : ℚ), (1 / 2 : ℚ), 3]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-13 / 5 : ℚ), 0, 0], ![(11 / 5 : ℚ), (1 / 5 : ℚ), -3, -1, (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-17 / 7 : ℚ), 0, 0], ![(15 / 7 : ℚ), (1 / 7 : ℚ), (-19 / 7 : ℚ), (-5 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, -3, 0, 0], ![(7 / 3 : ℚ), (1 / 3 : ℚ), -3, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-2 / 11 : ℚ), (-26 / 11 : ℚ), (-15 / 11 : ℚ), 0], ![2, 0, (-28 / 11 : ℚ), (-17 / 11 : ℚ), (1 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-23 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(19 / 9 : ℚ), (1 / 9 : ℚ), (-25 / 9 : ℚ), (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-32 / 11 : ℚ), 0, (4 / 11 : ℚ)], ![(24 / 11 : ℚ), (2 / 11 : ℚ), (-36 / 11 : ℚ), (4 / 11 : ℚ), (4 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-22 / 7 : ℚ), 0, 0], ![2, 0, (-22 / 7 : ℚ), (2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-1 / 3 : ℚ), (-25 / 6 : ℚ), (-13 / 6 : ℚ)], ![0, -2, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-4 / 7 : ℚ), (-24 / 7 : ℚ), 0, 0], ![(16 / 7 : ℚ), (2 / 7 : ℚ), (-24 / 7 : ℚ), (4 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 6 : ℚ), 2, 0, -2, (-4 / 3 : ℚ)], ![-1, 0, 0, 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 8 : ℚ), 2, 0, -2, (-35 / 8 : ℚ)], ![-1, 0, 0, 0, (-35 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-5 / 3 : ℚ), 0, (1 / 6 : ℚ), (-4 / 3 : ℚ)], ![(4 / 3 : ℚ), (-11 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-4 / 3 : ℚ), (-7 / 6 : ℚ), (-25 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (3 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 24 : ℚ), (-7 / 6 : ℚ), 0, 0, (-43 / 24 : ℚ)], ![(13 / 12 : ℚ), (-7 / 6 : ℚ), (1 / 24 : ℚ), (1 / 24 : ℚ), (-43 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (-9 / 5 : ℚ)], ![(11 / 10 : ℚ), (-6 / 5 : ℚ), (1 / 20 : ℚ), (1 / 10 : ℚ), (3 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-7 / 5 : ℚ), 0, (1 / 5 : ℚ), (-17 / 10 : ℚ)], ![(6 / 5 : ℚ), (-7 / 5 : ℚ), (1 / 10 : ℚ), (1 / 5 : ℚ), 2]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-9 / 5 : ℚ), 0, 0, -1], ![(7 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), 0, -1]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-11 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-11 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-5 / 4 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-15 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 6 : ℚ), 0, 0, (-13 / 6 : ℚ)], ![1, (-4 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-9 / 4 : ℚ)], ![1, (-3 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)], ![1, (-5 / 3 : ℚ), 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-19 / 11 : ℚ), 0, (-16 / 11 : ℚ), (-14 / 11 : ℚ)], ![(15 / 11 : ℚ), (-21 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-6 / 5 : ℚ), 0, (-9 / 5 : ℚ), (-7 / 4 : ℚ)], ![(11 / 10 : ℚ), (-6 / 5 : ℚ), (1 / 20 : ℚ), 0, (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 11 : ℚ), (-4 / 11 : ℚ), (-15 / 11 : ℚ), (-46 / 11 : ℚ), (-24 / 11 : ℚ)], ![0, (-6 / 11 : ℚ), (17 / 11 : ℚ), (2 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-6 / 5 : ℚ), 0, (-37 / 20 : ℚ), (-7 / 4 : ℚ)], ![(11 / 10 : ℚ), (-6 / 5 : ℚ), (1 / 20 : ℚ), (1 / 20 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-9 / 5 : ℚ), 0, -1, (-3 / 5 : ℚ)], ![(7 / 5 : ℚ), (-9 / 5 : ℚ), (1 / 5 : ℚ), -1, (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-8 / 5 : ℚ), 0, 0, (-11 / 5 : ℚ)], ![(6 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), (-6 / 5 : ℚ), (-3 / 5 : ℚ), 0, -4], ![(1 / 2 : ℚ), (-6 / 5 : ℚ), (1 / 10 : ℚ), 0, (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-13 / 10 : ℚ), 0, (1 / 10 : ℚ), (-17 / 10 : ℚ)], ![(11 / 10 : ℚ), (-13 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (-17 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, (-19 / 10 : ℚ)], ![(11 / 10 : ℚ), (-13 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-6 / 5 : ℚ), 0, 0, (-19 / 10 : ℚ)], ![(11 / 10 : ℚ), (-13 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-5 / 4 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ), (-15 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 6 : ℚ), 0, 0, (-13 / 6 : ℚ)], ![1, (-4 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), -1, 1, (-13 / 3 : ℚ)], ![0, (-2 / 3 : ℚ), 0, 1, (1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![1, (-3 / 2 : ℚ), 0, 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 12 : ℚ), (-2 / 3 : ℚ), (-13 / 12 : ℚ), (-49 / 12 : ℚ), (-7 / 2 : ℚ)], ![0, (-3 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ), (-5 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-13 / 10 : ℚ), 0, (-9 / 5 : ℚ), (-17 / 10 : ℚ)], ![(11 / 10 : ℚ), (-13 / 10 : ℚ), (1 / 10 : ℚ), 0, (-17 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 3 : ℚ), (-7 / 6 : ℚ), (-25 / 6 : ℚ), (-13 / 6 : ℚ)], ![0, (-1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), (-7 / 10 : ℚ), (-11 / 10 : ℚ), (-41 / 10 : ℚ), (-29 / 10 : ℚ)], ![0, (-7 / 10 : ℚ), (1 / 10 : ℚ), (1 / 10 : ℚ), (-29 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-8 / 5 : ℚ), 0, (-7 / 5 : ℚ), (-4 / 5 : ℚ)], ![(6 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), (-7 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-5 / 4 : ℚ), (1 / 8 : ℚ), 0, (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 4 : ℚ), 0, 0, (-15 / 8 : ℚ)], ![(9 / 8 : ℚ), (-5 / 4 : ℚ), (1 / 8 : ℚ), 0, (9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, 0, (-7 / 4 : ℚ)], ![(5 / 4 : ℚ), (-3 / 2 : ℚ), (1 / 4 : ℚ), 0, (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0, (-5 / 2 : ℚ)], ![(3 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0, (-11 / 4 : ℚ)], ![(3 / 4 : ℚ), (-5 / 4 : ℚ), 0, 0, (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-9 / 4 : ℚ), (-9 / 4 : ℚ)], ![1, (-3 / 2 : ℚ), 0, 2, 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), 0, -2, (-7 / 4 : ℚ)], ![1, (-3 / 2 : ℚ), 0, (1 / 4 : ℚ), (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-7 / 4 : ℚ), 0, (-9 / 8 : ℚ), -2], ![(3 / 2 : ℚ), (-7 / 4 : ℚ), 0, 3, (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-4 / 3 : ℚ), 0, (-13 / 6 : ℚ), (-11 / 6 : ℚ)], ![1, (-4 / 3 : ℚ), 0, 2, (-11 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-23 / 10 : ℚ), 0, (-13 / 10 : ℚ), 0], ![(21 / 10 : ℚ), (-5 / 2 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 7 : ℚ), 0, (-10 / 7 : ℚ), 0], ![(15 / 7 : ℚ), (-19 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0], ![(13 / 6 : ℚ), (-5 / 2 : ℚ), (-11 / 6 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, 0, 0], ![(11 / 5 : ℚ), -3, -1, (2 / 5 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, 0], ![(13 / 6 : ℚ), (-5 / 2 : ℚ), (-5 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, 0, (-1 / 5 : ℚ)], ![(11 / 5 : ℚ), -3, -1, (2 / 5 : ℚ), (2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -3, 0, 0, 0], ![(7 / 3 : ℚ), -3, (-5 / 3 : ℚ), (2 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx), (.yy, .xy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ)], ![(9 / 4 : ℚ), (-11 / 4 : ℚ), (-5 / 4 : ℚ), 0, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-29 / 12 : ℚ), (-17 / 12 : ℚ), 0, 0], ![(25 / 12 : ℚ), (-31 / 12 : ℚ), (-19 / 12 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-18 / 7 : ℚ), (-11 / 7 : ℚ), 0, 0], ![2, (-18 / 7 : ℚ), (-11 / 7 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), 0, (1 / 2 : ℚ), (-53 / 12 : ℚ), (-9 / 4 : ℚ)], ![(-1 / 6 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-19 / 7 : ℚ), (-12 / 7 : ℚ), 0, (4 / 7 : ℚ)], ![(15 / 7 : ℚ), (-19 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ), (4 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-19 / 8 : ℚ), (3 / 4 : ℚ), (-9 / 8 : ℚ), 0], ![(-5 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 8 : ℚ), (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 7 : ℚ), (-20 / 7 : ℚ), (3 / 7 : ℚ), (2 / 7 : ℚ), 0], ![(-11 / 7 : ℚ), (-11 / 7 : ℚ), (-2 / 7 : ℚ), (-24 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 8 : ℚ), (1 / 8 : ℚ), 2, (1 / 8 : ℚ), (-13 / 8 : ℚ)], ![(1 / 8 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-13 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), (-9 / 7 : ℚ), (3 / 14 : ℚ), (1 / 7 : ℚ), 0], ![(-9 / 7 : ℚ), (-1 / 7 : ℚ), (-1 / 7 : ℚ), (-26 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (9 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (-5 / 4 : ℚ)], ![(1 / 2 : ℚ), 0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (23 / 12 : ℚ), (1 / 6 : ℚ), (-11 / 12 : ℚ), (-11 / 12 : ℚ)], ![0, 0, (-1 / 3 : ℚ), (11 / 12 : ℚ), (-11 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (7 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-4 / 3 : ℚ)], ![(1 / 2 : ℚ), 0, 0, (4 / 3 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(3 / 8 : ℚ), (17 / 8 : ℚ), (1 / 8 : ℚ), 0, (-9 / 8 : ℚ)], ![(3 / 8 : ℚ), 0, 0, (9 / 8 : ℚ), (-9 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 1], ![(-3 / 2 : ℚ), 0, (-9 / 2 : ℚ), -1, 1]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (9 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ)], ![(1 / 2 : ℚ), 0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (4 / 3 : ℚ), 0, (-5 / 3 : ℚ), (5 / 3 : ℚ)], ![0, (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 3 : ℚ), (5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (3 / 4 : ℚ), (5 / 4 : ℚ), 0, 0], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-11 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(7 / 8 : ℚ), (17 / 8 : ℚ), (1 / 8 : ℚ), (-13 / 8 : ℚ), (-11 / 8 : ℚ)], ![(7 / 8 : ℚ), 0, 0, 0, (-11 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (5 / 4 : ℚ), (1 / 4 : ℚ), (-3 / 4 : ℚ), (-1 / 2 : ℚ)], ![0, 0, (-7 / 4 : ℚ), 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .xy), (.xy, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (17 / 8 : ℚ), 0, (-11 / 8 : ℚ), (-5 / 4 : ℚ)], ![(1 / 2 : ℚ), 0, 0, 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (19 / 9 : ℚ), (2 / 9 : ℚ), (2 / 9 : ℚ), (-14 / 9 : ℚ)], ![0, (-2 / 9 : ℚ), 0, 0, (-14 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .y), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 2, (1 / 4 : ℚ), 0, (-3 / 2 : ℚ)], ![0, (-1 / 4 : ℚ), 0, 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xx, .x), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (21 / 10 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (-3 / 2 : ℚ)], ![0, (-1 / 5 : ℚ), 0, (-1 / 10 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .yy), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (15 / 7 : ℚ), (2 / 7 : ℚ), 0, (-12 / 7 : ℚ)], ![0, (-2 / 7 : ℚ), 0, 0, (-12 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, (-2 / 13 : ℚ), (-19 / 13 : ℚ), 0], ![2, (2 / 13 : ℚ), 0, (-21 / 13 : ℚ), (1 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (-1 / 9 : ℚ), (-2 / 9 : ℚ), (-14 / 9 : ℚ), 0], ![(19 / 9 : ℚ), 0, (1 / 9 : ℚ), (-16 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), (9 / 8 : ℚ), (-9 / 8 : ℚ), 0], ![(17 / 8 : ℚ), (1 / 4 : ℚ), (-9 / 8 : ℚ), (-9 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 3 : ℚ), (4 / 3 : ℚ), (-4 / 3 : ℚ), 0], ![(7 / 3 : ℚ), (2 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (1 / 2 : ℚ), (-5 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-9 / 4 : ℚ)], ![1, -2, 0, 0, (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, -1, 1, (-25 / 6 : ℚ)], ![0, -4, 0, 1, (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (1 / 2 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), 0, (15 / 8 : ℚ), (-15 / 8 : ℚ), (-1 / 8 : ℚ)], ![(9 / 8 : ℚ), (7 / 8 : ℚ), (15 / 8 : ℚ), (-15 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 8 : ℚ), (11 / 8 : ℚ), (-11 / 8 : ℚ), 0], ![(17 / 8 : ℚ), 0, (11 / 8 : ℚ), (-11 / 8 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 8 : ℚ), 0, (-9 / 8 : ℚ), 0], ![(49 / 24 : ℚ), (1 / 4 : ℚ), (-9 / 8 : ℚ), (-9 / 8 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 10 : ℚ), 0, (-13 / 10 : ℚ), 0], ![(21 / 10 : ℚ), (3 / 5 : ℚ), (-13 / 10 : ℚ), (-13 / 10 : ℚ), (1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 16 : ℚ), 0, (-19 / 16 : ℚ), 0], ![(33 / 16 : ℚ), (3 / 8 : ℚ), (-19 / 16 : ℚ), (-19 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-1 / 13 : ℚ), (-18 / 13 : ℚ), 0, (-2 / 13 : ℚ)], ![(27 / 13 : ℚ), 0, (-20 / 13 : ℚ), (2 / 13 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-1 / 7 : ℚ), (-11 / 7 : ℚ), 0, 0], ![2, 0, (-11 / 7 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-4 / 3 : ℚ), (1 / 12 : ℚ), (-43 / 12 : ℚ), (-11 / 6 : ℚ)], ![(1 / 4 : ℚ), (-31 / 12 : ℚ), 0, (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), 0, (-12 / 7 : ℚ), 0, (2 / 7 : ℚ)], ![(15 / 7 : ℚ), (2 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), (-4 / 3 : ℚ), 0], ![(7 / 3 : ℚ), (1 / 3 : ℚ), (-4 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (1 / 4 : ℚ), (-5 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (1 / 4 : ℚ), 0, (-5 / 4 : ℚ), (1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (4 / 3 : ℚ), (-4 / 3 : ℚ), 0], ![(7 / 3 : ℚ), (1 / 3 : ℚ), 0, (-4 / 3 : ℚ), (2 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (5 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![(9 / 4 : ℚ), (1 / 4 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (7 / 6 : ℚ), (-7 / 6 : ℚ), 0], ![2, 0, (7 / 6 : ℚ), (-7 / 6 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (11 / 8 : ℚ), (-11 / 8 : ℚ), 0], ![(17 / 8 : ℚ), (1 / 8 : ℚ), (11 / 8 : ℚ), (-11 / 8 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-13 / 10 : ℚ), 0], ![(21 / 10 : ℚ), (1 / 10 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-10 / 7 : ℚ), 0], ![(15 / 7 : ℚ), (1 / 7 : ℚ), (-12 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-3 / 2 : ℚ), 0], ![(13 / 6 : ℚ), (1 / 6 : ℚ), (-11 / 6 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-17 / 12 : ℚ), 0, 0], ![(25 / 12 : ℚ), (1 / 12 : ℚ), (-19 / 12 : ℚ), (1 / 6 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-11 / 7 : ℚ), 0, 0], ![2, 0, (-11 / 7 : ℚ), (1 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 3 : ℚ), (-13 / 3 : ℚ), (-25 / 12 : ℚ)], ![0, (-3 / 2 : ℚ), (1 / 4 : ℚ), (1 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), (-12 / 7 : ℚ), 0, 0], ![(15 / 7 : ℚ), (1 / 7 : ℚ), (-12 / 7 : ℚ), (2 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 7 : ℚ), (1 / 7 : ℚ), 0], ![0, (-1 / 7 : ℚ), (-9 / 7 : ℚ), (-1 / 7 : ℚ), (5 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-9 / 8 : ℚ), 0, (1 / 4 : ℚ), (3 / 8 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 7 : ℚ), (-11 / 7 : ℚ), 0, (2 / 7 : ℚ), 0], ![(-11 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-24 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)], ![0, (-1 / 5 : ℚ), (-7 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-7 / 4 : ℚ), 0, (1 / 4 : ℚ), 0], ![(-5 / 4 : ℚ), (-3 / 4 : ℚ), 0, (-15 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), (-7 / 5 : ℚ), 0, (2 / 5 : ℚ), (-6 / 5 : ℚ)], ![(-7 / 5 : ℚ), 0, 0, (-16 / 5 : ℚ), (-3 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-4 / 3 : ℚ), 0, (2 / 3 : ℚ), (-1 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, -3, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-11 / 7 : ℚ), (2 / 7 : ℚ), (-34 / 7 : ℚ)], ![0, (-2 / 7 : ℚ), (-11 / 7 : ℚ), (-2 / 7 : ℚ), (-34 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-27 / 22 : ℚ), (-12 / 11 : ℚ), (-1 / 22 : ℚ), (3 / 11 : ℚ), (4 / 11 : ℚ)], ![(-29 / 22 : ℚ), (-1 / 11 : ℚ), 0, (-25 / 11 : ℚ), (-3 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-29 / 24 : ℚ), (-25 / 24 : ℚ), (-1 / 24 : ℚ), (1 / 3 : ℚ), (3 / 8 : ℚ)], ![(-31 / 24 : ℚ), 0, 0, (-13 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 7 : ℚ), (-9 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), (-2 / 7 : ℚ)], ![(-10 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-20 / 7 : ℚ), (-2 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 12 : ℚ), (-7 / 6 : ℚ), (-1 / 12 : ℚ), (1 / 6 : ℚ), (1 / 6 : ℚ)], ![(-19 / 12 : ℚ), (-1 / 6 : ℚ), 0, (-17 / 6 : ℚ), (-5 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-5 / 4 : ℚ), 0, (1 / 8 : ℚ), (-3 / 2 : ℚ)], ![(-5 / 4 : ℚ), 0, (1 / 8 : ℚ), (-21 / 8 : ℚ), (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 12 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ), (2 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-19 / 12 : ℚ), 0, 0, (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 7 : ℚ), (-9 / 7 : ℚ), (-1 / 7 : ℚ), (2 / 7 : ℚ), (-16 / 7 : ℚ)], ![(-10 / 7 : ℚ), (-2 / 7 : ℚ), 0, (-20 / 7 : ℚ), (-16 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-1 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-9 / 8 : ℚ), 0, 0, (3 / 8 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-5 / 3 : ℚ)], ![0, (-1 / 3 : ℚ), (-4 / 3 : ℚ), (-1 / 3 : ℚ), (-5 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-7 / 6 : ℚ), (-1 / 6 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-4 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, -3, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 3 : ℚ)], ![0, (-8 / 9 : ℚ), (-17 / 9 : ℚ), (-8 / 9 : ℚ), (-20 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (3 / 10 : ℚ), (8 / 5 : ℚ), 0], ![-2, 0, (-43 / 10 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (2 / 11 : ℚ), 0, (-50 / 11 : ℚ)], ![0, (-2 / 11 : ℚ), (-2 / 11 : ℚ), (7 / 11 : ℚ), (-50 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (1 / 4 : ℚ), (5 / 4 : ℚ), 0], ![-2, 0, (-17 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-13 / 6 : ℚ), (2 / 3 : ℚ), (11 / 6 : ℚ), 0], ![(-5 / 2 : ℚ), 0, (-14 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 7 : ℚ), (-17 / 7 : ℚ), (2 / 7 : ℚ), (6 / 7 : ℚ), 0], ![(-17 / 7 : ℚ), (-2 / 7 : ℚ), (-36 / 7 : ℚ), (6 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), -4], ![0, 0, (-1 / 2 : ℚ), (1 / 2 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-19 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (3 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (1 / 2 : ℚ), (-1 / 4 : ℚ), 0], ![-2, 0, (-49 / 12 : ℚ), (-13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 3, (1 / 2 : ℚ), (-14 / 3 : ℚ)], ![0, (-2 / 9 : ℚ), (-2 / 9 : ℚ), (1 / 2 : ℚ), (-14 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-11 / 10 : ℚ), (1 / 2 : ℚ)], ![(-6 / 5 : ℚ), (-1 / 10 : ℚ), 0, (-12 / 5 : ℚ), (-2 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-9 / 8 : ℚ), 0, -1, (3 / 8 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-5 / 4 : ℚ), 0], ![(-3 / 2 : ℚ), (-1 / 4 : ℚ), 0, -3, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-1 / 2 : ℚ), (1 / 10 : ℚ)], ![(-6 / 5 : ℚ), (-1 / 10 : ℚ), 0, (-12 / 5 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .y), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-5 / 4 : ℚ), 0, (-1 / 2 : ℚ), 0], ![(-5 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-2 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, (-7 / 2 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-5 / 4 : ℚ), 0, -1, (-1 / 4 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, (-11 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 8 : ℚ), (-19 / 8 : ℚ), (7 / 8 : ℚ), (-17 / 8 : ℚ), 0], ![(-19 / 8 : ℚ), (-1 / 4 : ℚ), (7 / 8 : ℚ), (-19 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-17 / 16 : ℚ), 0, (-9 / 8 : ℚ), (1 / 4 : ℚ)], ![(-19 / 16 : ℚ), (-1 / 16 : ℚ), 0, (-9 / 4 : ℚ), (-3 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-10 / 9 : ℚ), (-37 / 36 : ℚ), 0, (-10 / 9 : ℚ), (2 / 9 : ℚ)], ![(-7 / 6 : ℚ), 0, 0, (-20 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-7 / 4 : ℚ), 0], ![(-3 / 2 : ℚ), (-1 / 4 : ℚ), 0, (-7 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-11 / 10 : ℚ), 0, (-6 / 5 : ℚ), (1 / 10 : ℚ)], ![(-13 / 10 : ℚ), (-1 / 10 : ℚ), 0, (-12 / 5 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), (-7 / 4 : ℚ), 0, (-5 / 2 : ℚ), (-1 / 2 : ℚ)], ![(-7 / 4 : ℚ), 0, 0, -5, (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 15 : ℚ), (-17 / 15 : ℚ), 0, (-23 / 15 : ℚ), (-2 / 15 : ℚ)], ![(-9 / 5 : ℚ), 0, 0, (-46 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-3, -3, (1 / 3 : ℚ), (-11 / 3 : ℚ), 0], ![-3, (-2 / 3 : ℚ), (2 / 3 : ℚ), (-22 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ), (-9 / 4 : ℚ), (1 / 3 : ℚ)], ![(-5 / 4 : ℚ), (-1 / 12 : ℚ), 0, (-55 / 12 : ℚ), (-1 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (-23 / 10 : ℚ), (2 / 5 : ℚ)], ![(-13 / 10 : ℚ), 0, 0, (-47 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-17 / 10 : ℚ), (-17 / 10 : ℚ), (-1 / 10 : ℚ), (-23 / 10 : ℚ), (1 / 2 : ℚ)], ![(-17 / 10 : ℚ), (-1 / 10 : ℚ), 0, (-47 / 10 : ℚ), (1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ), (-11 / 4 : ℚ), -1], ![(-3 / 2 : ℚ), 0, 0, (-23 / 4 : ℚ), (-1 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-11 / 4 : ℚ), (-1 / 4 : ℚ)], ![(-7 / 4 : ℚ), 0, 0, (-23 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-13 / 5 : ℚ), (-11 / 5 : ℚ)], ![(-7 / 5 : ℚ), (-1 / 5 : ℚ), 0, (-27 / 5 : ℚ), (-11 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, -2, (8 / 5 : ℚ), 0], ![-2, 0, (-43 / 10 : ℚ), (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 17 : ℚ), (-40 / 17 : ℚ), (-36 / 17 : ℚ), (35 / 17 : ℚ), 0], ![(-40 / 17 : ℚ), (-4 / 17 : ℚ), (-80 / 17 : ℚ), (-31 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, -2, (5 / 4 : ℚ), 0], ![-2, 0, (-17 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-25 / 12 : ℚ), (-23 / 12 : ℚ), (17 / 12 : ℚ), 0], ![(-9 / 4 : ℚ), 0, (-13 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-5 / 4 : ℚ), (-5 / 8 : ℚ), 0, (-15 / 8 : ℚ)], ![(-5 / 4 : ℚ), (-1 / 8 : ℚ), (-5 / 2 : ℚ), 0, (-15 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, 0, (1 / 4 : ℚ), 0], ![-2, 0, (-17 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (-19 / 4 : ℚ)], ![0, (-1 / 4 : ℚ), 0, (3 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, -2, (-3 / 5 : ℚ), 0], ![-2, 0, (-21 / 5 : ℚ), (-6 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-5 / 2 : ℚ), (-7 / 6 : ℚ), (-3 / 2 : ℚ), 0], ![(-5 / 2 : ℚ), (-1 / 3 : ℚ), -5, (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 10 : ℚ), (-11 / 10 : ℚ), 0, (-11 / 10 : ℚ), (1 / 4 : ℚ)], ![(-11 / 10 : ℚ), (-1 / 20 : ℚ), 0, (-11 / 10 : ℚ), (-1 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-9 / 8 : ℚ), 0, (-5 / 4 : ℚ), (3 / 8 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-6 / 5 : ℚ), 0, (-6 / 5 : ℚ), (1 / 10 : ℚ)], ![(-6 / 5 : ℚ), (-1 / 10 : ℚ), 0, (-6 / 5 : ℚ), (-3 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-9 / 8 : ℚ), 0, (-5 / 4 : ℚ), (-7 / 4 : ℚ)], ![(-9 / 8 : ℚ), 0, 0, (-5 / 4 : ℚ), (-7 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-5 / 3 : ℚ), (-1 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(23 / 40 : ℚ), (1 / 2 : ℚ), (-23 / 10 : ℚ), (3 / 40 : ℚ), (-51 / 40 : ℚ)], ![(1 / 2 : ℚ), (-3 / 40 : ℚ), (-181 / 40 : ℚ), 0, (27 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), (-41 / 40 : ℚ), (-1 / 40 : ℚ), (-17 / 8 : ℚ), (9 / 40 : ℚ)], ![(-47 / 40 : ℚ), 0, 0, (-87 / 40 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(9 / 16 : ℚ), (1 / 2 : ℚ), (-9 / 4 : ℚ), (1 / 16 : ℚ), (1 / 16 : ℚ)], ![(1 / 2 : ℚ), (-1 / 16 : ℚ), (-71 / 16 : ℚ), 0, (23 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-33 / 17 : ℚ), (-33 / 17 : ℚ), (-3 / 17 : ℚ), (-49 / 17 : ℚ), (-2 / 17 : ℚ)], ![(-33 / 17 : ℚ), 0, 0, (-55 / 17 : ℚ), (-1 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-27 / 17 : ℚ), (-19 / 17 : ℚ), (-2 / 17 : ℚ), (-44 / 17 : ℚ), (-2 / 17 : ℚ)], ![(-31 / 17 : ℚ), 0, 0, (-48 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-18 / 13 : ℚ), (-15 / 13 : ℚ), (-3 / 13 : ℚ), (-31 / 13 : ℚ), (8 / 13 : ℚ)], ![(-20 / 13 : ℚ), (-2 / 13 : ℚ), 0, (-33 / 13 : ℚ), (-6 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 5 : ℚ), (-6 / 5 : ℚ), (-1 / 5 : ℚ), (-12 / 5 : ℚ), (4 / 5 : ℚ)], ![(-8 / 5 : ℚ), 0, 0, (-13 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-2 / 5 : ℚ), (-14 / 5 : ℚ), 0], ![-2, 0, 0, (-16 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 2 : ℚ), (-1 / 4 : ℚ)], ![(-7 / 4 : ℚ), 0, 0, (-11 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-9 / 5 : ℚ), (11 / 5 : ℚ), 0], ![-2, 0, (-13 / 5 : ℚ), (-8 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-40 / 17 : ℚ), (-40 / 17 : ℚ), (-40 / 17 : ℚ), (35 / 17 : ℚ), 0], ![(-40 / 17 : ℚ), (-4 / 17 : ℚ), (-40 / 17 : ℚ), (-31 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-3 / 4 : ℚ), (5 / 4 : ℚ), 0], ![-2, 0, (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-13 / 6 : ℚ), (-5 / 2 : ℚ), (11 / 6 : ℚ), 0], ![(-5 / 2 : ℚ), 0, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-3 / 8 : ℚ), (1 / 8 : ℚ), 0], ![-2, 0, (-17 / 8 : ℚ), (-9 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 8 : ℚ), (-19 / 8 : ℚ), (-19 / 8 : ℚ), (1 / 4 : ℚ), 0], ![(-19 / 8 : ℚ), (-1 / 4 : ℚ), (-19 / 8 : ℚ), (-13 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-1 / 2 : ℚ), (-1 / 2 : ℚ), 0], ![-2, 0, (-13 / 6 : ℚ), (-7 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, 1, (-2 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, (-5 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-7 / 6 : ℚ), 0, (1 / 2 : ℚ), (-1 / 6 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-39 / 20 : ℚ), (-37 / 20 : ℚ), 0, 1, (-9 / 20 : ℚ)], ![(-39 / 20 : ℚ), (-1 / 20 : ℚ), 0, (-19 / 20 : ℚ), (-9 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 3 : ℚ), (-5 / 3 : ℚ), 0, (5 / 6 : ℚ), (-2 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, 0, (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-9 / 8 : ℚ), 0, (3 / 8 : ℚ), (-1 / 8 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-5 / 4 : ℚ), 0, (3 / 4 : ℚ), (-7 / 4 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, 0, (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-9 / 8 : ℚ), (1 / 8 : ℚ), -4], ![0, 0, (-9 / 8 : ℚ), (3 / 8 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-9 / 8 : ℚ), 0, (1 / 8 : ℚ), (-1 / 8 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, (-1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-6 / 5 : ℚ), 0, (1 / 10 : ℚ), (-19 / 10 : ℚ)], ![(-6 / 5 : ℚ), (-1 / 10 : ℚ), 0, (-3 / 10 : ℚ), (-19 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (1 / 4 : ℚ), (-5 / 4 : ℚ), 0], ![-2, 0, (1 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-7 / 6 : ℚ), 0, (-1 / 3 : ℚ), (-1 / 6 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, (-1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 11 : ℚ), (-8 / 11 : ℚ), (-23 / 22 : ℚ), 0, (-28 / 11 : ℚ)], ![(-8 / 11 : ℚ), 0, (-43 / 22 : ℚ), (3 / 22 : ℚ), (-14 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-43 / 28 : ℚ), (-31 / 28 : ℚ), (-3 / 28 : ℚ), (33 / 28 : ℚ), (-3 / 28 : ℚ)], ![(-7 / 4 : ℚ), 0, 0, (-9 / 28 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-48 / 17 : ℚ), (-40 / 17 : ℚ), (50 / 51 : ℚ), (35 / 17 : ℚ), 0], ![(-48 / 17 : ℚ), (-4 / 17 : ℚ), (112 / 51 : ℚ), (-31 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (1 / 6 : ℚ), (7 / 6 : ℚ), 0], ![-2, 0, (1 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (1 / 10 : ℚ), (-7 / 5 : ℚ), (-2 / 5 : ℚ), (-11 / 4 : ℚ)], ![0, 0, (-27 / 10 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 2 : ℚ), (-13 / 6 : ℚ), (5 / 6 : ℚ), (11 / 6 : ℚ), 0], ![(-5 / 2 : ℚ), 0, 2, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (1 / 3 : ℚ), (1 / 12 : ℚ), 0], ![-2, 0, (3 / 4 : ℚ), (-13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-33 / 28 : ℚ), (-29 / 28 : ℚ), (-1 / 28 : ℚ), (1 / 7 : ℚ), (-1 / 28 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, (-3 / 28 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-49 / 22 : ℚ), (-47 / 22 : ℚ), (1 / 2 : ℚ), (1 / 11 : ℚ), 0], ![(-49 / 22 : ℚ), (-1 / 11 : ℚ), (12 / 11 : ℚ), (-27 / 22 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-1 / 17 : ℚ), (-25 / 17 : ℚ), 0], ![-2, 0, (1 / 17 : ℚ), (-28 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-27 / 17 : ℚ), (-19 / 17 : ℚ), (-2 / 17 : ℚ), (-27 / 17 : ℚ), (-2 / 17 : ℚ)], ![(-31 / 17 : ℚ), 0, 0, (-31 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-1 / 12 : ℚ), (7 / 6 : ℚ), 0], ![-2, 0, (1 / 3 : ℚ), (-13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-13 / 12 : ℚ), (-1 / 12 : ℚ), (1 / 3 : ℚ), (-1 / 12 : ℚ)], ![(-5 / 4 : ℚ), 0, 0, (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 7 : ℚ), (-6 / 7 : ℚ), (-1 / 14 : ℚ), (1 / 14 : ℚ), (-5 / 2 : ℚ)], ![(-6 / 7 : ℚ), (-1 / 14 : ℚ), (-2 / 7 : ℚ), 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-1 / 8 : ℚ), (9 / 8 : ℚ), 0], ![-2, 0, (1 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-11 / 10 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ), (-1 / 10 : ℚ)], ![(-13 / 10 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 8 : ℚ), (-17 / 8 : ℚ), (-1 / 4 : ℚ), (13 / 8 : ℚ), 0], ![(-19 / 8 : ℚ), 0, (7 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-5 / 3 : ℚ), (1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-13 / 12 : ℚ), 0, 0, (-1 / 12 : ℚ)], ![(-7 / 6 : ℚ), 0, 0, (-1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -5], ![0, (-1 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ), -5]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, -2, (-1 / 10 : ℚ), (-6 / 5 : ℚ), 0], ![-2, 0, 0, (-13 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ)], ![(-7 / 4 : ℚ), 0, 0, (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 10 : ℚ), (-8 / 5 : ℚ), (3 / 10 : ℚ), 0], ![0, 0, (-8 / 5 : ℚ), 0, (3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 14 : ℚ), (-8 / 7 : ℚ), (1 / 14 : ℚ), 0], ![0, 0, (-8 / 7 : ℚ), 0, (3 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-5 / 2 : ℚ), 0, (1 / 2 : ℚ), 0], ![(-4 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (-19 / 16 : ℚ), (1 / 8 : ℚ), (1 / 8 : ℚ)], ![(-1 / 16 : ℚ), (-1 / 16 : ℚ), (-19 / 16 : ℚ), (-1 / 8 : ℚ), (7 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .zero), (.xy, .yy)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-7 / 3 : ℚ), 0, (1 / 3 : ℚ), 0], ![(-4 / 3 : ℚ), (-4 / 3 : ℚ), 0, (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 4 : ℚ), (-5 / 4 : ℚ), (5 / 8 : ℚ), (-11 / 4 : ℚ)], ![0, (1 / 8 : ℚ), (-5 / 4 : ℚ), (1 / 2 : ℚ), (-11 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 14 : ℚ), 0, (-17 / 14 : ℚ), (2 / 7 : ℚ), (-10 / 7 : ℚ)], ![(-1 / 14 : ℚ), (-1 / 14 : ℚ), (-17 / 14 : ℚ), 0, (8 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), (-13 / 3 : ℚ), (5 / 12 : ℚ), (1 / 2 : ℚ), 0], ![(-9 / 4 : ℚ), (-9 / 4 : ℚ), (5 / 12 : ℚ), (-25 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-53 / 48 : ℚ), (-7 / 3 : ℚ), (-1 / 48 : ℚ), (25 / 24 : ℚ), (31 / 144 : ℚ)], ![(-55 / 48 : ℚ), (-19 / 16 : ℚ), 0, (-11 / 6 : ℚ), (-25 / 144 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 12 : ℚ), (-34 / 15 : ℚ), (-1 / 60 : ℚ), (11 / 10 : ℚ), (1 / 4 : ℚ)], ![(-67 / 60 : ℚ), (-23 / 20 : ℚ), 0, (-26 / 15 : ℚ), (1 / 30 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), (-8 / 3 : ℚ), 0, (2 / 3 : ℚ), 0], ![(-13 / 9 : ℚ), (-13 / 9 : ℚ), (2 / 9 : ℚ), (-22 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-46 / 15 : ℚ), (-1 / 15 : ℚ), (2 / 15 : ℚ), (2 / 15 : ℚ)], ![(-22 / 15 : ℚ), (-8 / 5 : ℚ), 0, (-46 / 15 : ℚ), (-8 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-26 / 17 : ℚ), (-52 / 17 : ℚ), 0, (3 / 17 : ℚ), (2 / 17 : ℚ)], ![(-29 / 17 : ℚ), (-26 / 17 : ℚ), (3 / 17 : ℚ), (-52 / 17 : ℚ), (1 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 13 : ℚ), (-44 / 13 : ℚ), 0, (10 / 39 : ℚ), 0], ![(-21 / 13 : ℚ), (-23 / 13 : ℚ), (2 / 13 : ℚ), (-10 / 3 : ℚ), (2 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), (-8 / 3 : ℚ), 0, (2 / 3 : ℚ), (-16 / 9 : ℚ)], ![(-13 / 9 : ℚ), (-13 / 9 : ℚ), (2 / 9 : ℚ), (-22 / 9 : ℚ), (-16 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-4 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-1 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), 0, 0, 0, (-3 / 20 : ℚ)], ![(-3 / 20 : ℚ), (-1 / 20 : ℚ), (-21 / 20 : ℚ), (-1 / 5 : ℚ), (1 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 6 : ℚ), 0, 0, (-4 / 3 : ℚ)], ![0, 0, (-7 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 3 : ℚ)], ![(-13 / 36 : ℚ), 0, (-10 / 9 : ℚ), (-1 / 9 : ℚ), (-7 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-20 / 7 : ℚ)], ![(-2 / 7 : ℚ), (-1 / 7 : ℚ), (-9 / 7 : ℚ), (-2 / 7 : ℚ), (2 / 7 : ℚ)]] }
]

theorem conicDetC30_checked : conicDetC30.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
