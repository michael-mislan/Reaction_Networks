import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

def conicDetC27 : List RationalConicRecord := [
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-33 / 17 : ℚ), 0, (-2 / 17 : ℚ), (-27 / 17 : ℚ), (-2 / 17 : ℚ)], ![(-33 / 17 : ℚ), (33 / 17 : ℚ), 0, (-31 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), -1, -4], ![0, 0, (-3 / 2 : ℚ), 1, -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 8 : ℚ), -1, -4], ![0, 0, (-5 / 4 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), -1, (-17 / 4 : ℚ)], ![0, 0, (-3 / 2 : ℚ), 1, (-17 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 6 : ℚ), -1, -4], ![0, 0, (-4 / 3 : ℚ), 0, -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, (-1 / 6 : ℚ), 1, 0], ![-2, 2, (1 / 6 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 3 : ℚ), -1, (-13 / 3 : ℚ)], ![0, 0, (-5 / 3 : ℚ), 0, (-13 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-5 / 3 : ℚ), (1 / 3 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -4], ![0, 0, (-5 / 3 : ℚ), (1 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, -5], ![0, (-1 / 3 : ℚ), (-4 / 3 : ℚ), (2 / 3 : ℚ), -5]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 20 : ℚ), (3 / 20 : ℚ), -4], ![0, 0, (-5 / 4 : ℚ), (1 / 10 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), (3 / 8 : ℚ), -4], ![0, 0, (-15 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, -4], ![0, 0, 0, 0, -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, -1, -5], ![0, 0, 0, 0, -5]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := -1
    multiplier := ![![0, 0, -1, 0, 4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, -1, 0, 0], ![-2, 2, (-1 / 3 : ℚ), -2, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-2, 0, -1, 0, 0], ![-2, 2, 0, -2, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 4 : ℚ), 0, -1, 0, 0], ![(-9 / 4 : ℚ), 2, (-1 / 4 : ℚ), -2, 0]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (7 / 8 : ℚ), (3 / 8 : ℚ), -4], ![0, 0, (-1 / 2 : ℚ), (1 / 4 : ℚ), -2]] },
  { network := { reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (1 / 2 : ℚ), -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, 0, 1, (-1 / 6 : ℚ)], ![(-4 / 3 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-1 / 4 : ℚ)], ![(-7 / 4 : ℚ), 0, 0, (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (2 / 5 : ℚ), (-1 / 10 : ℚ)], ![(-13 / 10 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), 1, 0, -4], ![0, (-7 / 6 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-11 / 4 : ℚ), (-1 / 4 : ℚ)], ![(-7 / 4 : ℚ), 0, 0, (-23 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-1 / 3 : ℚ), 0, (-1 / 3 : ℚ)], ![(-5 / 3 : ℚ), 0, 0, -5, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 4 : ℚ), (-1 / 8 : ℚ)], ![(-15 / 8 : ℚ), 0, 0, (-19 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, -1], ![0, 0, (-9 / 4 : ℚ), (-1 / 4 : ℚ), 1]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(4 / 3 : ℚ), 0, (1 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, (-11 / 8 : ℚ)], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 4 : ℚ), (-1 / 8 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), 0, 0], ![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-9 / 4 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, (-19 / 3 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-8 / 3 : ℚ), (-1 / 3 : ℚ), -3]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (1 / 6 : ℚ), (-17 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, (-31 / 6 : ℚ)], ![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (-8 / 3 : ℚ), (-1 / 3 : ℚ), -5]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, 0], ![1, 0, (-1 / 2 : ℚ), (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 3 : ℚ), 0, 0, 0], ![(4 / 3 : ℚ), 0, (1 / 3 : ℚ), (-11 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-7 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-124 / 17 : ℚ)], ![(-8 / 17 : ℚ), (-8 / 17 : ℚ), (-25 / 17 : ℚ), (-8 / 17 : ℚ), (-58 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-10 / 3 : ℚ), 0, 0, 0], ![(22 / 9 : ℚ), 0, (4 / 9 : ℚ), (-68 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-34 / 5 : ℚ)], ![(-4 / 5 : ℚ), (-4 / 5 : ℚ), (-9 / 5 : ℚ), (-4 / 5 : ℚ), (-32 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 1, 0, -1], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-17 / 14 : ℚ), 0, 0, 0], ![1, (-1 / 14 : ℚ), (-1 / 14 : ℚ), -4, (1 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-32 / 9 : ℚ), (-5 / 3 : ℚ), 0, 0], ![(20 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (-70 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 9 : ℚ), (5 / 9 : ℚ), 0, (-40 / 9 : ℚ)], ![0, 0, 0, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-25 / 9 : ℚ), (-5 / 3 : ℚ), 0, 0], ![(20 / 9 : ℚ), (-4 / 9 : ℚ), (-4 / 9 : ℚ), (-70 / 9 : ℚ), (2 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-19 / 5 : ℚ)], ![1, 0, (-13 / 5 : ℚ), 0, (-8 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-5 / 2 : ℚ)], ![1, 0, (-5 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, 0, 0, (-11 / 4 : ℚ)], ![1, 0, (-5 / 2 : ℚ), 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (-17 / 6 : ℚ), 0, (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ), (-13 / 3 : ℚ)], ![0, 0, -1, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, (-11 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (-17 / 6 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-7 / 4 : ℚ), (-25 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-3 / 2 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-4 / 3 : ℚ), 0, 0, (-23 / 6 : ℚ)], ![(7 / 6 : ℚ), 0, (-17 / 6 : ℚ), (1 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, (-1 / 4 : ℚ), (-15 / 8 : ℚ)], ![(5 / 4 : ℚ), (-1 / 4 : ℚ), (-13 / 4 : ℚ), 0, (-7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, 0], ![(13 / 6 : ℚ), 0, (-16 / 3 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (1 / 2 : ℚ), (-9 / 2 : ℚ)], ![(-1 / 14 : ℚ), (-1 / 14 : ℚ), (-97 / 28 : ℚ), (3 / 7 : ℚ), (-31 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0], ![(13 / 6 : ℚ), 0, (-22 / 3 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-8 / 3 : ℚ), 0, (-5 / 3 : ℚ), 0], ![(20 / 9 : ℚ), (-4 / 9 : ℚ), (-70 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 6 : ℚ), 0, (4 / 3 : ℚ), (-1 / 3 : ℚ), (-19 / 6 : ℚ)], ![0, (-4 / 3 : ℚ), 0, (1 / 3 : ℚ), (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 14 : ℚ), 0, 0, 0, (-25 / 14 : ℚ)], ![(-19 / 28 : ℚ), (-5 / 7 : ℚ), (-11 / 28 : ℚ), (-15 / 14 : ℚ), (-6 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), (5 / 6 : ℚ), 0, (-17 / 6 : ℚ)], ![(-1 / 6 : ℚ), (-4 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (2 / 3 : ℚ), (-1 / 6 : ℚ)], ![(-3 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 6 : ℚ), (1 / 3 : ℚ), 0, (-23 / 6 : ℚ)], ![0, (-7 / 6 : ℚ), (-2 / 3 : ℚ), 0, (-11 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(19 / 14 : ℚ), (-9 / 28 : ℚ), (12 / 7 : ℚ), (1 / 28 : ℚ), (-87 / 14 : ℚ)], ![(9 / 7 : ℚ), (-11 / 4 : ℚ), (-9 / 14 : ℚ), 0, (-43 / 14 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 12 : ℚ), 0, 0, 0, (-31 / 12 : ℚ)], ![(-1 / 2 : ℚ), (-2 / 3 : ℚ), (-7 / 12 : ℚ), (-49 / 12 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), (-1 / 12 : ℚ), (-1 / 4 : ℚ), (-13 / 6 : ℚ), (-7 / 12 : ℚ)], ![(-5 / 4 : ℚ), 0, (-1 / 12 : ℚ), (-9 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 4 : ℚ), (-5 / 2 : ℚ), 0, (-7 / 4 : ℚ)], ![(-3 / 4 : ℚ), 0, -5, 0, (7 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 9 : ℚ), (1 / 9 : ℚ), (-13 / 9 : ℚ), 0, (-17 / 9 : ℚ)], ![(-2 / 3 : ℚ), 0, (-26 / 9 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), (1 / 6 : ℚ), (-4 / 3 : ℚ), 0, (-5 / 3 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 6 : ℚ), (-8 / 3 : ℚ), 0, (-3 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 0, (-3 / 2 : ℚ), 0], ![(5 / 4 : ℚ), (-3 / 4 : ℚ), 0, -3, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), (-9 / 4 : ℚ), 0, (-9 / 4 : ℚ), -3], ![(1 / 2 : ℚ), (-1 / 2 : ℚ), 0, (-9 / 2 : ℚ), (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 15 : ℚ), (-14 / 5 : ℚ), (23 / 15 : ℚ), (-58 / 15 : ℚ), 0], ![(34 / 15 : ℚ), 0, (46 / 15 : ℚ), (-116 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 7 : ℚ), (-11 / 7 : ℚ), 0, (-15 / 7 : ℚ), (-20 / 7 : ℚ)], ![(3 / 7 : ℚ), (-4 / 7 : ℚ), 0, (-30 / 7 : ℚ), (-18 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-3 / 17 : ℚ), (-32 / 17 : ℚ), 0], ![1, 0, (-11 / 17 : ℚ), (-67 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-8 / 5 : ℚ), (-1 / 10 : ℚ), (-23 / 10 : ℚ), (2 / 5 : ℚ)], ![(3 / 2 : ℚ), 0, 0, (-47 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-1 / 6 : ℚ), 0, (-3 / 2 : ℚ)], ![(-1 / 2 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), 0, (-3 / 40 : ℚ), (-33 / 20 : ℚ), (-181 / 40 : ℚ)], ![(-33 / 40 : ℚ), (-3 / 40 : ℚ), (-43 / 40 : ℚ), (-27 / 8 : ℚ), (-89 / 40 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (-46 / 17 : ℚ), (-8 / 17 : ℚ), (-62 / 17 : ℚ), 0], ![(38 / 17 : ℚ), 0, (4 / 17 : ℚ), (-132 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 11 : ℚ), 0, (-4 / 11 : ℚ), (-8 / 11 : ℚ), (-58 / 11 : ℚ)], ![(-4 / 11 : ℚ), (-4 / 11 : ℚ), (-26 / 11 : ℚ), (-20 / 11 : ℚ), (-56 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 7 : ℚ), (-2 / 7 : ℚ), 1, (-6 / 7 : ℚ), -1], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 12 : ℚ), (-17 / 15 : ℚ), (3 / 5 : ℚ), (-37 / 30 : ℚ), (-19 / 60 : ℚ)], ![(1 / 3 : ℚ), (-1 / 15 : ℚ), (-1 / 3 : ℚ), (-38 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-116 / 111 : ℚ), (-112 / 111 : ℚ), 0, (-250 / 111 : ℚ), (-346 / 111 : ℚ)], ![0, (-6 / 37 : ℚ), (-6 / 37 : ℚ), (-14 / 3 : ℚ), (-164 / 111 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 9 : ℚ), (-4 / 9 : ℚ), (5 / 9 : ℚ), (-4 / 3 : ℚ), (-40 / 9 : ℚ)], ![0, 0, 0, (-10 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 12 : ℚ), (-5 / 2 : ℚ), (-1 / 2 : ℚ), (-10 / 3 : ℚ), (-1 / 6 : ℚ)], ![(7 / 6 : ℚ), (-1 / 3 : ℚ), (-1 / 3 : ℚ), -7, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-17 / 11 : ℚ), 0, (-40 / 11 : ℚ)], ![1, 0, (-40 / 11 : ℚ), 0, (-17 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 5 : ℚ), -1, (-23 / 5 : ℚ)], ![0, 0, (-9 / 5 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-11 / 7 : ℚ), 0, (-20 / 7 : ℚ)], ![1, 0, (-26 / 7 : ℚ), 0, (-18 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 20 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-11 / 10 : ℚ), (-15 / 4 : ℚ)], ![0, 0, (-17 / 10 : ℚ), 0, (-13 / 10 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-3 / 5 : ℚ), (-6 / 5 : ℚ), (-21 / 5 : ℚ)], ![0, 0, (-7 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 20 : ℚ), (-4 / 5 : ℚ), (-4 / 5 : ℚ), (-11 / 10 : ℚ), (-17 / 5 : ℚ)], ![0, 0, (-17 / 10 : ℚ), 0, (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), (-17 / 13 : ℚ), (-16 / 13 : ℚ), (-3 / 13 : ℚ), (-40 / 13 : ℚ)], ![(10 / 13 : ℚ), (-2 / 13 : ℚ), (-34 / 13 : ℚ), 0, (-15 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 12 : ℚ), (-2 / 3 : ℚ), (-5 / 4 : ℚ), (-1 / 2 : ℚ), (-59 / 12 : ℚ)], ![0, 0, (-31 / 12 : ℚ), (-5 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), (-19 / 16 : ℚ), (-21 / 16 : ℚ), 0, (-59 / 32 : ℚ)], ![(9 / 8 : ℚ), (-1 / 16 : ℚ), (-43 / 16 : ℚ), (1 / 16 : ℚ), (-29 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0], ![(13 / 6 : ℚ), 0, (-16 / 3 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-4 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 42 : ℚ), (-13 / 6 : ℚ), (-38 / 21 : ℚ), (-11 / 14 : ℚ), (-11 / 21 : ℚ)], ![(73 / 42 : ℚ), (-1 / 14 : ℚ), (-30 / 7 : ℚ), (-47 / 42 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-1 / 8 : ℚ), (-3 / 8 : ℚ), (3 / 4 : ℚ), (-33 / 8 : ℚ)], ![0, 0, (-9 / 8 : ℚ), (1 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-35 / 16 : ℚ), (-39 / 16 : ℚ), (-21 / 16 : ℚ), 0], ![(33 / 16 : ℚ), (-1 / 8 : ℚ), (-47 / 8 : ℚ), (-21 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 3 : ℚ), 0, 1, 0, (-8 / 3 : ℚ)], ![(-2 / 3 : ℚ), -1, 0, 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), 0, (-5 / 2 : ℚ)], ![0, (-7 / 6 : ℚ), (-2 / 3 : ℚ), (-2 / 3 : ℚ), (-5 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), (-1 / 8 : ℚ), (-1 / 8 : ℚ), (3 / 8 : ℚ), 0], ![(-5 / 4 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 4 : ℚ), (1 / 2 : ℚ), 0, (-29 / 4 : ℚ)], ![0, (-11 / 4 : ℚ), -3, (-1 / 4 : ℚ), (-29 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-10 / 3 : ℚ)], ![0, (-13 / 9 : ℚ), (-13 / 9 : ℚ), (-40 / 9 : ℚ), (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, (-35 / 16 : ℚ), 1], ![2, 0, (1 / 16 : ℚ), (-9 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ), (1 / 5 : ℚ), (-9 / 5 : ℚ)], ![(-3 / 5 : ℚ), 0, (-27 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (1 / 2 : ℚ), (-23 / 10 : ℚ), 0, 0], ![(-3 / 5 : ℚ), (-1 / 10 : ℚ), (-9 / 2 : ℚ), (-1 / 10 : ℚ), (7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-35 / 16 : ℚ), (-1 / 16 : ℚ), (-37 / 16 : ℚ), (-5 / 2 : ℚ)], ![(33 / 16 : ℚ), (-5 / 8 : ℚ), 0, (-39 / 16 : ℚ), (-19 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), (8 / 17 : ℚ), (-66 / 17 : ℚ), (8 / 17 : ℚ), (-128 / 17 : ℚ)], ![(-24 / 17 : ℚ), 0, (-124 / 17 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 10 : ℚ), (-7 / 5 : ℚ), 0], ![1, 0, (-4 / 5 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 10 : ℚ), (-6 / 5 : ℚ), (-1 / 10 : ℚ), (-9 / 5 : ℚ), 0], ![(11 / 10 : ℚ), 0, (-2 / 5 : ℚ), (-19 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), 0, (-1 / 4 : ℚ), (-1 / 4 : ℚ), (-23 / 4 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-9 / 4 : ℚ), (-1 / 2 : ℚ), (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-19 / 8 : ℚ), (-1 / 4 : ℚ), (-21 / 8 : ℚ), 0], ![(17 / 8 : ℚ), 0, (1 / 8 : ℚ), (-23 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 1, (-2 / 3 : ℚ), -1], ![0, 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 3 : ℚ), (-5 / 3 : ℚ), (1 / 3 : ℚ), (-5 / 2 : ℚ), (-11 / 6 : ℚ)], ![0, (-1 / 6 : ℚ), (-1 / 6 : ℚ), (-8 / 3 : ℚ), (-5 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), (2 / 3 : ℚ), (-2 / 3 : ℚ), (-13 / 3 : ℚ)], ![0, 0, 0, (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-4 / 3 : ℚ), 0, -3], ![1, 0, (-5 / 3 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 4 : ℚ), -1, (-17 / 4 : ℚ)], ![0, 0, (-1 / 2 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-5 / 3 : ℚ), 0, (-8 / 3 : ℚ)], ![1, 0, (-5 / 3 : ℚ), 0, (-8 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), (-7 / 10 : ℚ), (-7 / 10 : ℚ), (-11 / 10 : ℚ), (-7 / 2 : ℚ)], ![0, 0, (-4 / 5 : ℚ), 0, (-7 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-2 / 5 : ℚ), (-6 / 5 : ℚ), (-21 / 5 : ℚ)], ![0, 0, (-3 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-17 / 8 : ℚ), (-19 / 8 : ℚ), (5 / 8 : ℚ), 0], ![(15 / 8 : ℚ), 0, (-19 / 8 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-3 / 2 : ℚ), (-3 / 2 : ℚ), 0, (-7 / 2 : ℚ)], ![1, (-1 / 4 : ℚ), (-3 / 2 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-7 / 2 : ℚ), (-23 / 6 : ℚ), (13 / 6 : ℚ), 0], ![(19 / 6 : ℚ), 0, (-23 / 6 : ℚ), (13 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0], ![(13 / 6 : ℚ), 0, (-17 / 6 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), (-5 / 2 : ℚ), 0, 0], ![(13 / 6 : ℚ), (-1 / 3 : ℚ), (-5 / 2 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 12 : ℚ), (-1 / 12 : ℚ), 0, (1 / 2 : ℚ), (-53 / 12 : ℚ)], ![(-5 / 24 : ℚ), (-1 / 12 : ℚ), (-1 / 12 : ℚ), (5 / 12 : ℚ), (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-1 / 2 : ℚ), (1 / 2 : ℚ), (-17 / 4 : ℚ)], ![0, 0, (-3 / 4 : ℚ), (1 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 4 : ℚ), 0, (25 / 12 : ℚ), 0, (-13 / 12 : ℚ)], ![0, (-25 / 12 : ℚ), 0, (-1 / 12 : ℚ), (13 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 4 : ℚ), 0, 0, 0, 1], ![(-3 / 2 : ℚ), 0, 0, (-17 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), 0, (9 / 4 : ℚ), 0, (-5 / 4 : ℚ)], ![(1 / 4 : ℚ), (-9 / 4 : ℚ), 0, (-1 / 4 : ℚ), (5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-23 / 10 : ℚ), (2 / 5 : ℚ)], ![(-13 / 10 : ℚ), 0, 0, (-47 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![-1, 0, 0, 0, (1 / 2 : ℚ)], ![(-5 / 4 : ℚ), (-1 / 4 : ℚ), 0, (-17 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-6 / 5 : ℚ), (-1 / 10 : ℚ), (-1 / 10 : ℚ), (-11 / 5 : ℚ), (9 / 10 : ℚ)], ![(-9 / 5 : ℚ), 0, 0, (-23 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 10 : ℚ), (13 / 10 : ℚ), 0, (-9 / 5 : ℚ)], ![0, (-23 / 10 : ℚ), (-7 / 5 : ℚ), (-1 / 10 : ℚ), (-9 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (1 / 2 : ℚ), 0, (-1 / 3 : ℚ)], ![0, (-7 / 6 : ℚ), (-2 / 3 : ℚ), (-19 / 6 : ℚ), (-1 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), (3 / 5 : ℚ), (8 / 5 : ℚ), (-3 / 5 : ℚ)], ![(13 / 5 : ℚ), 0, (9 / 5 : ℚ), (-8 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 4 : ℚ), -1, (-17 / 4 : ℚ)], ![0, 0, (-9 / 4 : ℚ), 1, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 4 : ℚ), 0, (-19 / 8 : ℚ)], ![1, 0, (-1 / 4 : ℚ), 0, (-9 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-7 / 5 : ℚ), 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-12 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-11 / 8 : ℚ), (-1 / 8 : ℚ), 0, -2], ![(9 / 8 : ℚ), 0, 0, (-5 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, (-39 / 8 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 2 : ℚ), (3 / 4 : ℚ), (-19 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 16 : ℚ), 0, (-7 / 2 : ℚ), (7 / 16 : ℚ), (-71 / 16 : ℚ)], ![(-1 / 16 : ℚ), (-1 / 16 : ℚ), (-81 / 16 : ℚ), (3 / 8 : ℚ), (-35 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 17 : ℚ), (-28 / 17 : ℚ), (-1 / 17 : ℚ), (-22 / 17 : ℚ), (-18 / 17 : ℚ)], ![(26 / 17 : ℚ), 0, 0, (-24 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 3 : ℚ), 0, -3], ![1, 0, (-1 / 3 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 3 : ℚ), 0, (-7 / 3 : ℚ)], ![1, 0, (-1 / 3 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -1, (-1 / 3 : ℚ), 0, (-5 / 2 : ℚ)], ![1, 0, (-1 / 3 : ℚ), 0, (-7 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-27 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-6 / 5 : ℚ), (4 / 5 : ℚ), (-13 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-5 / 2 : ℚ), 0, 0, 0], ![(13 / 6 : ℚ), 0, (1 / 6 : ℚ), (-11 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-66 / 13 : ℚ)], ![(-4 / 13 : ℚ), (-4 / 13 : ℚ), (-17 / 13 : ℚ), (9 / 13 : ℚ), (-64 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 13 : ℚ), 0, (-2 / 13 : ℚ), (16 / 13 : ℚ), (-66 / 13 : ℚ)], ![(-7 / 13 : ℚ), (-2 / 13 : ℚ), (-33 / 13 : ℚ), 1, (-32 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .xy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 8 : ℚ), (-35 / 16 : ℚ), (-1 / 8 : ℚ), (-21 / 16 : ℚ), 0], ![(33 / 16 : ℚ), 0, (1 / 16 : ℚ), (-23 / 16 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-25 / 9 : ℚ), -1, 0, 0], ![2, (-2 / 9 : ℚ), (-2 / 9 : ℚ), -2, (1 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-1 / 2 : ℚ), 1, 0, -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-25 / 11 : ℚ), (-5 / 11 : ℚ), 0, (-12 / 11 : ℚ)], ![(16 / 11 : ℚ), (-2 / 11 : ℚ), (-2 / 11 : ℚ), (-16 / 11 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-13 / 9 : ℚ), (-8 / 9 : ℚ), (4 / 9 : ℚ), (-1 / 2 : ℚ), (-47 / 18 : ℚ)], ![0, (-1 / 18 : ℚ), (-1 / 18 : ℚ), (-5 / 9 : ℚ), (-23 / 18 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 3 : ℚ), (-1 / 3 : ℚ), 1, (1 / 3 : ℚ), -4], ![0, 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 15 : ℚ), 0, 0, 1, (-2 / 15 : ℚ)], ![(-9 / 5 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 15 : ℚ), 0, 0, 0, (-2 / 15 : ℚ)], ![(-9 / 5 : ℚ), 0, 0, -1, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-27 / 17 : ℚ), (-2 / 17 : ℚ), (-2 / 17 : ℚ), (-27 / 17 : ℚ), (-2 / 17 : ℚ)], ![(-31 / 17 : ℚ), 0, 0, (-31 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 10 : ℚ), (-7 / 5 : ℚ), (11 / 10 : ℚ), (-2 / 5 : ℚ), (-11 / 4 : ℚ)], ![0, (-27 / 10 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .xx), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-3 / 2 : ℚ), 1, 0, -4], ![0, (-5 / 2 : ℚ), 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 15 : ℚ), 0, (-2 / 15 : ℚ), (-34 / 15 : ℚ), (-2 / 15 : ℚ)], ![(-9 / 5 : ℚ), 0, 0, (-68 / 15 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(4 / 15 : ℚ), (-9 / 5 : ℚ), (9 / 5 : ℚ), 0, (-56 / 15 : ℚ)], ![0, (-18 / 5 : ℚ), 0, (-2 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-105 / 68 : ℚ), (-1 / 17 : ℚ), (-1 / 17 : ℚ), (-39 / 17 : ℚ), (-1 / 17 : ℚ)], ![(-65 / 34 : ℚ), 0, 0, (-41 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-11 / 7 : ℚ), 0, -1], ![0, 0, (-18 / 7 : ℚ), (-2 / 7 : ℚ), 1]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-22 / 7 : ℚ), 0, 0, (4 / 7 : ℚ)], ![(11 / 7 : ℚ), (-11 / 7 : ℚ), (4 / 7 : ℚ), (-24 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-23 / 17 : ℚ), 0, (-31 / 17 : ℚ)], ![(-2 / 17 : ℚ), (-2 / 17 : ℚ), (-40 / 17 : ℚ), (-2 / 17 : ℚ), (-27 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-3 / 2 : ℚ), 0, 0], ![(-1 / 6 : ℚ), (-1 / 6 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ), (5 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, (-44 / 9 : ℚ)], ![(-2 / 9 : ℚ), 0, (-23 / 9 : ℚ), (-2 / 9 : ℚ), (-22 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-22 / 7 : ℚ), 0, 0, (-6 / 7 : ℚ)], ![(11 / 7 : ℚ), (-11 / 7 : ℚ), (4 / 7 : ℚ), (-24 / 7 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-5 / 3 : ℚ), 0, (-16 / 3 : ℚ)], ![(-2 / 9 : ℚ), (-2 / 9 : ℚ), (-26 / 9 : ℚ), (-2 / 9 : ℚ), (-46 / 9 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![1, -1, (-1 / 3 : ℚ), (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![1, -1, (-1 / 3 : ℚ), (-7 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-31 / 17 : ℚ)], ![(-2 / 17 : ℚ), (-2 / 17 : ℚ), (-19 / 17 : ℚ), (-2 / 17 : ℚ), (-27 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -5, 0, 0, 0], ![(9 / 4 : ℚ), (-5 / 2 : ℚ), (1 / 4 : ℚ), (-21 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, 0, 0, 0], ![2, -2, (1 / 4 : ℚ), (-17 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-11 / 2 : ℚ)], ![(-1 / 4 : ℚ), (-1 / 4 : ℚ), (-5 / 4 : ℚ), (-1 / 4 : ℚ), (-21 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .zero), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, 0], ![1, -1, 0, -4, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .zero), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-44 / 15 : ℚ), 0, 0, 0], ![1, (-23 / 15 : ℚ), (-2 / 15 : ℚ), -4, (2 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-44 / 9 : ℚ), (-5 / 3 : ℚ), 0, 0], ![(20 / 9 : ℚ), (-22 / 9 : ℚ), (-4 / 9 : ℚ), (-70 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, -1, 0, 0], ![2, -2, 0, -7, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-56 / 11 : ℚ), (-19 / 11 : ℚ), 0, 0], ![(26 / 11 : ℚ), (-30 / 11 : ℚ), (-4 / 11 : ℚ), (-86 / 11 : ℚ), (2 / 11 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-5 / 2 : ℚ)], ![1, -1, (-9 / 4 : ℚ), 0, (-5 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, -2], ![1, -1, (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-34 / 9 : ℚ)], ![1, -1, (-22 / 9 : ℚ), 0, (-10 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-8 / 3 : ℚ)], ![1, -1, (-7 / 3 : ℚ), 0, (-4 / 3 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, -2], ![1, -1, (-9 / 4 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, 0, 0, (-18 / 5 : ℚ)], ![1, -1, (-12 / 5 : ℚ), 0, (-16 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, (-9 / 5 : ℚ), (-106 / 15 : ℚ)], ![(-2 / 15 : ℚ), 0, (-2 / 15 : ℚ), (-23 / 15 : ℚ), (-53 / 15 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-62 / 17 : ℚ), 0, 0, (-18 / 17 : ℚ)], ![(29 / 17 : ℚ), (-33 / 17 : ℚ), (-64 / 17 : ℚ), (4 / 17 : ℚ), (-16 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -5, 0, 0, 0], ![(9 / 4 : ℚ), (-5 / 2 : ℚ), (-21 / 4 : ℚ), (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, 0, 0, 0], ![2, -2, (-17 / 4 : ℚ), (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 0, 0, (-26 / 5 : ℚ)], ![(-1 / 5 : ℚ), (-1 / 5 : ℚ), (-1 / 5 : ℚ), (4 / 5 : ℚ), -5]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-40 / 9 : ℚ), 0, (-4 / 3 : ℚ), 0], ![(19 / 9 : ℚ), (-20 / 9 : ℚ), (-62 / 9 : ℚ), (-14 / 9 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, 0, (-7 / 5 : ℚ), 0], ![2, -2, (-36 / 5 : ℚ), (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-44 / 9 : ℚ), 0, (-5 / 3 : ℚ), 0], ![(20 / 9 : ℚ), (-8 / 3 : ℚ), (-70 / 9 : ℚ), (-5 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 7 : ℚ), (-10 / 7 : ℚ), (10 / 7 : ℚ), (-3 / 7 : ℚ), (-23 / 7 : ℚ)], ![0, (-20 / 7 : ℚ), 0, (3 / 7 : ℚ), (-11 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), 0, 0, 0, (-3 / 7 : ℚ)], ![(-10 / 7 : ℚ), 0, 0, -1, (-1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 8 : ℚ), 0, (-1 / 6 : ℚ), (-9 / 8 : ℚ), (-17 / 24 : ℚ)], ![(-7 / 6 : ℚ), (1 / 24 : ℚ), (-1 / 24 : ℚ), (-7 / 6 : ℚ), (1 / 24 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-31 / 26 : ℚ), (-1 / 26 : ℚ), (-1 / 13 : ℚ), (9 / 26 : ℚ), (-1 / 13 : ℚ)], ![(-33 / 26 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-23 / 12 : ℚ), (-11 / 12 : ℚ), (-13 / 12 : ℚ), (23 / 12 : ℚ), 0], ![(-23 / 12 : ℚ), 0, (-1 / 6 : ℚ), (23 / 12 : ℚ), (1 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-4 / 3 : ℚ), 0, (-1 / 2 : ℚ), (-5 / 2 : ℚ), (-1 / 6 : ℚ)], ![(-3 / 2 : ℚ), 0, (-1 / 6 : ℚ), -5, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-9 / 7 : ℚ), 0, 0, 0, (-3 / 7 : ℚ)], ![(-10 / 7 : ℚ), 0, 0, -4, (-1 / 7 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-53 / 48 : ℚ), (-1 / 48 : ℚ), (-7 / 48 : ℚ), (-101 / 48 : ℚ), (-3 / 4 : ℚ)], ![(-55 / 48 : ℚ), 0, (-1 / 24 : ℚ), (-103 / 48 : ℚ), (1 / 48 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-7 / 2 : ℚ), 0, (-5 / 2 : ℚ), (3 / 4 : ℚ)], ![(7 / 4 : ℚ), (-7 / 4 : ℚ), 0, -5, (-3 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-10 / 3 : ℚ), 0, (-7 / 3 : ℚ), (2 / 3 : ℚ)], ![(5 / 3 : ℚ), (-5 / 3 : ℚ), 0, (-14 / 3 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 17 : ℚ), (-49 / 17 : ℚ), 0, (-25 / 17 : ℚ), (-3 / 17 : ℚ)], ![(14 / 17 : ℚ), (-26 / 17 : ℚ), 0, (-50 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .y), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-9 / 4 : ℚ), 0, (-7 / 6 : ℚ), 0], ![(13 / 12 : ℚ), (-17 / 12 : ℚ), 0, (-7 / 3 : ℚ), (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 5 : ℚ), 0, (-6 / 5 : ℚ), -1, (-28 / 5 : ℚ)], ![(-4 / 5 : ℚ), 0, (-12 / 5 : ℚ), -2, (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-18 / 5 : ℚ), 0, (-13 / 5 : ℚ), (-2 / 5 : ℚ)], ![(9 / 5 : ℚ), (-9 / 5 : ℚ), 0, (-26 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 13 : ℚ), (-42 / 13 : ℚ), 0, (-29 / 13 : ℚ), (-34 / 13 : ℚ)], ![(5 / 13 : ℚ), (-25 / 13 : ℚ), 0, (-58 / 13 : ℚ), (-30 / 13 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-3 / 17 : ℚ), (-32 / 17 : ℚ), 0], ![1, -1, (-11 / 17 : ℚ), (-67 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 20 : ℚ), (-6 / 5 : ℚ), 0], ![1, -1, (-19 / 20 : ℚ), (-49 / 20 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 24 : ℚ), 0, (-1 / 24 : ℚ), (-35 / 48 : ℚ), (-55 / 48 : ℚ)], ![(-43 / 48 : ℚ), (-1 / 48 : ℚ), (-67 / 48 : ℚ), (-3 / 2 : ℚ), (-53 / 48 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 2 : ℚ), -5, (-1 / 2 : ℚ), (-7 / 2 : ℚ), 0], ![2, (-5 / 2 : ℚ), 0, (-15 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (-8 / 17 : ℚ), (-62 / 17 : ℚ), 0], ![2, -2, (4 / 17 : ℚ), (-132 / 17 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-8 / 17 : ℚ), 0, (-8 / 17 : ℚ), (-8 / 17 : ℚ), (-92 / 17 : ℚ)], ![(-16 / 17 : ℚ), (-4 / 17 : ℚ), (-50 / 17 : ℚ), (-24 / 17 : ℚ), (-88 / 17 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .y), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-2 / 3 : ℚ), -1], ![0, 0, 0, -2, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .y), (.xy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 8 : ℚ), (-23 / 8 : ℚ), 0, (-13 / 8 : ℚ), 0], ![(3 / 4 : ℚ), (-3 / 2 : ℚ), (-3 / 4 : ℚ), (-27 / 8 : ℚ), (1 / 8 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-5 / 24 : ℚ), -7, (-59 / 24 : ℚ), (-31 / 8 : ℚ), 0], ![(10 / 3 : ℚ), (-7 / 2 : ℚ), (-7 / 6 : ℚ), (-63 / 8 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-1 / 2 : ℚ), -4], ![0, 0, 0, (-5 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-11 / 12 : ℚ), -5, (-7 / 12 : ℚ), (-41 / 12 : ℚ), 0], ![(5 / 4 : ℚ), (-8 / 3 : ℚ), (-1 / 3 : ℚ), (-43 / 6 : ℚ), (1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-13 / 10 : ℚ), 0, (-23 / 10 : ℚ)], ![1, -1, (-29 / 10 : ℚ), 0, (-23 / 20 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-8 / 5 : ℚ), 0, -2], ![1, -1, (-19 / 5 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-23 / 15 : ℚ), 0, (-46 / 15 : ℚ)], ![1, -1, (-18 / 5 : ℚ), 0, (-14 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-9 / 8 : ℚ), 0, (-17 / 8 : ℚ)], ![1, -1, (-19 / 8 : ℚ), 0, (-17 / 16 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 2 : ℚ), -1, -4], ![0, 0, (-3 / 2 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-3 / 2 : ℚ), 0, -3], ![1, -1, (-7 / 2 : ℚ), 0, (-11 / 4 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 24 : ℚ), 0, (-3 / 4 : ℚ), (-9 / 8 : ℚ), (-37 / 6 : ℚ)], ![(-7 / 8 : ℚ), 0, (-37 / 24 : ℚ), (-13 / 12 : ℚ), (-37 / 12 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-19 / 24 : ℚ), 0, (-35 / 48 : ℚ), (-55 / 48 : ℚ), (-17 / 4 : ℚ)], ![(-43 / 48 : ℚ), (-1 / 48 : ℚ), (-3 / 2 : ℚ), (-53 / 48 : ℚ), (-25 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -5, (-11 / 4 : ℚ), 0, 0], ![(9 / 4 : ℚ), (-5 / 2 : ℚ), -6, (-7 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (-13 / 6 : ℚ), 0, 0], ![2, -2, (-9 / 2 : ℚ), (-13 / 12 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, (-1 / 10 : ℚ), 0, (-23 / 5 : ℚ)], ![(-1 / 10 : ℚ), (-1 / 10 : ℚ), (-2 / 5 : ℚ), (2 / 5 : ℚ), (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 20 : ℚ), (-41 / 10 : ℚ), (-43 / 20 : ℚ), (-11 / 10 : ℚ), 0], ![2, (-41 / 20 : ℚ), (-39 / 8 : ℚ), (-61 / 40 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (-12 / 5 : ℚ), (-7 / 5 : ℚ), 0], ![2, -2, (-29 / 5 : ℚ), (-9 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .yy), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (1 / 6 : ℚ), (-3 / 2 : ℚ), 1, (-9 / 2 : ℚ)], ![(-5 / 3 : ℚ), 0, (-19 / 6 : ℚ), 1, (-9 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (1 / 6 : ℚ), (-1 / 6 : ℚ), (7 / 6 : ℚ), 0], ![(-3 / 2 : ℚ), (1 / 3 : ℚ), 0, (-7 / 6 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 4 : ℚ), (1 / 4 : ℚ), (-1 / 4 : ℚ), 0, 0], ![(-7 / 4 : ℚ), (1 / 2 : ℚ), 0, (-5 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xy, .x), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-3 / 2 : ℚ), (-1 / 6 : ℚ), (-1 / 6 : ℚ), (5 / 6 : ℚ), 0], ![(-3 / 2 : ℚ), 0, 0, 0, 0]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .y), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(1 / 2 : ℚ), (-5 / 2 : ℚ), 2, 0, (-11 / 2 : ℚ)], ![(1 / 2 : ℚ), -5, (-1 / 2 : ℚ), 0, (-11 / 2 : ℚ)]] },
  { network := { reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero), (.yy, .xx)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-7 / 6 : ℚ), 0, 0, 0, (-1 / 6 : ℚ)], ![(-7 / 6 : ℚ), 0, 0, -4, (-1 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, 0, (-35 / 16 : ℚ), 1], ![2, -2, (1 / 16 : ℚ), (-9 / 4 : ℚ), -1]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (3 / 5 : ℚ), (-23 / 10 : ℚ), 0, (-13 / 10 : ℚ)], ![(-3 / 10 : ℚ), (3 / 10 : ℚ), (-9 / 2 : ℚ), (-1 / 10 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .y)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (-13 / 5 : ℚ), 0, (-13 / 5 : ℚ), 0], ![(6 / 5 : ℚ), (-8 / 5 : ℚ), (1 / 5 : ℚ), (-14 / 5 : ℚ), (-4 / 5 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-1 / 6 : ℚ), 0, (-7 / 6 : ℚ), (-4 / 3 : ℚ), (-13 / 3 : ℚ)], ![(-1 / 6 : ℚ), 0, (-13 / 6 : ℚ), (-3 / 2 : ℚ), (-13 / 6 : ℚ)]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, (60 / 17 : ℚ), (-66 / 17 : ℚ), (8 / 17 : ℚ), (-128 / 17 : ℚ)], ![(-30 / 17 : ℚ), (30 / 17 : ℚ), (-124 / 17 : ℚ), 0, 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 10 : ℚ), (-7 / 5 : ℚ), 0], ![1, -1, (-4 / 5 : ℚ), (-3 / 2 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -2, (-1 / 10 : ℚ), (-13 / 10 : ℚ), 0], ![1, -1, (-9 / 10 : ℚ), (-7 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![(-2 / 5 : ℚ), (-24 / 5 : ℚ), (-2 / 5 : ℚ), (-14 / 5 : ℚ), 0], ![2, (-12 / 5 : ℚ), 0, (-16 / 5 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xx, .xy), (.yy, .zero)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, -4, (-1 / 2 : ℚ), (-13 / 4 : ℚ), 0], ![2, -2, (1 / 4 : ℚ), (-15 / 4 : ℚ), 0]] },
  { network := { reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .xy), (.xy, .x)]
                 noSelf := by decide
                 injective := by decide }
    sign := 1
    multiplier := ![![0, 0, 1, (-1 / 4 : ℚ), -1], ![0, 0, 0, -1, 0]] }
]

theorem conicDetC27_checked : conicDetC27.all RationalConicRecord.check = true := by
  native_decide

end SmallCusp
