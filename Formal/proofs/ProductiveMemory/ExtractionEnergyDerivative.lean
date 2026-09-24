import proofs.ProductiveMemory.ExtractionRegions
import proofs.CoreCouplingCAC.Cutoff
import proofs.CoreCouplingCAC.EnergyBarrier

namespace ProductiveMemory
open FiniteCopy Set
noncomputable section
set_option Elab.async false

theorem low_extraction_energy_derivative (x : ℝ → Point) (v c : Point) (t : ℝ)
    (hd : HasDerivAt x v t) :
    HasDerivAt (fun s => lowExtractionEnergy (fun i => x s i-c i))
      (2*lowExtractionPair (fun i => x t i-c i) v) t := by
  have h0 := ((hasDerivAt_pi.1 hd) 0).sub_const (c 0)
  have h1 := ((hasDerivAt_pi.1 hd) 1).sub_const (c 1)
  have h2 := ((hasDerivAt_pi.1 hd) 2).sub_const (c 2)
  have h3 := ((hasDerivAt_pi.1 hd) 3).sub_const (c 3)
  have h := (((((((((((((((((h0.const_mul (539561/500000:ℝ)).mul h0).add ((h0.const_mul (-568413/1000000:ℝ)).mul h1)).add ((h0.const_mul (2227359/1000000:ℝ)).mul h2)).add ((h0.const_mul (326633/100000:ℝ)).mul h3)).add ((h1.const_mul (-568413/1000000:ℝ)).mul h0)).add ((h1.const_mul (211557/200000:ℝ)).mul h1)).add ((h1.const_mul (-548597/250000:ℝ)).mul h2)).add ((h1.const_mul (-80379/25000:ℝ)).mul h3)).add ((h2.const_mul (2227359/1000000:ℝ)).mul h0)).add ((h2.const_mul (-548597/250000:ℝ)).mul h1)).add ((h2.const_mul (398987/62500:ℝ)).mul h2)).add ((h2.const_mul (9601239/1000000:ℝ)).mul h3)).add ((h3.const_mul (326633/100000:ℝ)).mul h0)).add ((h3.const_mul (-80379/25000:ℝ)).mul h1)).add ((h3.const_mul (9601239/1000000:ℝ)).mul h2)).add ((h3.const_mul (7325563/500000:ℝ)).mul h3))
  convert h using 1
  simp only [lowExtractionPair]
  ring

theorem high_extraction_energy_derivative (x : ℝ → Point) (v c : Point) (t : ℝ)
    (hd : HasDerivAt x v t) :
    HasDerivAt (fun s => highExtractionEnergy (fun i => x s i-c i))
      (2*highExtractionPair (fun i => x t i-c i) v) t := by
  have h0 := ((hasDerivAt_pi.1 hd) 0).sub_const (c 0)
  have h1 := ((hasDerivAt_pi.1 hd) 1).sub_const (c 1)
  have h2 := ((hasDerivAt_pi.1 hd) 2).sub_const (c 2)
  have h3 := ((hasDerivAt_pi.1 hd) 3).sub_const (c 3)
  have h := (((((((((((((((((h0.const_mul (244049/250000:ℝ)).mul h0).add ((h0.const_mul (-93801/62500:ℝ)).mul h1)).add ((h0.const_mul (2954639/1000000:ℝ)).mul h2)).add ((h0.const_mul (2205629/500000:ℝ)).mul h3)).add ((h1.const_mul (-93801/62500:ℝ)).mul h0)).add ((h1.const_mul (5195401/1000000:ℝ)).mul h1)).add ((h1.const_mul (-2080217/250000:ℝ)).mul h2)).add ((h1.const_mul (-6269591/500000:ℝ)).mul h3)).add ((h2.const_mul (2954639/1000000:ℝ)).mul h0)).add ((h2.const_mul (-2080217/250000:ℝ)).mul h1)).add ((h2.const_mul (14137961/1000000:ℝ)).mul h2)).add ((h2.const_mul (10664797/500000:ℝ)).mul h3)).add ((h3.const_mul (2205629/500000:ℝ)).mul h0)).add ((h3.const_mul (-6269591/500000:ℝ)).mul h1)).add ((h3.const_mul (10664797/500000:ℝ)).mul h2)).add ((h3.const_mul (32242779/1000000:ℝ)).mul h3))
  convert h using 1
  simp only [highExtractionPair]
  ring

end
end ProductiveMemory
