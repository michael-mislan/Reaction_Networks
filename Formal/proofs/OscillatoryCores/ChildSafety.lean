import proofs.OscillatoryCores.Source
import proofs.OscillatoryCores.ChildTransport
import proofs.OscillatoryCores.KernelChildCertificate

namespace OscillatoryCores

open DUnstableCores

theorem all_children_dNonUnstable (κ : ChildSelection source) :
    DNonUnstable κ.realMatrix := by
  apply transport_child_safety
    (Q' := KernelChildCertificate.parameterRichCounterexampleSource) _ _
    KernelChildCertificate.parameterRichCounterexample_all_children_dNonUnstable κ
  · intro i j h
    exact (reactant_iff_base i j).mp h
  · exact stoich_eq_base

end OscillatoryCores
