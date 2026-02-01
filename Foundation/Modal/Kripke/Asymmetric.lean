module

public import Foundation.Modal.Kripke.AxiomGeach
public import Foundation.Modal.Kripke.Closure

@[expose] public section


namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}

protected abbrev Frame.IsAsymmetric (F : Frame) := Std.Asymm F.Rel

lemma Frame.asymm [F.IsAsymmetric] : ∀ {x y : F.World}, x ≺ y → ¬y ≺ x := by
  apply Std.Asymm.asymm

instance [F.IsAsymmetric] : F.IsIrreflexive := ⟨by
  intro x hx
  exact (Frame.asymm (F := F) hx) hx
⟩

end Kripke

end LO.Modal
end
