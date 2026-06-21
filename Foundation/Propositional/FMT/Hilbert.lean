module

public import Foundation.Propositional.Hilbert.VF.Basic
public import Foundation.Propositional.FMT.Basic

@[expose] public section

namespace LO.Propositional

open FMT
open Formula
open Formula.FMT

namespace Hilbert.VF.FMT

variable {Ax Ax₁ Ax₂ : Axiom ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}


section FrameClass

variable {C C₁ C₂ : FMT.FrameClass}

lemma soundness_frameclass (hV : C ⊧* Ax) : (Hilbert.VF Ax) ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind;

def instFrameClassSound (hV : C ⊧* Ax) : Sound (Hilbert.VF Ax) C := ⟨fun {_} => soundness_frameclass hV⟩

lemma consistent_of_sound_frameclass (C : FMT.FrameClass) (hC : Set.Nonempty C) [sound : Sound (Hilbert.VF Ax) C] : Entailment.Consistent (Hilbert.VF Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := hC;
  use F;
  grind;

lemma weakerThan_of_subset_frameClass (C₁ C₂ : FMT.FrameClass) (hC : C₂ ⊆ C₁) [Sound (Hilbert.VF Ax₁) C₁] [Complete (Hilbert.VF Ax₂) C₂] : (Hilbert.VF Ax₁) ⪯ (Hilbert.VF Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓢 := (Hilbert.VF Ax₁)) (𝓜 := C₁) hφ;
  apply hC hF;

end FrameClass


section ModelClass

variable {C C₁ C₂ : FMT.ModelClass}

lemma soundness_modelclass (hV : C ⊧* Ax) : (Hilbert.VF Ax) ⊢ φ → C ⊧ φ := by
  intro hφ M hM;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind

def instModelClassSound (hV : C ⊧* Ax) : Sound (Hilbert.VF Ax) C := ⟨fun {_} => soundness_modelclass hV⟩

lemma consistent_of_sound_modelclass (C : FMT.ModelClass) (hC : Set.Nonempty C) [sound : Sound (Hilbert.VF Ax) C] : Entailment.Consistent (Hilbert.VF Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨M, hM⟩ := hC;
  use M;
  grind;

end ModelClass


end Hilbert.VF.FMT


end LO.Propositional
end
