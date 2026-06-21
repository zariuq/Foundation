module

public import Foundation.Propositional.Hilbert.F.Basic
public import Foundation.Propositional.Kripke2.Basic

@[expose] public section

namespace LO.Propositional

open Kripke2
open Formula
open Formula.Kripke2

namespace Hilbert.F.Kripke2

variable {Ax Ax₁ Ax₂ : Axiom ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}


section FrameClass

variable {C C₁ C₂ : Kripke2.FrameClass}

lemma soundness_frameclass (hV : C ⊧* Ax) : (Hilbert.F Ax) ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind;

def instFrameClassSound (hV : C ⊧* Ax) : Sound (Hilbert.F Ax) C := ⟨fun {_} => soundness_frameclass hV⟩

lemma consistent_of_sound_frameclass (C : Kripke2.FrameClass) (hC : Set.Nonempty C) [sound : Sound (Hilbert.F Ax) C] : Entailment.Consistent (Hilbert.F Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := hC;
  use F;
  grind;

lemma weakerThan_of_subset_frameClass (C₁ C₂ : Kripke2.FrameClass) (hC : C₂ ⊆ C₁) [Sound (Hilbert.F Ax₁) C₁] [Complete (Hilbert.F Ax₂) C₂] : (Hilbert.F Ax₁) ⪯ (Hilbert.F Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓢 := (Hilbert.F Ax₁)) (𝓜 := C₁) hφ;
  apply hC hF;

end FrameClass


section ModelClass

variable {C C₁ C₂ : Kripke2.ModelClass}

lemma soundness_modelclass (hV : C ⊧* Ax) : (Hilbert.F Ax) ⊢ φ → C ⊧ φ := by
  intro hφ M hM;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind

def instModelClassSound (hV : C ⊧* Ax) : Sound (Hilbert.F Ax) C := ⟨fun {_} => soundness_modelclass hV⟩

lemma consistent_of_sound_modelclass (C : Kripke2.ModelClass) (hC : Set.Nonempty C) [sound : Sound (Hilbert.F Ax) C] : Entailment.Consistent (Hilbert.F Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨M, hM⟩ := hC;
  use M;
  grind;

end ModelClass


end Hilbert.F.Kripke2


end LO.Propositional
end
