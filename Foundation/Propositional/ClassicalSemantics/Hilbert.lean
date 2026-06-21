module

public import Foundation.Propositional.Hilbert.Standard
public import Foundation.Propositional.ClassicalSemantics.Basic
public import Foundation.Propositional.ConsistentTableau

@[expose] public section

namespace LO.Propositional

open LO.Entailment
open Semantics
open ClassicalSemantics
open Formula.ClassicalSemantics

namespace Cl

theorem soundness (h : Propositional.Cl ⊢ φ) : φ.Tautology := by
  intro v;
  induction h with
  | axm _ h => rcases h with (rfl | rfl) <;> tauto;
  | mdp ihφψ ihφ => exact ihφψ ihφ;
  | andElimL => simp [Semantics.Models, val]; tauto;
  | andElimR => simp [Semantics.Models, val];
  | orElim => simp [Semantics.Models, val]; tauto;
  | _ => tauto;

lemma not_provable_of_exists_valuation : (∃ v : Valuation _, ¬(v ⊧ φ)) → Propositional.Cl ⊬ φ := by
  contrapose!;
  simpa [Formula.Tautology, Semantics.Valid] using soundness;

section Completeness

open
  Entailment
  SaturatedConsistentTableau

def canonicalVal (T : SaturatedConsistentTableau Propositional.Cl) : Valuation ℕ := λ a => (.atom a) ∈ T.1.1

lemma truthlemma {T : SaturatedConsistentTableau Propositional.Cl} : (canonicalVal T) ⊧ φ ↔ φ ∈ T.1.1 := by
  induction φ with
  | hatom => simp [canonicalVal];
  | hfalsum => simp
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ;
      rcases imp_iff_not_or.mp hφψ with hφ | hψ;
      . apply iff_mem₁_imp.mpr;
        left;
        exact iff_not_mem₁_mem₂.mp $ ihφ.not.mp $ hφ;
      . apply iff_mem₁_imp.mpr;
        right;
        exact ihψ.mp hψ;
    . rintro hφψ hφ;
      apply ihψ.mpr;
      rcases iff_mem₁_imp.mp hφψ with hφ | hψ;
      . have := ihφ.not.mpr $ iff_not_mem₁_mem₂.mpr hφ; contradiction;
      . exact hψ;
  | hand φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩;
      apply iff_mem₁_and.mpr;
      constructor;
      . apply ihφ.mp hφ;
      . apply ihψ.mp hψ;
    . rintro hφψ;
      rcases iff_mem₁_and.mp hφψ with ⟨hφ, hψ⟩;
      constructor;
      . apply ihφ.mpr hφ;
      . apply ihψ.mpr hψ;
  | hor φ ψ ihφ ihψ =>
    constructor;
    . rintro (hφ | hψ);
      . apply iff_mem₁_or.mpr;
        left;
        apply ihφ.mp hφ;
      . apply iff_mem₁_or.mpr;
        right;
        apply ihψ.mp hψ;
    . rintro hφψ;
      rcases iff_mem₁_or.mp hφψ with hφ | hψ;
      . left; apply ihφ.mpr hφ;
      . right; apply ihψ.mpr hψ;

theorem completeness : (φ.Tautology) → (Propositional.Cl ⊢ φ) := by
  contrapose;
  intro h;
  obtain ⟨T, hT⟩ := lindenbaum (𝓢 := Propositional.Cl) (t₀ := (∅, {φ})) $ by
    intro Γ Δ hΓ hΔ;
    by_contra hC;
    apply h;
    replace hΓ : Γ = ∅ := by simpa using hΓ;
    subst hΓ;
    rcases Set.subset_singleton_iff_eq.mp hΔ with (hΔ | hΔ);
    . simp only [Finset.coe_eq_empty] at hΔ;
      subst hΔ;
      exact of_O! $ (by simpa using hC) ⨀ verum!;
    . simp only [Finset.coe_eq_singleton] at hΔ;
      subst hΔ;
      exact (by simpa using hC) ⨀ verum!;
  unfold Formula.Tautology Semantics.Valid;
  push_neg;
  use (canonicalVal T);
  apply truthlemma.not.mpr;
  apply iff_not_mem₁_mem₂.mpr;
  apply hT.2;
  tauto;

@[grind =]
theorem iff_provable_tautology : Propositional.Cl ⊢ φ ↔ φ.Tautology := ⟨
  soundness,
  completeness,
⟩

lemma exists_valuation_of_not_provable : ¬(Propositional.Cl ⊢ φ) → ∃ v : Valuation _, ¬(v ⊧ φ) := by
  contrapose!;
  simpa [Formula.Tautology, Semantics.Valid] using completeness;

end Completeness

theorem tautologies : Propositional.Cl = { φ | φ.Tautology } := by
  ext;
  rw [←Logic.iff_provable];
  apply iff_provable_tautology;

end Cl


end LO.Propositional
end
