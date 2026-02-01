module

public import Foundation.Modal.Neighborhood.Logic.EP
public import Foundation.Modal.Neighborhood.Logic.ED

@[expose] public section

namespace LO.Modal

open LO.Entailment (Incomparable)
open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

instance : Incomparable Modal.ED Modal.EP := by
  apply Incomparable.of_unprovable;
  . use (Axioms.D (.atom 0));
    constructor;
    . simp;
    . exact EP.unprovable_AxiomD;
  . use (Axioms.P);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ED);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, λ x => match x with | 0 => {∅, {1}} | 1 => {∅, {0}}⟩;
      constructor;
      . constructor;
        intro X x hX;
        cases x using Fin.cases with
        | zero =>
          -- `hX : X ∈ {∅, {1}}`; show `Xᶜ ∉ {∅, {1}}`
          have hX' : X = ∅ ∨ X = ({1} : Set (Fin 2)) := by
            simpa [Neighborhood.Frame.box, Set.mem_insert_iff, Set.mem_singleton_iff] using hX
          have : Xᶜ ≠ (∅ : Set (Fin 2)) ∧ Xᶜ ≠ ({1} : Set (Fin 2)) := by
            rcases hX' with rfl | rfl
            · constructor
              · simp
              · intro h
                have h' : (Set.univ : Set (Fin 2)) = ({1} : Set (Fin 2)) := by
                  simpa using h
                have hmem : (0 : Fin 2) ∈ (Set.univ : Set (Fin 2)) := by simp
                rw [h'] at hmem
                simp [Set.mem_singleton_iff] at hmem
            · constructor
              · intro h
                have hmem : (0 : Fin 2) ∈ ({1}ᶜ : Set (Fin 2)) := by simp
                rw [h] at hmem
                simp at hmem
              · intro h
                have hmem : (0 : Fin 2) ∈ ({1}ᶜ : Set (Fin 2)) := by simp
                rw [h] at hmem
                simp [Set.mem_singleton_iff] at hmem
          -- unfold `dia` and discharge using the computed complement non-membership
          simpa [Neighborhood.Frame.dia, Neighborhood.Frame.box, Set.mem_compl_iff, Set.mem_setOf_eq,
            Set.mem_insert_iff, Set.mem_singleton_iff] using this
        | succ i =>
          -- `hX : X ∈ {∅, {0}}`; show `Xᶜ ∉ {∅, {0}}`
          have hX' : X = ∅ ∨ X = ({0} : Set (Fin 2)) := by
            simpa [Neighborhood.Frame.box, Set.mem_insert_iff, Set.mem_singleton_iff] using hX
          have : Xᶜ ≠ (∅ : Set (Fin 2)) ∧ Xᶜ ≠ ({0} : Set (Fin 2)) := by
            rcases hX' with rfl | rfl
            · constructor
              · simp
              · intro h
                have h' : (Set.univ : Set (Fin 2)) = ({0} : Set (Fin 2)) := by
                  simpa using h
                have hmem : (1 : Fin 2) ∈ (Set.univ : Set (Fin 2)) := by simp
                rw [h'] at hmem
                simp [Set.mem_singleton_iff] at hmem
            · constructor
              · intro h
                have hmem : (1 : Fin 2) ∈ ({0}ᶜ : Set (Fin 2)) := by simp
                rw [h] at hmem
                simp at hmem
              · intro h
                have hmem : (1 : Fin 2) ∈ ({0}ᶜ : Set (Fin 2)) := by simp
                rw [h] at hmem
                simp [Set.mem_singleton_iff] at hmem
          simpa [Neighborhood.Frame.dia, Neighborhood.Frame.box, Set.mem_compl_iff, Set.mem_setOf_eq,
            Set.mem_insert_iff, Set.mem_singleton_iff] using this
      . apply not_imp_not.mpr notContainsEmpty_of_valid_axiomP;
        by_contra! hC;
        have := hC |>.not_contains_empty;
        simpa using @this 1;

end LO.Modal
end
