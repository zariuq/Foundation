module

public import Foundation.Modal.Kripke.Basic

@[expose] public section

namespace LO.Modal.Kripke

def complexityLimitedFrame (F : Kripke.Frame) (r : F.World) (φ : Formula ℕ) : Kripke.Frame where
  World := { x | ∃ n ≤ φ.complexity, r ≺^[n] x }
  Rel x y := x.1 ≺ y.1
  world_nonempty := ⟨r, by use 0; simp⟩

def complexityLimitedModel (M : Kripke.Model) (w : M.World) (φ : Formula ℕ) : Kripke.Model where
  toFrame := complexityLimitedFrame M.toFrame w φ
  Val x a := M.Val x.1 a

section

variable {M : Kripke.Model} {r x : M.World} {φ ψ : Formula ℕ}

open Formula.Kripke
open Formula

lemma iff_satisfy_complexityLimitedModel_aux
  (hq : ψ ∈ φ.subformulas)
  (hx : ∃ n ≤ φ.complexity - ψ.complexity, r ≺^[n] x)
  :
  haveI : x ∈ {y | ∃ n ≤ φ.complexity, r ≺^[n] y} := by obtain ⟨n, _, _⟩ := hx; use n; exact ⟨by omega, by assumption⟩;
  x ⊧ ψ ↔ Satisfies (complexityLimitedModel M r φ) ⟨x, this⟩ ψ := by
  induction ψ generalizing x φ with
  | hbox ψ ihq =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    have : n + 1 ≤ φ.complexity - ψ.complexity := by
      have : ψ.complexity + 1 ≤ φ.complexity := by simpa using subformulas.complexity_lower hq;
      omega;
    constructor;
    . rintro h ⟨y, hy⟩ Rxy;
      apply ihq (subformulas.mem_box hq) ?_ |>.mp;
      . exact h _ Rxy;
      . use (n + 1);
        constructor;
        . assumption;
        . apply Rel.Iterate.forward.mpr;
          refine ⟨x, ?_, Rxy⟩;
          assumption
    . rintro h y Rxy;
      apply ihq (subformulas.mem_box hq) ?_ |>.mpr;
      . exact h _ Rxy;
      . use (n + 1);
        constructor;
        . assumption;
        . apply Rel.Iterate.forward.mpr;
          use x;
  | himp ψ₁ ψ₂ ihq₁ ihq₂ =>
    obtain ⟨n, hn, hx⟩ := hx;
    simp [Formula.complexity] at hn;
    have hx₁ : ∃ n ≤ φ.complexity - ψ₁.complexity, r ≺^[n] x := ⟨n, by omega, hx⟩
    have hx₂ : ∃ n ≤ φ.complexity - ψ₂.complexity, r ≺^[n] x := ⟨n, by omega, hx⟩
    constructor;
    . rintro hq₁ hq₂;
      apply (ihq₂ (by grind) hx₂).mp;
      apply hq₁;
      exact (ihq₁ (by grind) hx₁).mpr hq₂;
    . rintro hq₁ hq₂;
      apply (ihq₂ (subformulas.mem_imp (by assumption) |>.2) hx₂).mpr;
      apply hq₁;
      exact (ihq₁ (subformulas.mem_imp (by assumption) |>.1) hx₁).mp hq₂;
  | _ => simp [Satisfies, complexityLimitedModel];

lemma iff_satisfy_complexityLimitedModel : r ⊧ φ ↔ Satisfies (complexityLimitedModel M r φ) ⟨r, (by use 0; simp)⟩ φ := by
  apply iff_satisfy_complexityLimitedModel_aux (show φ ∈ φ.subformulas by simp);
  use 0; simp;

lemma complexityLimitedModel_subformula_closedAux {ψ₁ ψ₂ : Formula ℕ} (hq₁ : φ ∈ ψ₁.subformulas) (hq₂ : φ ∈ ψ₂.subformulas)
  : Satisfies (complexityLimitedModel M r ψ₁) ⟨r, (by use 0; simp)⟩ φ → Satisfies (complexityLimitedModel M r ψ₂) ⟨r, (by use 0; simp)⟩ φ := by
  intro h;
  have hx0 : ∃ n ≤ ψ₁.complexity - φ.complexity, r ≺^[n] r := by
    use 0; simp;
  have hx0' : ∃ n ≤ ψ₂.complexity - φ.complexity, r ≺^[n] r := by
    use 0; simp;
  exact (@iff_satisfy_complexityLimitedModel_aux M r r ψ₂ φ hq₂ hx0').mp
    <| (@iff_satisfy_complexityLimitedModel_aux M r r ψ₁ φ hq₁ hx0).mpr h

lemma complexityLimitedModel_subformula_closed (hq : φ ∈ ψ.subformulas)
  : Satisfies (complexityLimitedModel M r φ) ⟨r, (by use 0; simp)⟩ φ ↔ Satisfies (complexityLimitedModel M r ψ) ⟨r, (by use 0; simp)⟩ φ := by
  constructor;
  . apply complexityLimitedModel_subformula_closedAux <;> simp_all;
  . apply complexityLimitedModel_subformula_closedAux <;> simp_all;

end


end LO.Modal.Kripke
end
