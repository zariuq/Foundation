module

public import Foundation.Propositional.Hilbert.F.Deduction
public import Foundation.Propositional.Kripke2.Basic

@[expose] public section

namespace LO.Propositional

open LO.Entailment (disjunctive)
open LO.Propositional.Entailment.Corsi
open Formula

variable {α : Type*}
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

structure FTheory (L : Logic ℕ) where
  protected theory : FormulaSet ℕ
  protected no_bot : ⊥ ∉ theory
  protected andIR : ∀ {φ ψ}, φ ∈ theory → ψ ∈ theory → φ ⋏ ψ ∈ theory
  protected imp_closed : ∀ {φ ψ}, L ⊢ φ ➝ ψ → φ ∈ theory → ψ ∈ theory
  protected L_subset : L ⊆ theory


namespace FTheory

attribute [simp] FTheory.no_bot
attribute [grind <=] FTheory.andIR FTheory.imp_closed

variable {T : FTheory L} {φ ψ χ : Formula ℕ}

@[simp, grind <=]
lemma mem_of_provable [Entailment.HasAxiomVerum L] [Entailment.AFortiori L] (hφ : L ⊢ φ) : φ ∈ T.theory := by
  apply T.imp_closed (φ := ⊤) $ af hφ;
  apply T.L_subset;
  apply Logic.iff_provable.mp;
  simp;

lemma mem_trans [Entailment.HasAxiomI L] (h₁ : φ ➝ ψ ∈ T.theory) (h₂ : ψ ➝ χ ∈ T.theory) : φ ➝ χ ∈ T.theory := by
  apply T.imp_closed (axiomI (ψ := ψ));
  apply T.andIR h₁ h₂;

@[grind <=]
lemma mem_orIntroL [Entailment.HasAxiomOrInst L] (hφ : φ ∈ T.theory) : φ ⋎ ψ ∈ T.theory := by
  apply T.imp_closed (φ := φ);
  . exact orIntroL;
  . assumption;

@[grind <=]
lemma mem_orIntroR [Entailment.HasAxiomOrInst L] (hψ : ψ ∈ T.theory) : φ ⋎ ψ ∈ T.theory := by
  apply T.imp_closed (φ := ψ);
  . exact orIntroR;
  . assumption;

open Hilbert.F in
lemma iff_mem_CorsiDeducible {T : FTheory (Hilbert.F Ax)} : φ ∈ T.theory ↔ Deduction Ax T.theory φ := by
  constructor;
  . intro hφ;
    apply Deduction.ctx hφ;
  . intro h; induction h <;> grind

end FTheory


variable {L : Logic ℕ}

structure PrimeFTheory (L : Logic ℕ) extends FTheory L where
  protected prime : ∀ {φ ψ}, φ ⋎ ψ ∈ theory → φ ∈ theory ∨ ψ ∈ theory

namespace FTheory.lindenbaum

open Classical
open Encodable

variable {φ ψ χ ξ : Formula ℕ} {T : FTheory L} {hT : χ ➝ ξ ∉ T.theory}

def construction (T : FTheory L) (hT : χ ➝ ξ ∉ T.theory) : ℕ → Set (Formula ℕ)
  | 0 => { δ | χ ➝ δ ∈ T.theory }
  | i + 1 =>
    match (decode i) with
    | some δ =>
      letI T' := construction T hT i
      if ∀ Γ : Finset (Formula _), ↑Γ ⊆ T' → Γ.conj ⋏ δ ➝ ξ ∉ T.theory then insert δ T'
      else T'
    | none => construction T hT i

def construction_omega (T : FTheory L) (hT : χ ➝ ξ ∉ T.theory) : Set (Formula ℕ) := ⋃ i, construction T hT i

lemma subset_construction_succ : construction T hT i ⊆ construction T hT (i + 1) := by
  dsimp [construction];
  split;
  . split <;> tauto;
  . tauto;

lemma subset_construction_add : construction T hT i ⊆ construction T hT (i + j) := by
  induction j with
  | zero => simp;
  | succ j ih =>
    trans construction T hT (i + j);
    . apply ih;
    . apply subset_construction_succ;

lemma monotone_construction (hij : i ≤ j) : construction T hT i ⊆ construction T hT j := by
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp hij;
  apply subset_construction_add;

lemma mem_omega_of_mem (h : χ ➝ δ ∈ T.theory) : δ ∈ construction_omega T hT := by
  simp only [construction_omega, Set.mem_iUnion];
  use 0;
  simpa [construction];

lemma of_mem_construction_omega {φ : Formula ℕ} (hφ : φ ∈ construction_omega T hT) :
  (χ ➝ φ ∈ T.theory) ∨ (∀ Γ : Finset _, ↑Γ ⊆ construction T hT (encode φ) → Γ.conj ⋏ φ ➝ ξ ∉ T.theory) := by
  obtain ⟨i, hi⟩ := by simpa [construction_omega] using hφ;
  induction i with
  | zero => left; simpa [construction] using hi;
  | succ i ih =>
    dsimp [construction] at hi;
    sorry;
    /-
    split at hi;
    . split_ifs at hi with h;
      . replace hi := Set.mem_insert_iff.mp hi;
        rcases hi with (rfl | hi);
        . right;
          assumption;
        . grind;
      . grind;
    . grind;
    .dsimp [construction] at hi;
    split at hi;
    . split_ifs at hi with h;
      . replace hi := Set.mem_insert_iff.mp hi;
        rcases hi with (rfl | hi);
        . sorry;
        . grind;
      . grind;
    . grind;
    split at hi;
    -/

lemma not_of_mem_construction_omega {φ : Formula ℕ}
  {Γ : Finset (Formula ℕ)} (hΓ : ↑Γ ⊆ construction T hT (encode φ))
  (hφ : Γ.conj ⋏ φ ➝ ξ ∈ T.theory) :
  φ ∉ (construction_omega T hT) := by
  simp only [construction_omega, Set.mem_iUnion, not_exists];
  intro i;
  induction i with
  | zero =>
    simp [construction];
    sorry;
  | succ i ih =>
    simp only [construction];
    split;
    . split_ifs with h;
      . rename_i δ hδ;
        by_contra hC;
        have : δ = φ := by grind;
        subst this;
        apply h Γ ((show encode δ = i by sorry) ▸ hΓ) hφ;
      . assumption
    . assumption;

lemma of_not_mem_construction_omega {φ : Formula ℕ} (hφ : φ ∉ construction_omega T hT) :
  (χ ➝ φ ∉ T.theory) ∧ (∃ Γ : Finset (Formula _), ↑Γ ⊆ (construction T hT (encode φ)) ∧ Γ.conj ⋏ φ ➝ ξ ∈ T.theory) := by
  simp only [construction_omega, Set.mem_iUnion, not_exists] at hφ;
  constructor;
  . simpa using hφ 0;
  . have this := hφ (encode φ + 1);
    simp only [construction, encodek] at this;
    split_ifs at this with h;
    . simp at this;
    . simpa using h;


variable [Entailment.F L]

lemma construction_omega_mem_ant : χ ∈ construction_omega T hT := by
  apply mem_omega_of_mem;
  apply T.mem_of_provable;
  apply impId;

lemma construction_omega_not_mem_csq : ξ ∉ construction_omega T hT := by
  simp only [construction_omega, Set.mem_iUnion, not_exists];
  intro i;
  induction i with
  | zero => simpa [construction];
  | succ i ih =>
    contrapose! ih;
    dsimp [construction] at ih;
    split at ih;
    . split_ifs at ih with h;
      . rename_i δ hδ;
        have := h ∅ (by tauto);
        contrapose! this;
        have : ξ = δ := by grind;
        subst this;
        apply T.mem_of_provable;
        simp;
      . assumption;
    . assumption;

lemma construction_omega_andClosed :
  letI U := construction_omega T hT
  φ ∈ U → ψ ∈ U → φ ⋏ ψ ∈ U := by
  rintro hφ hψ;
  by_contra hφψ;
  replace ⟨hφψ, ⟨Γ, hΓ₁, hΓ₂⟩⟩ := of_not_mem_construction_omega hφψ;

  sorry;

lemma construction_omega_impClosed :
  letI U := construction_omega T hT
  L ⊢ φ ➝ ψ → φ ∈ U → ψ ∈ U := by
  rintro hφψ hφ;
  simp only [construction_omega, Set.mem_iUnion];
  use (encode ψ) + 1;
  simp only [construction, encodek];
  split_ifs with h;
  . tauto;
  . exfalso;
    push_neg at h;
    obtain ⟨Γ, hΓ, hΓ₂⟩ := h;
    have hΓ₁ : (Γ.conj ⋏ φ) ➝ (Γ.conj ⋏ ψ) ∈ T.theory := T.mem_of_provable $ by
      sorry;
    have : (Γ.conj ⋏ φ) ➝ ξ ∈ T.theory := T.imp_closed axiomI $ T.andIR hΓ₁ hΓ₂;

     sorry;

lemma construction_omega_L_subset :
  letI U := construction_omega T hT
  L ⊆ U := by
  intro φ hφ;
  simp only [construction_omega, Set.mem_iUnion];
  use (encode φ + 1);
  simp only [construction, encodek];
  split_ifs with h;
  . tauto;
  . exfalso;
    push_neg at h;
    obtain ⟨Γ, hΓ, h₁⟩ := h;
    have h₂ : Γ.conj ➝ (Γ.conj ⋏ φ) ∈ T.theory := by
      apply T.L_subset;
      apply Logic.iff_provable.mp;
      apply CK_of_C_of_C;
      . exact impId;
      . apply af;
        exact Logic.iff_provable.mpr hφ;
    have : Γ.conj ➝ ξ ∈ T.theory := T.mem_trans h₂ h₁;

    have : Γ.conj ➝ ξ ∈ construction_omega T hT := by sorry;
    sorry;

lemma construction_omega_prime :
  letI U := construction_omega T hT
  φ ⋎ ψ ∈ U → φ ∈ U ∨ ψ ∈ U := by
  rintro hφψ;
  by_contra! hC;
  obtain ⟨hφ, hψ⟩ := hC;
  obtain ⟨_, ⟨Γ, hΓ₁, hΓ₂⟩⟩ := of_not_mem_construction_omega hφ;
  obtain ⟨_, ⟨Δ, hΔ₁, hΔ₂⟩⟩ := of_not_mem_construction_omega hψ;

  let m := max (encode φ) (encode ψ);
  have : ↑(Γ ∪ Δ) ⊆ construction T hT m := by sorry;
  have : ((Γ.conj ⋏ Δ.conj) ⋏ (φ ⋎ ψ)) ➝ ξ ∈ T.theory := by
    apply T.imp_closed ?_ $ T.andIR hΓ₂ hΔ₂;
    sorry;
  sorry;

lemma construction_omega_noBot :
  letI U := construction_omega T hT
  ⊥ ∉ U := by
  simp only [construction_omega, Set.mem_iUnion, not_exists];
  intro i;
  induction i with
  | zero =>
    simp [construction];
    sorry;
  | succ i ih =>
    contrapose! ih;
    dsimp [construction] at ih;
    split at ih;
    . split_ifs at ih with h;
      . rename_i δ hδ;
        have := h ∅ (by tauto);
        contrapose! this;
        have : ⊥ = δ := by grind;
        subst this;
        sorry;
      . assumption;
    . assumption;

lemma construction_rel :
  letI U := construction_omega T hT
  (∀ φ ψ, φ ➝ ψ ∈ T.theory → φ ∈ U → ψ ∈ U) := by
  sorry;

end FTheory.lindenbaum

open FTheory.lindenbaum in
lemma FTheory.lindenbaum {χ ξ : Formula _} [Entailment.F L] (T : FTheory L) (hT : χ ➝ ξ ∉ T.theory) : ∃ U : PrimeFTheory L,
  (∀ φ ψ, φ ➝ ψ ∈ T.theory → φ ∈ U.theory → ψ ∈ U.theory) ∧
  χ ∈ U.theory ∧ ξ ∉ U.theory := by
  use {
     theory := construction_omega T hT,
     no_bot := construction_omega_noBot,
     andIR := construction_omega_andClosed,
     imp_closed := construction_omega_impClosed,
     L_subset := construction_omega_L_subset,
     prime := construction_omega_prime
  };
  constructor;
  . apply construction_rel;
  . exact ⟨construction_omega_mem_ant, construction_omega_not_mem_csq⟩;

abbrev emptyPrimeFTheory (L : Logic _) [Entailment.F L] [Entailment.Disjunctive L] : PrimeFTheory L where
  theory := L
  no_bot := by
    sorry;
  andIR hφ hψ := by
    simp only [←Logic.iff_provable] at hφ hψ ⊢;
    apply andIR <;> assumption;
  imp_closed := by
    intros φ ψ hφψ hφ;
    simp only [←Logic.iff_provable] at hφψ hφ ⊢;
    exact hφψ ⨀ hφ;
  L_subset := by tauto;
  prime {φ ψ} hφψ := by
    simp only [←Logic.iff_provable] at hφψ ⊢;
    exact disjunctive hφψ;

instance [Entailment.F L] [Entailment.Disjunctive L] : Nonempty (PrimeFTheory L) := ⟨emptyPrimeFTheory L⟩


namespace Kripke2

variable {Ax : Axiom ℕ} {φ ψ χ : Formula ℕ}
variable [Entailment.F L] [Entailment.Disjunctive L]

open Formula.Kripke2

abbrev canonicalModel (L : Logic ℕ) [Entailment.F L] [Entailment.Disjunctive L] : Kripke2.Model where
  World := PrimeFTheory L
  Rel T U := ∀ {φ ψ}, φ ➝ ψ ∈ T.theory → φ ∈ U.theory → ψ ∈ U.theory
  Val T a := (atom a) ∈ T.theory
  root := emptyPrimeFTheory L
  rooted := by
    intro T φ ψ hφψ hφ;
    rw [←Logic.iff_provable] at hφψ;
    exact T.imp_closed hφψ hφ;

lemma truthlemma {T : canonicalModel L} : Satisfies _ T φ ↔ φ ∈ T.theory := by
  induction φ generalizing T with
  | hatom a => simp [Kripke2.Satisfies];
  | hfalsum => simp [Kripke2.Satisfies];
  | hor φ ψ ihφ ihψ =>
    suffices φ ∈ T.theory ∨ ψ ∈ T.theory ↔ φ ⋎ ψ ∈ T.theory by
      simpa [Kripke2.Satisfies, ihφ, ihψ];
    constructor;
    . rintro (hφ | hψ);
      . apply T.imp_closed orIntroL hφ;
      . apply T.imp_closed orIntroR hψ;
    . apply T.prime;
  | hand φ ψ ihφ ihψ =>
    suffices (φ ∈ T.theory ∧ ψ ∈ T.theory) ↔ φ ⋏ ψ ∈ T.theory by
      simpa [Kripke2.Satisfies, ihφ, ihψ];
    constructor;
    . rintro ⟨hφ, hψ⟩;
      apply T.andIR hφ hψ;
    . intro h;
      constructor;
      . apply T.imp_closed andElimL h;
      . apply T.imp_closed andElimR h;
  | himp φ ψ ihφ ihψ =>
    suffices (∀ {U : canonicalModel L}, T ≺ U → φ ∈ U.theory → ψ ∈ U.theory) ↔ φ ➝ ψ ∈ T.theory by
      simpa [Kripke2.Satisfies, ihφ, ihψ];
    constructor;
    . contrapose!;
      exact FTheory.lindenbaum T.toFTheory;
    . rintro hφψ U RTU hφ;
      apply RTU hφψ hφ;

theorem provable_of_validOncanonicalModel : (canonicalModel L) ⊧ φ → L ⊢ φ := by
  contrapose!;
  intro h;
  apply ValidOnModel.not_of_exists_world;
  use (emptyPrimeFTheory L);
  apply truthlemma.not.mpr;
  apply Logic.iff_unprovable.mp;
  simpa;

end Kripke2

end LO.Propositional
end
