module

public import Foundation.FirstOrder.Intuitionistic.Formula

@[expose] public section
namespace LO.FirstOrder

namespace Semiformulaᵢ

def rewAux ⦃n₁ n₂ : ℕ⦄ : Rew L ξ₁ n₁ ξ₂ n₂ → Semiformulaᵢ L ξ₁ n₁ → Semiformulaᵢ L ξ₂ n₂
  | _, ⊥        => ⊥
  | ω, rel r v  => rel r (ω ∘ v)
  | ω, φ ⋏ ψ    => rewAux ω φ ⋏ rewAux ω ψ
  | ω, φ ⋎ ψ    => rewAux ω φ ⋎ rewAux ω ψ
  | ω, φ ➝ ψ    => rewAux ω φ ➝ rewAux ω ψ
  | ω, ∀' φ     => ∀' rewAux ω.q φ
  | ω, ∃' φ     => ∃' rewAux ω.q φ

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformulaᵢ L ξ₁ n₁ →ˡᶜ Semiformulaᵢ L ξ₂ n₂ where
  toTr := rewAux ω
  map_top' := rfl
  map_bot' := rfl
  map_neg' := by simp [Semiformulaᵢ.neg_def, rewAux]
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_imply' := fun _ _ ↦ rfl

instance : Rewriting L ξ (Semiformulaᵢ L ξ) ζ (Semiformulaᵢ L ζ) where
  app := rew
  app_all (_ _) := rfl
  app_ex (_ _) := rfl

instance : Coe (Semisentenceᵢ L n) (SyntacticSemiformulaᵢ L n) := ⟨Rewriting.emb (ξ := ℕ)⟩

lemma rew_rel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ rel r v = rel r fun i ↦ ω (v i) := rfl

lemma rew_rel' (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω ▹ rel r v = rel r (ω ∘ v) := rfl

private lemma map_inj {n₁ n₂} {b : Fin n₁ → Fin n₂} {f : ξ₁ → ξ₂}
    (hb : Function.Injective b) (hf : Function.Injective f) :
      Function.Injective fun φ : Semiformulaᵢ L ξ₁ n₁ ↦ @Rew.map L ξ₁ ξ₂ n₁ n₂ b f ▹ φ
  | ⊥, φ => by
    cases φ using cases' <;> simp [rew_rel]
  | rel r v, φ => by
    cases φ using cases'
    case hRel r' v' =>
      simp only [rew_rel, rel.injEq, and_imp]
      rintro rfl
      simp only [heq_eq_eq, true_and]
      rintro rfl h
      simp only [true_and]
      funext i
      exact Rew.map_inj hb hf (congr_fun h i)
    case hFalsum =>
      simp only [rew_rel, LogicalConnective.HomClass.map_bot, reduceCtorEq, imp_self]
    case hAnd φ ψ =>
      simp only [rew_rel, LogicalConnective.HomClass.map_and, reduceCtorEq, imp_self]
    case hOr φ ψ =>
      simp only [rew_rel, LogicalConnective.HomClass.map_or, reduceCtorEq, imp_self]
    case hImp φ ψ =>
      simp only [rew_rel, LogicalConnective.HomClass.map_imply, reduceCtorEq, imp_self]
    case hAll φ =>
      simp only [rew_rel, Rewriting.app_all, reduceCtorEq, imp_self]
    case hEx φ =>
      simp only [rew_rel, Rewriting.app_ex, reduceCtorEq, imp_self]
  | φ ⋏ ψ, χ => by
    cases χ using cases'
    case hRel r v =>
      simp only [LogicalConnective.HomClass.map_and, rew_rel, reduceCtorEq, imp_self]
    case hFalsum =>
      simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_bot, reduceCtorEq, imp_self]
    case hAnd χ₁ χ₂ =>
      simp only [LogicalConnective.HomClass.map_and, and_inj, and_imp]
      intro hp hq
      exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    case hOr χ₁ χ₂ =>
      simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or, reduceCtorEq, imp_self]
    case hImp χ₁ χ₂ =>
      simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_imply, reduceCtorEq, imp_self]
    case hAll χ =>
      simp only [LogicalConnective.HomClass.map_and, Rewriting.app_all, reduceCtorEq, imp_self]
    case hEx χ =>
      simp only [LogicalConnective.HomClass.map_and, Rewriting.app_ex, reduceCtorEq, imp_self]
  | φ ⋎ ψ, χ => by
    cases χ using cases'
    case hRel r v =>
      simp only [LogicalConnective.HomClass.map_or, rew_rel, reduceCtorEq, imp_self]
    case hFalsum =>
      simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_bot, reduceCtorEq, imp_self]
    case hAnd χ₁ χ₂ =>
      simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and, reduceCtorEq, imp_self]
    case hOr χ₁ χ₂ =>
      simp only [LogicalConnective.HomClass.map_or, or_inj, and_imp]
      intro hp hq
      exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    case hImp χ₁ χ₂ =>
      simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_imply, reduceCtorEq, imp_self]
    case hAll χ =>
      simp only [LogicalConnective.HomClass.map_or, Rewriting.app_all, reduceCtorEq, imp_self]
    case hEx χ =>
      simp only [LogicalConnective.HomClass.map_or, Rewriting.app_ex, reduceCtorEq, imp_self]
  | φ ➝ ψ, χ => by
    cases χ using cases'
    case hRel r v =>
      simp only [LogicalConnective.HomClass.map_imply, rew_rel, reduceCtorEq, imp_self]
    case hFalsum =>
      simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_bot, reduceCtorEq, imp_self]
    case hAnd χ₁ χ₂ =>
      simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and, reduceCtorEq, imp_self]
    case hOr χ₁ χ₂ =>
      simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_or, reduceCtorEq, imp_self]
    case hImp χ₁ χ₂ =>
      simp only [LogicalConnective.HomClass.map_imply, imp_inj, and_imp]
      intro hp hq
      exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    case hAll χ =>
      simp only [LogicalConnective.HomClass.map_imply, Rewriting.app_all, reduceCtorEq, imp_self]
    case hEx χ =>
      simp only [LogicalConnective.HomClass.map_imply, Rewriting.app_ex, reduceCtorEq, imp_self]
  | ∀' φ, ψ => by
    cases ψ using cases'
    case hRel r v =>
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, rew_rel, reduceCtorEq, imp_self]
    case hFalsum =>
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_bot, reduceCtorEq,
        imp_self]
    case hAnd φ ψ =>
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_and, reduceCtorEq,
        imp_self]
    case hOr φ ψ =>
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_or, reduceCtorEq,
        imp_self]
    case hImp φ ψ =>
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_imply, reduceCtorEq,
        imp_self]
    case hAll ψ =>
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, all_inj]
      intro h
      exact map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h
    case hEx ψ =>
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, Rewriting.app_ex, reduceCtorEq, imp_self]
  | ∃' φ, ψ => by
    cases ψ using cases'
    case hRel r v =>
      simp only [Rewriting.app_ex, Rew.q_map, Nat.succ_eq_add_one, rew_rel, reduceCtorEq, imp_self]
    case hFalsum =>
      simp only [Rewriting.app_ex, Rew.q_map, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_bot, reduceCtorEq,
        imp_self]
    case hAnd φ ψ =>
      simp only [Rewriting.app_ex, Rew.q_map, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_and, reduceCtorEq,
        imp_self]
    case hOr φ ψ =>
      simp only [Rewriting.app_ex, Rew.q_map, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_or, reduceCtorEq,
        imp_self]
    case hImp φ ψ =>
      simp only [Rewriting.app_ex, Rew.q_map, Nat.succ_eq_add_one, LogicalConnective.HomClass.map_imply, reduceCtorEq,
        imp_self]
    case hAll ψ =>
      simp only [Rewriting.app_ex, Rew.q_map, Nat.succ_eq_add_one, Rewriting.app_all, reduceCtorEq, imp_self]
    case hEx ψ =>
      simp only [Rewriting.app_ex, Rew.q_map, Nat.succ_eq_add_one, ex_inj]
      intro h
      exact map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h

instance : ReflectiveRewriting L ξ (Semiformulaᵢ L ξ) where
  id_app (φ) := by induction φ using rec' <;> simp [rew_rel, *]

instance : TransitiveRewriting L ξ₁ (Semiformulaᵢ L ξ₁) ξ₂ (Semiformulaᵢ L ξ₂) ξ₃ (Semiformulaᵢ L ξ₃) where
  comp_app {n₁ n₂ n₃ ω₁₂ ω₂₃ φ} := by
    induction φ using rec' generalizing n₂ n₃ <;> simp [rew_rel, Rew.comp_app, Rew.q_comp, *]

instance : InjMapRewriting L ξ (Semiformulaᵢ L ξ) ζ (Semiformulaᵢ L ζ) where
  smul_map_injective := map_inj

instance : LawfulSyntacticRewriting L (SyntacticSemiformulaᵢ L) where

@[simp] lemma complexity_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformulaᵢ L ξ₁ n₁) : (ω ▹ φ).complexity = φ.complexity := by
  induction φ using rec' generalizing n₂ <;> simp [*, rew_rel]

@[simp] lemma IsNegative.rew {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformulaᵢ L ξ₁ n₁} :
    (ω ▹ φ).IsNegative ↔ φ.IsNegative := by
  induction φ using rec' generalizing n₂ <;> simp [rew_rel, *]

end Semiformulaᵢ

end LO.FirstOrder
