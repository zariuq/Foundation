module

public import Mathlib.Data.Fintype.List
public import Foundation.Vorspiel.List.Basic

@[expose]
public section

namespace List

/--
```
  ChainI R x y [a, b, c, d] ↔ x = a ∧ R a b ∧ R b c ∧ R c d ∧ d = y
```
 -/
inductive ChainI {α : Type*} (R : α → α → Prop) : α → α → List α → Prop
  | singleton (a : α) : ChainI R a a [a]
  | cons {a b c : α} {l : List α} : R a b → ChainI R b c l → ChainI R a c (a :: l)

namespace ChainI

variable {α : Type*} {R : α → α → Prop}

@[simp] lemma not_nil (a b) : ¬ChainI R a b [] := by rintro ⟨⟩

@[simp] lemma singletob_iff (a b x) : ChainI R a b [x] ↔ a = x ∧ x = b := by
  constructor
  · rintro ⟨⟩ <;> simp_all
  · rintro ⟨rfl, rfl⟩; simp [ChainI.singleton]

attribute [simp] ChainI.singleton

lemma cons_iff : ChainI R a b (c :: l) ↔ a = c ∧ ChainI R c b (c :: l) := by
  constructor
  · rintro (_ | _)
    · simp
    case cons a' hR h =>
    simp [h.cons hR]
  · rintro ⟨rfl, _⟩
    assumption

lemma cons_cons_iff :
    ChainI R a b (c :: d ::  l) ↔ a = c ∧ R c d ∧ ChainI R d b (d :: l) := by
  constructor
  · rintro ⟨⟩
    case cons d' hR hC =>
      rcases cons_iff.mp hC with ⟨rfl, hC⟩
      simp_all
  · rintro ⟨rfl, hR, hC⟩
    exact hC.cons hR

lemma not_mem_of_rel (IR : Std.Irrefl R) (TR : Transitive R) {a b x : α} {l : List α} :
    ChainI R a b l → R x a → x ∉ l := by
  intro hChain hxa
  induction hChain generalizing x with
  | singleton a =>
      intro hx
      rcases List.mem_singleton.mp hx with rfl
      exact IR.irrefl _ hxa
  | cons hR hTail ih =>
      intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact IR.irrefl _ hxa
      · exact ih (TR hxa hR) hx

lemma nodup (IR : Std.Irrefl R) (TR : Transitive R) {a b l} : ChainI R a b l → l.Nodup := by
  intro hChain
  induction hChain with
  | singleton =>
      simp
  | cons hR hTail ih =>
      exact List.nodup_cons.mpr ⟨not_mem_of_rel IR TR hTail hR, ih⟩

lemma finite_of_irreflexive_of_transitive [Finite α] (IR : Std.Irrefl R) (TR : Transitive R) (a b : α) :
    Finite {l : List α // l.ChainI R a b} := by
  haveI : Fintype α := Fintype.ofFinite α
  let f : {l : List α // l.ChainI R a b} → {l : List α // l.Nodup} := fun l ↦ ⟨l, l.prop.nodup IR TR⟩
  have : Function.Injective f := by intro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩; simp [f]
  exact Finite.of_injective f this

lemma cons_eq {l} : ChainI R a b (a' :: l) → a = a' := by
  rintro ⟨⟩ <;> simp

lemma eq_of {l} (h₁ : ChainI R a₁ b₁ l) (h₂ : ChainI R a₂ b₂ l) : a₁ = a₂ ∧ b₁ = b₂ := by
  match l with
  |          [] => simp_all
  |      _ :: [] =>
    cases h₁ with
    | singleton =>
        cases h₂ with
        | singleton =>
            simp
        | cons _ hTail =>
            cases hTail
    | cons _ hTail =>
        cases hTail
  | j :: i :: l =>
    rcases cons_cons_iff.mp h₁ with ⟨ha₁, _, h₁'⟩
    rcases cons_cons_iff.mp h₂ with ⟨ha₂, _, h₂'⟩
    subst ha₁
    subst ha₂
    exact ⟨rfl, (eq_of h₁' h₂').2⟩

lemma prec_exists_of_ne {l} (h : ChainI R a b l) :
    a ≠ b → ∃ l' c, R a c ∧ l = a :: c :: l' ∧ ChainI R c b (c :: l') := by
  intro _
  match l with
  |            [] => rcases h
  |          [b'] => rcases h <;> simp_all
  | b' :: c :: l' =>
    rcases h
    case cons c' hR h =>
      rcases show c' = c from cons_eq h
      exact ⟨l', _, hR, rfl, h⟩

lemma tail_exists (h : ChainI R a b l) : ∃ l', l = a :: l' := by
  match l with
  |            [] => rcases h
  |          [b'] => rcases h <;> simp_all
  | b' :: c :: l' =>
    rcases h
    case cons c' hR h =>
      rcases show c' = c from cons_eq h
      exact ⟨_, rfl⟩

lemma append_singleton_append_iff {l₁ l₂ : List α} :
    ChainI R a b (l₁ ++ c :: l₂) ↔ ChainI R a c (l₁ ++ [c]) ∧ ChainI R c b (c :: l₂) := by
  match l₁ with
  |           [] => simp [cons_iff (a := a)]
  |          [x] => simp [cons_cons_iff, and_assoc]
  | x :: y :: l₁ =>
    have ih : ChainI R y b (y :: (l₁ ++ c :: l₂)) ↔ ChainI R y c (y :: (l₁ ++ [c])) ∧ ChainI R c b (c :: l₂) :=
      append_singleton_append_iff (l₁ := y :: l₁) (l₂ := l₂) (c := c) (a := y) (b := b)
    simp [cons_cons_iff, ih, and_assoc]

lemma rel_of_infix (hC : ChainI R a b l) (x y) (h : [x, y] <:+: l) : R x y := by
  rcases h with ⟨l₁, l₂, rfl⟩
  have hC' : ChainI R a b (l₁ ++ x :: y :: l₂) := by
    simpa using hC
  have hxyb : ChainI R x b (x :: y :: l₂) :=
    (append_singleton_append_iff (R := R) (a := a) (b := b)
      (l₁ := l₁) (l₂ := y :: l₂) (c := x)).mp hC' |>.2
  exact (cons_cons_iff.mp hxyb).2.1

lemma infix_of_suffix_of (h : ChainI R a b l₁) : x :: l₁ <:+ l₂ → [x, a] <:+: l₂ := by
  intro hx
  rcases h.tail_exists with ⟨l₁', rfl⟩
  exact List.infix_iff_prefix_suffix.mpr ⟨x :: a :: l₁', by simp, hx⟩

lemma prefix_suffix : ChainI R a b l → [a] <+: l ∧ [b] <:+ l := by
  match l with
  |           [] => simp
  |          [x] =>
    intro h
    rcases (singletob_iff (R := R) a b x).mp h with ⟨rfl, rfl⟩
    simp
  | x :: y :: l₁ =>
    rintro ⟨⟩
    case cons z hR h =>
      simpa using List.suffix_cons_of h.prefix_suffix.2

end ChainI

end List

end
