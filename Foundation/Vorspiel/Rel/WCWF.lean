module

public import Foundation.Vorspiel.Rel.CWF
public import Mathlib.Data.Fintype.Pigeonhole

@[expose]
public section

section

abbrev WeaklyConverseWellFounded {α} (rel : Rel α α) := ConverseWellFounded (rel.IrreflGen)

@[mk_iff]
class IsWeaklyConverseWellFounded (α) (rel : Rel α α) where wcwf : WeaklyConverseWellFounded rel

end


section

variable {α : Type*} {rel : α → α → Prop}

lemma dependent_choice (h : ∃ s : Set α, s.Nonempty ∧ ∀ a ∈ s, ∃ b ∈ s, rel a b)
  : ∃ f : ℕ → α, ∀ x, rel (f x) (f (x + 1)) := by
  obtain ⟨s, ⟨x, hx⟩, h'⟩ := h;
  choose! f hfs hR using h';
  use fun n ↦ f^[n] x;
  intro n;
  simp only [Function.iterate_succ'];
  refine hR (f^[n] x) ?a;
  induction n with
  | zero => simpa;
  | succ n ih => simp only [Function.iterate_succ']; apply hfs _ ih;

lemma Finite.exists_ne_map_eq_of_infinite_lt {α β} [LinearOrder α] [Infinite α] [Finite β] (f : α → β)
  : ∃ x y : α, (x < y) ∧ f x = f y
  := by
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f;
    rcases lt_trichotomy i j with (hij | _ | hij);
    . use i, j;
    . contradiction;
    . use j, i; simp [hij, e];


lemma antisymm_of_weaklyConverseWellFounded :
    WeaklyConverseWellFounded rel → ∀ ⦃x y : α⦄, rel x y → rel y x → x = y := by
  intro hW x y Rxy Ryx
  by_contra hxy
  have hNot : ¬ WeaklyConverseWellFounded rel := by
    simpa [WeaklyConverseWellFounded] using
      (ConverseWellFounded.iff_has_max (R := Rel.IrreflGen rel)).not.mpr <| by
        push_neg
        use ({x, y} : Set α)
        constructor
        · simp
        · intro z hz
          by_cases hz' : z = x
          · use y
            simp_all [Rel.IrreflGen]
          · use x
            simp_all [Rel.IrreflGen]
  exact hNot hW

instance [IsWeaklyConverseWellFounded _ rel] : Std.Antisymm rel := ⟨by
  intro x y hxy hyx
  exact antisymm_of_weaklyConverseWellFounded
    (isWeaklyConverseWellFounded_iff _ _ |>.mp ‹_›) hxy hyx
⟩


lemma weaklyConverseWellFounded_of_finite_trans_antisymm (hFin : Finite α) (R_trans : Transitive rel)
  : (∀ ⦃x y : α⦄, rel x y → rel y x → x = y) → WeaklyConverseWellFounded rel := by
    intro hAntisymm
    by_contra h
    have hbad :
        ¬ ∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬Rel.IrreflGen rel m x := by
      simpa [WeaklyConverseWellFounded] using
        (ConverseWellFounded.iff_has_max (R := Rel.IrreflGen rel)).not.mp h
    push_neg at hbad
    obtain ⟨f, hf⟩ := dependent_choice hbad
    dsimp [Rel.IrreflGen] at hf

    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite_lt f
    have hi : rel (f i) (f (i + 1)) := (hf i).1
    have hiNe : f i ≠ f (i + 1) := (hf i).2
    have hij' : i + 1 < j := lt_iff_le_and_ne.mpr ⟨by omega, by aesop⟩
    have H : ∀ i j, i < j → rel (f i) (f j) := by
      intro i j hij
      induction hij with
      | refl =>
          exact (hf i).1
      | step _ ih =>
          exact R_trans ih ((hf _).1)
    have hj : rel (f (i + 1)) (f i) := by
      simpa [e] using H (i + 1) j hij'
    exact hiNe (hAntisymm hi hj)

instance [Finite α] [IsTrans _ rel] [Std.Antisymm rel] : IsWeaklyConverseWellFounded α rel := ⟨by
  apply weaklyConverseWellFounded_of_finite_trans_antisymm;
  . assumption;
  . exact IsTrans.trans;
  . exact Std.Antisymm.antisymm;
⟩

end

end
