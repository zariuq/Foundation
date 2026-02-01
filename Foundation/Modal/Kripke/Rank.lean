module

public import Foundation.Modal.Kripke.Logic.GL.Tree
public import Foundation.Modal.Kripke.ExtendRoot

@[expose] public section

namespace LO.Modal

noncomputable section

namespace Kripke

variable {φ ψ : Formula ℕ}
         {F : Frame} {r : F} [Fintype F] [F.IsTree r] {x y i j : F}

def Frame.rank (i : F) : ℕ := fcwHeight (· ≺ ·) i

def Frame.height (F : Frame) {r : F} [Fintype F] [F.IsTree r] : ℕ := Frame.rank r

namespace Frame

lemma rank_lt_whole_height {i : F} (hi : r ≺ i) :
    F.rank i < F.height := fcwHeight_gt_of hi

lemma rank_le_whole_height (i : F) :
    F.rank i ≤ F.height := by
  by_cases hi : i = r
  · rcases hi; rfl
  · have : r ≺ i := root_genaretes'! i hi
    exact le_of_lt (fcwHeight_gt_of this)

lemma rank_lt_of_rel (hij : i ≺ j) : F.rank i > Frame.rank j := fcwHeight_gt_of hij

lemma exists_of_lt_height (hn : n < F.rank i) : ∃ j : F, i ≺ j ∧ Frame.rank j = n := fcwHeight_lt hn

lemma height_lt_iff_relItr {i : F} :
    F.rank i < n ↔ ∀ j, ¬i ≺^[n] j  := by
  match n with
  |     0 => simp_all
  | n + 1 =>
    suffices F.rank i ≤ n ↔ ∀ j : F, i ≺ j → Frame.rank j < n by
      calc
        F.rank i < n + 1
          ↔ F.rank i ≤ n := Nat.lt_add_one_iff
        _ ↔ ∀ j, i ≺ j → Frame.rank j < n := this
        _ ↔ ∀ j, i ≺ j → ∀ k, ¬j ≺^[n] k := by simp [height_lt_iff_relItr (n := n)]
        _ ↔ ∀ k j, i ≺ j → ¬j ≺^[n] k    := by grind
        _ ↔ ∀ j, ¬i ≺^[n + 1] j  := by simp
    constructor
    · exact fun h j hij ↦ lt_of_lt_of_le (fcwHeight_gt_of hij) h
    · exact fcwHeight_le

lemma le_height_iff_relItr {i : F} :
    n ≤ F.rank i ↔ ∃ j, i ≺^[n] j := calc
  n ≤ F.rank i ↔ ¬F.rank i < n := Iff.symm Nat.not_lt
  _                           ↔ ∃ j, i ≺^[n] j := by simp [height_lt_iff_relItr]

lemma height_eq_iff_relItr {i : F} :
    F.rank i = n ↔ (∃ j, i ≺^[n] j) ∧ (∀ j, i ≺^[n] j → ∀ k, ¬j ≺ k) := calc
  F.rank i = n
    ↔ F.rank i < n + 1 ∧ n ≤ F.rank i := by simpa [Nat.lt_succ_iff] using Nat.eq_iff_le_and_ge
  _ ↔ (∀ j, ¬i ≺^[n + 1] j) ∧ (∃ j, i ≺^[n] j) := by simp [height_lt_iff_relItr, le_height_iff_relItr]
  _ ↔ (∀ k j, i ≺^[n] j → ¬j ≺ k) ∧ (∃ j, i ≺^[n] j) := by simp only [Rel.Iterate.forward, not_exists, not_and]
  _ ↔ (∃ j, i ≺^[n] j) ∧ (∀ j, i ≺^[n] j → ∀ k, ¬j ≺ k) := by grind

lemma exists_rank_terminal (i : F) : ∃ j, i ≺^[F.rank i] j := le_height_iff_relItr.mp (by simp)

lemma eq_height_root : Frame.rank x = F.height ↔ x = r := by
  constructor;
  . rintro h;
    contrapose! h;
    apply Nat.ne_of_lt;
    apply Frame.rank_lt_whole_height;
    apply F.root_genaretes'!;
    assumption;
  . tauto;

lemma terminal_rel_height (h : x ≺^[rank x] y) : ∀ z, ¬y ≺ z := by
  intro z Ryz;
  suffices rank x + 1 ≤ rank x by omega;
  exact le_height_iff_relItr.mpr ⟨z, Rel.Iterate.forward.mpr ⟨y, h, Ryz⟩⟩;

namespace extendRoot

@[simp] lemma height_pos : 0 < (F.extendRoot 1).height := by
  apply lt_fcwHeight ?_ (by simp)
  · exact Sum.inr r
  trivial

@[simp] lemma height_succ : (F.extendRoot 1).height = F.height + 1 := by
  let l := rank (extendRoot.root : F.extendRoot 1)
  suffices
      l ≤ Frame.rank r + 1 ∧
      Frame.rank r < l by
    simpa using Nat.eq_iff_le_and_ge.mpr this
  constructor
  · suffices l - 1 ≤ rank r from Nat.le_add_of_sub_le this
    apply le_height_iff_relItr.mpr
    by_cases hl : l - 1 = 0
    · exact ⟨r, by simp [hl]⟩
    have lpos : 0 < l - 1 := Nat.zero_lt_of_ne_zero hl
    have e : l = (l - 1) + 1 := by
      symm; exact Nat.sub_add_cancel Frame.extendRoot.height_pos
    have : ∃ j, extendRoot.root ≺^[l] j := exists_rank_terminal (extendRoot.root : F.extendRoot 1)
    rcases this with ⟨j, hj⟩
    have : ∃ z, extendRoot.root ≺ z ∧ z ≺^[l - 1] j := by
      rw [e] at hj
      simpa using hj
    rcases this with ⟨z, hz, hzj⟩
    have : ∃ x, j = embed x := eq_inr_of_root_rel <| Rel.Iterate.unwrap_of_trans_of_pos height_pos hj
    rcases this with ⟨j, rfl⟩
    rcases not_root_of_from_root'₁ hz with (rfl | ⟨z, rfl, Rrz⟩)
    · exact ⟨j, embed_rel_iterate_embed_iff_rel.mp hzj⟩
    use j
    exact Rel.Iterate.constant_trans_of_pos lpos Rrz (embed_rel_iterate_embed_iff_rel.mp hzj)
  · suffices rank r + 1 ≤ rank extendRoot.root from this
    apply le_height_iff_relItr.mpr
    rcases exists_rank_terminal r with ⟨j, hj⟩
    exact ⟨j, r, by trivial, embed_rel_iterate_embed_iff_rel.mpr hj⟩

lemma eq_original_height : Frame.rank (x : F.extendRoot 1) = Frame.rank x := by
  apply height_eq_iff_relItr.mpr;
  constructor;
  . obtain ⟨y, Rxy⟩ := exists_rank_terminal (i := x);
    use y;
    apply extendRoot.embed_rel_iterate_embed_iff_rel.mpr;
    exact Rxy;
  . rintro (_ | y) Rxy (_ | z);
    . simp;
    . -- TODO: extract no loop lemma (x ≺^[n] i cannot happen where x is original and i is new elements by extension)
      exfalso;
      have : extendRoot.root ≺ (x : F.extendRoot 1) := Frame.root_genaretes'! (F := F.extendRoot 1) x (by simp);
      have : (x : F.extendRoot 1) ≺ x :=
        Rel.Iterate.unwrap_of_trans_of_pos (by omega) $
        Rel.Iterate.comp (m := 1) |>.mp ⟨_, Rxy, by simpa⟩;
      exact Frame.irrefl _ this;
    . apply Frame.asymm;
      exact Frame.root_genaretes'! (F := F.extendRoot 1) y (by simp);
    . have := terminal_rel_height $ extendRoot.embed_rel_iterate_embed_iff_rel.mp Rxy;
      exact extendRoot.embed_rel_embed_iff_rel.not.mpr $ this z;

lemma eq_original_height_root : (F.extendRoot 1).rank r = F.height := eq_original_height

@[grind]
lemma iff_eq_height_eq_original_root {x : F.extendRoot 1} : Frame.rank x = F.height ↔ x = r := by
  constructor;
  . rcases x with (a | x);
    . intro h;
      have := h ▸ height_succ (F := F);
      simp [Frame.height] at this;
    . intro h;
      suffices x = r by simp [this];
      apply Frame.eq_height_root.mp;
      exact h ▸ Frame.extendRoot.eq_original_height.symm;
  . rintro rfl;
    exact eq_original_height_root;

end extendRoot


namespace pointGenerate

open Classical in
instance [Fintype F] : Fintype (F↾x) := by apply Subtype.fintype;

instance [F.IsTree r] : (F↾x).IsTree ⟨x, by tauto⟩ := by constructor;

theorem eq_original_height (hxy : y = x ∨ x ≺^+ y) :
    Frame.rank (F := F↾x) (⟨y, hxy⟩) = Frame.rank y := by
  let y' : (F↾x) := ⟨y, hxy⟩

  have proj_iterate :
      ∀ {n : ℕ} {a b : (F↾x)},
        Frame.RelItr' (F := (F↾x)) n a b → a.1 ≺^[n] b.1 := by
    intro n a b hab
    induction n generalizing a b with
    | zero =>
      have : a = b := (Rel.Iterate.iff_zero).1 hab
      subst this
      simp [Rel.Iterate.iff_zero]
    | succ n ih =>
      rcases (Rel.Iterate.iff_succ).1 hab with ⟨w, haw, hwb⟩
      have haw' : a.1 ≺ w.1 := by simpa using haw
      have hwb' : w.1 ≺^[n] b.1 := ih hwb
      apply (Rel.Iterate.iff_succ).2
      exact ⟨w.1, haw', hwb'⟩

  have lift_iterate :
      ∀ {n : ℕ} {y z : F} (hy : y = x ∨ x ≺^+ y),
        y ≺^[n] z →
          ∃ hz : z = x ∨ x ≺^+ z,
            Frame.RelItr' (F := (F↾x)) n (⟨y, hy⟩ : (F↾x)) (⟨z, hz⟩ : (F↾x)) := by
    intro n y z hy hyz
    classical
    induction n generalizing y z with
    | zero =>
      have : y = z := (Rel.Iterate.iff_zero).1 hyz
      subst this
      refine ⟨hy, ?_⟩
      simp [Frame.RelItr', Rel.Iterate.iff_zero]
    | succ n ih =>
      rcases (Rel.Iterate.iff_succ).1 hyz with ⟨w, R_yw, R_wz⟩
      have hw : w = x ∨ x ≺^+ w := by
        right
        rcases hy with rfl | hxy
        · exact Relation.TransGen.single R_yw
        · exact Relation.TransGen.tail hxy R_yw
      rcases ih (y := w) (z := z) hw R_wz with ⟨hz, ih'⟩
      refine ⟨hz, ?_⟩
      apply (Rel.Iterate.iff_succ).2
      refine ⟨⟨w, hw⟩, ?_, ih'⟩
      exact R_yw

  apply Nat.le_antisymm
  · by_contra h
    have hlt : Frame.rank y < Frame.rank (F := F↾x) y' := Nat.lt_of_not_ge h
    have hn : Frame.rank y + 1 ≤ Frame.rank (F := F↾x) y' := Nat.succ_le_of_lt hlt
    rcases (Frame.le_height_iff_relItr (F := (F↾x)) (i := y') (n := Frame.rank y + 1)).1 hn with ⟨j, hyj⟩
    have hyj' : Frame.RelItr' (F := (F↾x)) (Frame.rank y + 1) y' j := hyj
    have hyj_orig : y ≺^[Frame.rank y + 1] j.1 := proj_iterate hyj'
    have none : ∀ t : F, ¬y ≺^[Frame.rank y + 1] t :=
      (Frame.height_lt_iff_relItr (F := F) (i := y) (n := Frame.rank y + 1)).1 (Nat.lt_succ_self (Frame.rank y))
    exact (none j.1) hyj_orig
  · by_contra h
    have hlt : Frame.rank (F := F↾x) y' < Frame.rank y := Nat.lt_of_not_ge h
    have nle : Frame.rank (F := F↾x) y' + 1 ≤ Frame.rank y := Nat.succ_le_of_lt hlt
    rcases (Frame.le_height_iff_relItr (F := F) (i := y) (n := Frame.rank (F := F↾x) y' + 1)).1 nle with
      ⟨z, hyz⟩
    rcases lift_iterate (y := y) (z := z) hxy hyz with ⟨hz, hyz'⟩
    have none : ∀ t : (F↾x), ¬y' ≺^[Frame.rank (F := F↾x) y' + 1] t :=
      (Frame.height_lt_iff_relItr (F := (F↾x)) (i := y') (n := Frame.rank (F := F↾x) y' + 1)).1
        (Nat.lt_succ_self (Frame.rank (F := F↾x) y'))
    have hyz'' : y' ≺^[Frame.rank (F := F↾x) y' + 1] (⟨z, hz⟩ : (F↾x)) := by
      simpa [Frame.RelItr', y'] using hyz'
    exact (none (⟨z, hz⟩ : (F↾x))) hyz''

end pointGenerate

end Frame


section

variable {M : Model} {r : M.World} [M.IsFiniteTree r] [Fintype M]

lemma height_lt_iff_satisfies_boxbot {i : M} :
    M.rank i < n ↔ i ⊧ □^[n] ⊥ := by
  simp only [Frame.height_lt_iff_relItr, Formula.Kripke.Satisfies.boxItr_def]
  simp

lemma height_pos_of_dia {i : M} (hA : i ⊧ ◇ A) : 0 < M.rank i := by
  have : ∃ j, i ≺ j ∧ j ⊧ A := Formula.Kripke.Satisfies.dia_def.mp hA
  rcases this with ⟨j, hj, _⟩
  apply lt_fcwHeight hj (by simp)

@[simp]
lemma Model.extendRoot.height₁ : (M.extendRoot 1).height = M.height + 1 := Frame.extendRoot.height_succ

end

end Kripke

end

end LO.Modal
end
