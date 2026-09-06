module

public import Foundation.Modal.Neighborhood.Supplementation

@[expose] public section

namespace LO.Modal.Neighborhood

open Classical

variable {F : Frame}

def Frame.intersectionClosure (F : Frame) : Frame := {
  World := F.World,
  𝒩 a X := ∃ Xs : Finset (Set F.World), Xs ≠ ∅ ∧ (X = ⋂ Xi ∈ Xs, Xi) ∧ (∀ Xi ∈ Xs, Xi ∈ F.𝒩 a)
}

instance Frame.intersectionClosure.isRegular : F.intersectionClosure.IsRegular := by
  constructor;
  intro X Y a;
  intro h
  rw [Set.mem_inter_iff] at h
  obtain ⟨hX, hY⟩ := h
  obtain ⟨Xs, hXs₁, rfl, hX₂⟩ := hX
  obtain ⟨Ys, hYs₁, rfl, hY₂⟩ := hY
  refine ⟨Xs ∪ Ys, ?_, ?_, ?_⟩;
  . simp only [ne_eq, Finset.union_eq_empty, not_and];
    intro _; exact hYs₁;
  . exact (Finset.set_biInter_inter Xs Ys _).symm;
  . simp only [Finset.mem_union];
    rintro Z (hZ | hZ);
    . apply hX₂; assumption;
    . apply hY₂; assumption;

lemma Frame.intersectionClosure.mem_box_of_mem_original_box {F : Frame} {x : F} {s : Set F} : x ∈ F.box s → x ∈ F.intersectionClosure.box s := by
  intro hx;
  use {s};
  refine ⟨?_, ?_, ?_⟩ <;> simp_all;

def Frame.quasiFiltering (F : Frame) : Frame := F.intersectionClosure.supplementation

namespace Frame.quasiFiltering

lemma symm_𝒩 : F.quasiFiltering.𝒩 = F.supplementation.intersectionClosure.𝒩 := by
  dsimp [quasiFiltering];
  ext w X;
  constructor;
  . rintro ⟨_, hYs₃, ⟨Ys, hYs₁, rfl, hYs₂⟩⟩;
    let Y := ⋂ Yi ∈ Ys, Yi;
    have : X = ⋂ Yi ∈ Ys, Yi ∪ (X \ Y) := calc
      _ = Y ∪ (X \ Y) := by
        ext x;
        constructor;
        . tauto;
        . rintro (h | ⟨h, _⟩);
          . apply hYs₃ h;
          . assumption;
      _ = _ := by
        ext x;
        simp [Y];
        grind;
    rw [this];
    use Ys.image (λ Yi => Yi ∪ (X \ Y));
    refine ⟨?_, ?_, ?_⟩;
    . exact fun h => hYs₁ (Finset.image_eq_empty.mp h)
    . apply Set.Subset.antisymm
      · intro a ha
        apply Set.mem_iInter.mpr
        intro Z
        apply Set.mem_iInter.mpr
        intro hZ
        obtain ⟨Yi, hYi, rfl⟩ := Finset.mem_image.mp hZ
        exact Set.mem_iInter.mp (Set.mem_iInter.mp ha Yi) hYi
      · intro a ha
        apply Set.mem_iInter.mpr
        intro Yi
        apply Set.mem_iInter.mpr
        intro hYi
        exact Set.mem_iInter.mp (Set.mem_iInter.mp ha _)
          (Finset.mem_image.mpr ⟨Yi, hYi, rfl⟩)
    . intro Zi hZi;
      obtain ⟨Yi, hYi, rfl⟩ := Finset.mem_image.mp hZi;
      exact ⟨Yi, Set.subset_union_left, hYs₂ Yi hYi⟩;
  . rintro ⟨Ys, hYs₁, rfl, hYs₂⟩;
    let Zs := Finset.image (α := Ys) (λ ⟨Yi, hYi⟩ => hYs₂ Yi hYi |>.choose) Finset.univ;
    use (⋂ Zi ∈ Zs, Zi);
    constructor;
    . intro a ha
      apply Set.mem_iInter.mpr
      intro Y
      apply Set.mem_iInter.mpr
      intro hY
      apply (hYs₂ Y hY).choose_spec.1
      exact Set.mem_iInter.mp (Set.mem_iInter.mp ha _) (Finset.mem_image.mpr
        ⟨⟨Y, hY⟩, Finset.mem_univ _, rfl⟩)
    . use Zs;
      refine ⟨?_, ?_, ?_⟩;
      . simpa [Zs];
      . rfl;
      . simp [Zs];
        rintro _ Yi hYi rfl;
        apply hYs₂ Yi hYi |>.choose_spec |>.2;

lemma symm_box : F.quasiFiltering.box = F.supplementation.intersectionClosure.box := by
  ext x;
  simp [symm_𝒩];
  rfl;

instance isMonotonic : F.quasiFiltering.IsMonotonic := Frame.supplementation.isMonotonic

instance isRegular : F.quasiFiltering.IsRegular := Frame.supplementation.isRegular

instance isTransitive [F.IsTransitive] : F.quasiFiltering.IsTransitive := by
  constructor;
  intro X w hw;
  obtain ⟨Y, hY₁, Ys, hYs₁, rfl, hYs₂⟩ := Frame.supplementation.iff_exists_subset.mp hw;
  apply Frame.mono' (F := F.quasiFiltering) (X := (⋂ Yi ∈ Ys, F.box Yi)) $ by
    intro a ha;
    use (⋂ Yi ∈ Ys, Yi);
    refine ⟨?_, Ys, ?_, ?_, ?_⟩
    . assumption;
    . assumption;
    . tauto;
    . intro Xi hXi
      have := Set.mem_iInter₂.mp ha Xi hXi
      exact this;
  replace hYs₂ : w ∈ ⋂ Yi ∈ Ys, F.box^[2] Yi := by
    refine Set.mem_biInter ?_;
    intro Yi hYi;
    exact F.trans $ hYs₂ Yi hYi;
  use (⋂ Yi ∈ Ys, F.box Yi);
  constructor;
  . rfl;
  . use Ys.image F.box
    refine ⟨?_, ?_, ?_⟩;
    . simpa;
    . rw [Finset.set_biInter_finset_image];
      rfl;
    . intro Zi hZi;
      obtain ⟨Yi, hYi, rfl⟩ := Finset.mem_image.mp hZi;
      exact Set.mem_iInter₂.mp hYs₂ Yi hYi;

instance containsUnit [F.ContainsUnit] : F.quasiFiltering.ContainsUnit := by
  constructor;
  apply Set.eq_univ_of_forall;
  intro x;
  apply Frame.supplementation.mem_box_of_mem_original_box (F := F.intersectionClosure);
  apply Frame.intersectionClosure.mem_box_of_mem_original_box;
  exact F.univ_mem x;

lemma mem_box_of_mem_original_box {x : F} {s : Set F} : x ∈ F.box s → x ∈ F.quasiFiltering.box s := by
  intro hx;
  suffices x ∈ F.supplementation.intersectionClosure.box s by exact symm_box ▸ this;
  apply Frame.intersectionClosure.mem_box_of_mem_original_box;
  apply Frame.supplementation.mem_box_of_mem_original_box;
  exact hx;

end Frame.quasiFiltering

end LO.Modal.Neighborhood
end
