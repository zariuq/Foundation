module

public import Mathlib.Logic.IsEmpty.Basic

@[expose] public section

namespace _root_.IsEmpty
variable {o : Sort u} (h : _root_.IsEmpty o)

lemma eq_elim' {α : Sort*} (f : o → α) : f = h.elim' := by
  funext x
  exact h.elim x

lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim := by
  funext x
  exact h.elim x

end _root_.IsEmpty

end
