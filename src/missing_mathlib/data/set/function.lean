import data.set.function

universes u v w x y

variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open function

namespace set

lemma restrict_eq_iff_eq_on {f g : α → β} {s : set α} :
  s.restrict f = s.restrict g ↔ s.eq_on f g :=
begin
  split,
  { intros h a ha,
    apply congr_fun h ⟨a, ha⟩, },
  { intro h,
    ext ⟨a, ha⟩,
    exact h ha, },
end

end set