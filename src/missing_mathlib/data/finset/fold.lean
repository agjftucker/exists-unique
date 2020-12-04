import data.finset.fold
import missing_mathlib.data.finset.basic

namespace finset
open multiset

variables {α β γ : Type*}

section fold
variables (op : β → β → β) [hc : is_commutative β op] [ha : is_associative β op]
local notation a * b := op a b
include hc ha

variables {op} {f : α → β} {b : β} {s : finset α} {a : α}

@[simp] theorem fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a * s.fold op b f :=
begin
  unfold fold,
  rw [cons_val, map_cons, fold_cons_left]
end

end fold
end finset