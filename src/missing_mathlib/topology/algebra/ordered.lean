import topology.algebra.ordered

open classical set filter topological_space
open function (curry uncurry)
open_locale topological_space classical filter

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section order_topology

section conditionally_complete_linear_order

variables [conditionally_complete_linear_order α] [topological_space α] [order_topology α]
  [conditionally_complete_linear_order β] [topological_space β] [order_topology β] [nonempty γ]

section densely_ordered

variables [densely_ordered α] {a b : α}

variables {δ : Type*} [linear_order δ] [topological_space δ] [order_closed_topology δ]

lemma intermediate_value_Ioc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Ioc (f a) (f b) ⊆ f '' (Ioc a b) :=
begin
  rintros y ⟨hy₁, hy₂⟩,
  obtain ⟨x, ⟨hx₁, hx₂⟩, he⟩ := intermediate_value_Icc hab hf ⟨le_of_lt hy₁, hy₂⟩,
  refine ⟨x, ⟨lt_of_le_of_ne hx₁ _, hx₂⟩, he⟩,
  intro h,
  apply lt_irrefl y,
  rwa [h, he] at hy₁,
end

lemma intermediate_value_Ico {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Ico (f a) (f b) ⊆ f '' (Ico a b) :=
begin
  rintros y ⟨hy₁, hy₂⟩,
  obtain ⟨x, ⟨hx₁, hx₂⟩, he⟩ := intermediate_value_Icc hab hf ⟨hy₁, le_of_lt hy₂⟩,
  refine ⟨x, ⟨hx₁, lt_of_le_of_ne hx₂ _⟩, he⟩,
  intro h,
  apply lt_irrefl y,
  rwa [← h, he] at hy₂,
end

lemma intermediate_value_Ioo {a b : α} (hab : a ≤ b) {f : α → δ} (hf : continuous_on f (Icc a b)) :
  Ioo (f a) (f b) ⊆ f '' (Ioo a b) :=
begin
  rintros y ⟨hy₁, hy₂⟩,
  obtain ⟨x, ⟨hx₁, hx₂⟩, he⟩ := intermediate_value_Icc hab hf ⟨le_of_lt hy₁, le_of_lt hy₂⟩,
  refine ⟨x, ⟨lt_of_le_of_ne hx₁ _, lt_of_le_of_ne hx₂ _⟩, he⟩,
  all_goals { intro h, apply lt_irrefl y, },
  rwa [h, he] at hy₁,
  rwa [← h, he] at hy₂,
end

end densely_ordered

end conditionally_complete_linear_order

end order_topology