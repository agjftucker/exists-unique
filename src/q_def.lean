import missing_mathlib.data.finset.powerset
import missing_mathlib.data.finset.lattice

local prefix `𝒫`:100 := λ {α : Type} (s : finset α), {t // t ≤ s}

section q_definition

variables {α : Type*} [order_bot α] (r : α → α → Prop)

inductive q : α → Prop
| base : q ⊥
| succ {b c : α} : c < b → r c b → q c → q b

end q_definition

section
set_option old_structure_cmd true

class bounded_join_semilattice (α : Type*) extends order_top α, semilattice_sup_bot α

variables {α : Type*} [semilattice_sup_bot α] {a : α}

instance semi_sup_bot_of_bdd_above : semilattice_sup_bot {b // b ≤ a} :=
subtype.semilattice_sup_bot bot_le (fun _ _, sup_le)

instance : bounded_join_semilattice {b // b ≤ a} :=
{ top := ⟨a, refl _⟩,
  le_top := fun ⟨b, h⟩, h,
  ..semi_sup_bot_of_bdd_above }

variables {r : α → α → Prop} {r_ : {b // b ≤ a} → {b // b ≤ a} → Prop}
variables (hr_ : ∀ b c, c < b → (r ↑c ↑b ↔ r_ c b))

include hr_

lemma q_on_subsets_of_q : ∀ b, q r ↑b → q r_ b :=
begin
  rintros ⟨b, hb⟩ (hb' : q r b),
  induction hb' with b c hlt hr hq hq',
  { exact q.base, },
  { have hc := trans (le_of_lt hlt) hb,
    apply @q.succ _ _ r_ ⟨b, hb⟩ ⟨c, hc⟩ hlt,
    { rwa ←(hr_ ⟨b, hb⟩ ⟨c, hc⟩ hlt), },
    { apply hq', }, },
end

lemma q_of_q_on_subsets : ∀ b, q r_ b → q r ↑b :=
begin
  rintros b hb,
  induction hb with b c hlt hr hq hq',
  { exact q.base, },
  { apply @q.succ _ _ r b c hlt,
    { rwa (hr_ b c hlt), },
    { exact hq', }, },
end

lemma q_iff : ∀ b, q r ↑b ↔ q r_ b :=
begin
  intro b,
  split,
  { exact q_on_subsets_of_q hr_ b, },
  { exact q_of_q_on_subsets hr_ b, },
end

lemma q_eq : q r_ = (q r) ∘ coe :=
begin
  funext b,
  rw ←q_iff hr_,
end

end

namespace subtype

variables {α : Type*}

def order_bot [order_bot α] {P : α → Prop} (Pbot : P ⊥) : order_bot {x : α // P x} :=
{ bot := ⟨⊥, Pbot⟩,
  bot_le := λ x, bot_le,
  ..subtype.partial_order P }

end subtype

namespace si  --structural induction

variables {β : Type} [decidable_eq β]

section decidable₁

variables {𝒮 : set (finset β)}

def strong_induction {p : 𝒮 → Sort*} : (∀ (B : 𝒮), (∀ C, C < B → p C) → p B) → (∀ B, p B) :=
fun h', suffices h : ∀ (B : finset β) (hB : B ∈ 𝒮), p ⟨B, hB⟩, from (fun ⟨B, hB⟩, h B hB),
finset.strong_induction (fun B ih hB, h' ⟨B, hB⟩ (fun ⟨C, hC⟩ hlt, ih C hlt hC))

variables [decidable_pred 𝒮] (𝒮bot : 𝒮 ⊥)
include 𝒮bot

variables (r : 𝒮 → 𝒮 → Prop) [decidable_rel r]

def decidable_of_ssubsets : let 𝒮b := subtype.order_bot 𝒮bot in
  ∀ B, (∀ C < B, decidable (@q _ 𝒮b r C)) → decidable (@q _ 𝒮b r B) :=
begin
  intros 𝒮b B ih,
  apply dite (B = 𝒮b.bot),
  { intro hB,
    apply is_true,
    rw hB,
    apply q.base, },
  intro hB,
  have : ∀ (C : finset β) (hlt : C < B), decidable (∃ (h : 𝒮 C), r ⟨C, h⟩ B ∧ @q _ 𝒮b r ⟨C, h⟩),
  { intros C hlt,
    apply @exists_prop_decidable _ _ _ _,
    apply_instance,
    intro hC,
    apply @and.decidable _ _ _ _,
    apply_instance,
    exact ih ⟨C, hC⟩ hlt, },
  cases finset.decidable_exists_of_ssubsets this with hne he,
  { apply is_false,
    intro hq,
    rcases hq with _ | ⟨_, ⟨C, hC⟩, hlt, hr, hq⟩,
    { apply hB,
      refl, },
    { apply hne,
      refine ⟨C, _, hC, hr, hq⟩,
      exact hlt, }, },
  { apply is_true,
    rcases he with ⟨C, hlt, hC, hr, hq⟩,
    apply @q.succ _ 𝒮b _ _ ⟨C, hC⟩ hlt hr hq, },
end

instance q_decidable₁ : decidable_pred (@q _ (subtype.order_bot 𝒮bot) r) :=
strong_induction (decidable_of_ssubsets 𝒮bot r)

end decidable₁

section decidable₂

variables {r : finset β → finset β → Prop} [decidable_rel r]

instance q_decidable₂ : decidable_pred (q r) :=
begin
  intro A,
  let 𝒮b := @subtype.order_bot (finset β) _ set.univ trivial,
  apply decidable_of_iff (@q _ 𝒮b (fun C B, r ↑C ↑B) ⟨A, trivial⟩),
  split,
  { intro hq,
    apply @q.rec_on _ 𝒮b _ (fun B, q r ↑B) _ hq,
    { apply q.base, },
    { intros B C hlt hr hq hq',
      apply @q.succ (finset β) _ _ _ _ hlt hr hq', }, },
  { intro hq,
    apply q.rec_on hq,
    { apply q.base, },
    { intros B C hlt hr hq hq',
      apply @q.succ _ 𝒮b _ ⟨B, trivial⟩ ⟨C, trivial⟩ hlt,
      { exact hr, },
      { exact hq', }, }, },
end

end decidable₂

section φ_definition

variables {A : finset β} (r_ : 𝒫 A → 𝒫 A → Prop) [decidable_rel r_]

def id' : {B // B ∈ A.powerset} ↪ 𝒫 A :=
(function.embedding.refl _).subtype_map (fun B, finset.mem_powerset.mp)

def φ : 𝒫 A :=
((A.powerset.attach.map id').filter (q r_)).sup id

end φ_definition

section φ_properties

variables {r : finset β → finset β → Prop} [decidable_rel r]

variables {A : finset β} {rA : 𝒫 A → 𝒫 A → Prop} [decidable_rel rA]
variables (hrA : ∀ C D, D < C → (r ↑D ↑C ↔ rA D C))
include hrA

lemma le_φ_of_q : ∀ (B : 𝒫 A), q r ↑B → B ≤ φ rA :=
begin
  rintros ⟨B, hB⟩ hq,
  apply @finset.le_sup (𝒫 A) _ _ _ id,
  rw finset.mem_filter,
  split,
  { rw finset.mem_map,
    use [B, finset.mem_powerset.2 hB, finset.mem_attach _ _, rfl], },
  { rwa q_iff hrA at hq, },
end

lemma φ_eq : (φ rA : finset β) = (A.powerset.filter (q r)).sup id :=
begin
  rw [φ, finset.sup_coe],
  simp [q_eq hrA],
  rw [finset.sup_def, finset.sup_def, multiset.map_id],
  congr,
  let coe' : 𝒫 A ↪ finset β := function.embedding.subtype _,
  conv_lhs
  { change ((A.powerset.attach.map id').filter (q r ∘ coe')).val.map coe',
    rw [←finset.map_val, ←finset.map_filter, finset.map_map], },
  congr,
  exact finset.attach_map_val,
end

variables {B : finset β} {rB : 𝒫 B → 𝒫 B → Prop} [decidable_rel rB]
variables (hrB : ∀ C D, D < C → (r ↑D ↑C ↔ rB D C))

include hrB

lemma φ_mono : B ≤ A → (φ rB : finset β) ≤ φ rA :=
begin
  intro h,
  rw [φ_eq hrA, φ_eq hrB],
  refine finset.sup_mono _,
  apply finset.filter_subset_filter,
  rwa finset.powerset_mono,
end

end φ_properties

end si
