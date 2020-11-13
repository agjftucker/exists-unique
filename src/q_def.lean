import finset.powerset
import finset.lattice

local prefix `𝒫`:100 := λ {α : Type} (s : finset α), {t // t ≤ s}

section
variables {α : Type*} [semilattice_sup_bot α] (r : α → α → Prop)

inductive q : α → Prop
| base : q ⊥
| succ {b c : α} : c < b → r c b → q c → q b

end

section
set_option old_structure_cmd true

class bounded_join_semilattice (α : Type*) extends order_top α, semilattice_sup_bot α

variables {α : Type*} [semilattice_sup_bot α] {a : α}

instance semi_sup_bot_of_bdd_above : semilattice_sup_bot {b // b ≤ a} :=
subtype.semilattice_sup_bot bot_le (fun b c hb hc, sup_le hb hc)

instance : bounded_join_semilattice {b // b ≤ a} :=
{ top := ⟨a, le_refl a⟩,
  le_top := λ ⟨b, h⟩, h,
  ..semi_sup_bot_of_bdd_above }

variables {r : α → α → Prop} {r_ : {b // b ≤ a} → {b // b ≤ a} → Prop}
variables (hr' : ∀ b c, r ↑c ↑b ↔ r_ c b)

include hr'

lemma q_on_subsets_of_q : ∀ b, q r ↑b → q r_ b :=
begin
  rintros ⟨b, hb⟩ (hb' : q r b),
  induction hb' with b c hlt hr hq hq',
  { exact q.base, },
  { have hc := trans (le_of_lt hlt) hb,
    apply @q.succ _ _ r_ ⟨b, hb⟩ ⟨c, hc⟩ hlt,
    { rwa ←hr', },
    { apply hq', }, },
end

lemma q_of_q_on_subsets : ∀ b, q r_ b → q r ↑b :=
begin
  rintros b hb,
  induction hb with b c hlt hr hq hq',
  { exact q.base, },
  { apply @q.succ _ _ r b c hlt,
    { rwa hr', },
    { exact hq', }, },
end

lemma q_iff_q_on_subsets : ∀ b, q r ↑b ↔ q r_ b :=
begin
  intro b,
  split,
  { exact q_on_subsets_of_q hr' b, },
  { exact q_of_q_on_subsets hr' b, },
end

end

section
variables {α : Type*} [bounded_join_semilattice α] {r : α → α → Prop}

variable hr₁ (b c d : α) : c < ⊤ → d ≤ c → r d b → r c b
variable hr₂ (b c d : α) : r d b → r d c → r d (b ⊔ c)

include hr₁

lemma hr₄ {b : α} : ⊥ < b → b < ⊤ → q r b → r b b :=
begin
  intros hb ht hq,
  rcases hq with _ | ⟨_, c, hlt, hr, hq⟩,
  { exfalso,
    exact not_lt_bot hb, },
  { exact hr₁ _ _ _ ht (le_of_lt hlt) hr, },
end

include hr₂

lemma hr₅ {b c d : α} : b ⊔ d < ⊤ → r d c → q r b → r (b ⊔ d) (b ⊔ c) :=
begin
  intros ht hr hq,
  cases lt_or_eq_of_le (order_bot.bot_le b) with hb hb,
  { apply hr₂,
    { apply hr₁ _ _ _ ht le_sup_left,
      refine hr₄ hr₁ hb _ hq,
      exact lt_of_le_of_lt le_sup_left ht, },
    { exact hr₁ _ _ _ ht le_sup_right hr, }, },
  { rw [← hb, bot_sup_eq, bot_sup_eq],
    exact hr, },
end

lemma q_of_sup_of_foreach : ∀ b c, q r b → q r c → q r (b ⊔ c) :=
begin
  rintros b c hb hc,
  apply hc.rec_on,
  { convert hb,
    exact sup_bot_eq, },
  { intros c d hd hr hq,
    cases lt_or_eq_of_le (sup_le_sup_left (le_of_lt hd) b) with hlt he,
    { apply q.succ hlt,
      exact hr₅ hr₁ hr₂ (lt_of_lt_of_le hlt le_top) hr hb, },
    { intro h,
      rwa ←he, }, },
end

lemma q_of_sup_of_forall (s : finset α) : (∀ b ∈ s, q r b) → q r (s.sup id) :=
begin
  intro h,
  apply finset.of_sup_of_forall,
  apply q.base,
  apply q_of_sup_of_foreach hr₁ hr₂,
  exact h,
end

end

section

variables {β : Type} [decidable_eq β]
variables {A : finset β} (r : 𝒫 A → 𝒫 A → Prop) [decidable_rel r]

variable [decidable_pred (q r)] --should be able to prove this

def map_id : {B // B ∈ A.powerset} → {B // B ≤ A} :=
subtype.map id (λ B, finset.mem_powerset.mp)

def φ : 𝒫 A :=
((A.powerset.attach.image map_id).filter (q r)).sup id

variable hr₁ (B C D : 𝒫 A) : C < ⊤ → D ≤ C → r D B → r C B
variable hr₂ (B C D : 𝒫 A) : r D B → r D C → r D (B ⊔ C)

include hr₁ hr₂

example : q r (φ r) :=
begin
  apply q_of_sup_of_forall hr₁ hr₂,
  intros B hB,
  rw finset.mem_filter at hB,
  exact hB.2,
end

end
