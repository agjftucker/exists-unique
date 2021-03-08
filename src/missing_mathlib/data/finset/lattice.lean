import data.finset.lattice
import missing_mathlib.data.finset.fold
import missing_mathlib.order.bounded_lattice

variables {α β γ : Type*}

namespace finset
open multiset order_dual

section sup
variables [semilattice_sup_bot α]

variables {s s₁ s₂ : finset β} {f : β → α}

@[simp] lemma sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f :=
fold_cons h

-- a proof of sup_lt_iff without classical.choice
@[simp] protected lemma sup_lt_iff' [is_total α (≤)] {a : α} (ha : ⊥ < a) :
  s.sup f < a ↔ (∀ b ∈ s, f b < a) :=
begin
  split,
  { intros h b hb,
    exact lt_of_le_of_lt (le_sup hb) h, },
  { intro h,
    induction s using finset.induction' with c s hc ih,
    { rwa sup_empty, },
    { rw [sup_cons, _root_.sup_lt_iff], -- TODO: remove 'root', check on 'protected'
      split,
      { apply h,
        exact mem_cons.2 (or.inl rfl), },
      { apply ih,
        intros b hb,
        apply h,
        exact mem_cons.2 (or.inr hb), }, }, },
end

-- a proof of comp_sup_eq_sup_comp without classical.choice
lemma comp_sup_eq_sup_comp' [semilattice_sup_bot γ] (g : α → γ)
  (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
begin
  induction s using finset.induction' with c s hc ih,
  { exact bot, },
  { rw [sup_cons, sup_cons, g_sup],
    congr,
    exact ih, },
end

lemma of_sup_of_forall {p : α → Prop} (h0 : p ⊥)
  (hp : ∀ (a₁ a₂ : α), p a₁ → p a₂ → p (a₁ ⊔ a₂)) (hs : ∀ b ∈ s, p (f b)) : p (s.sup f) :=
begin
  induction s using finset.induction' with c s hc ih,
  { exact h0, },
  { rw sup_cons,
    apply hp,
    { apply hs,
      rw mem_cons,
      exact or.inl rfl, },
    { apply ih,
      intros b hb,
      apply hs,
      rw mem_cons,
      exact or.inr hb, }, },
end

end sup

section inf
variables [semilattice_inf_top α]

variables {s s₁ s₂ : finset β} {f : β → α}

@[simp] lemma inf_cons {b : β} (h : b ∉ s) : (cons b s h).inf f = f b ⊓ s.inf f :=
@sup_cons (order_dual α) _ _ _ _ _ h

-- sup_lt_iff and lt_inf_iff should probably be declared protected
@[simp] protected lemma lt_inf_iff' [is_total α (≤)] {a : α} (ha : a < ⊤) :
  a < s.inf f ↔ (∀b ∈ s, a < f b) :=
@finset.sup_lt_iff (order_dual α) _ _ _ _ _ _ ha

lemma of_inf_of_forall {p : α → Prop} (h0 : p ⊤)
  (hp : ∀ (a₁ a₂ : α), p a₁ → p a₂ → p (a₁ ⊓ a₂)) (hs : ∀ b ∈ s, p (f b)) : p (s.inf f) :=
@of_sup_of_forall (order_dual α) _ _ _ _ _ h0 hp hs

end inf

section sup'
variables [semilattice_sup α]

lemma sup_of_mem {s : finset β} (f : β → α) {b : β} (h : b ∈ s) :
  ∃ (a : α), @sup (with_bot α) _ _ s (coe ∘ f) = ↑a :=
(@le_sup (with_bot α) _ _ _ _ _ h (f b) rfl).imp (fun b, Exists.fst)

lemma le_sup_of_mem {s : finset β} (f : β → α) {b : β} (h₁ : b ∈ s) {a : α}
  (h₂ : @sup (with_bot α) _ _ s (coe ∘ f) = ↑a) : f b ≤ a :=
begin
  rcases @le_sup (with_bot α) _ _ _ _ _ h₁ (f b) rfl with ⟨c, hb, ab⟩,
  cases h₂.symm.trans hb,
  assumption,
end

def sup' (s : finset β) (H : s.nonempty) (f : β → α) : α :=
option.get $ let ⟨k, hk⟩ := H in option.is_some_iff_exists.2 (sup_of_mem f hk)

@[simp] lemma coe_sup'_eq_sup_coe {s : finset β} (H : s.nonempty) (f : β → α) :
  ((s.sup' H f : α) : with_bot α) = s.sup (coe ∘ f) :=
by rw [sup', ←with_bot.some_eq_coe, option.some_get]

lemma le_sup' {s : finset β} (f : β → α) {b : β} (H2 : b ∈ s) : f b ≤ s.sup' ⟨b, H2⟩ f :=
le_sup_of_mem f H2 $ option.get_mem _

lemma sup'_le {s : finset β} (H : s.nonempty) (f : β → α) {a : α} (H2 : ∀ b ∈ s, f b ≤ a) :
  s.sup' H f ≤ a :=
begin
  rw [←with_bot.coe_le_coe, coe_sup'_eq_sup_coe],
  apply @sup_le (with_bot α) β _,
  intros b hb,
  rw with_bot.coe_le_coe,
  exact H2 b hb,
end

variables {s : finset β} (H : s.nonempty) {f : β → α}

lemma sup'_cons {b : β} (hb : b ∉ s) :
  (cons b s hb).sup' (nonempty_cons hb) f = f b ⊔ s.sup' H f :=
by { rw ←with_bot.coe_eq_coe, simp }

lemma sup'_insert [decidable_eq β] {b : β} (h : (insert b s).nonempty) :
  (insert b s).sup' h f = f b ⊔ s.sup' H f :=
by { rw ←with_bot.coe_eq_coe, simp }

-- sup_lt_iff is marked 'simp', should this be?
lemma sup'_lt_iff [is_total α (≤)] {a : α} : s.sup' H f < a ↔ (∀ b ∈ s, f b < a) :=
begin
  rw [← with_bot.coe_lt_coe, coe_sup'_eq_sup_coe],
  rw finset.sup_lt_iff' (with_bot.bot_lt_coe a),
  simp_rw with_bot.coe_lt_coe,
end

lemma of_sup'_of_forall {p : α → Prop}
  (hp : ∀ (a₁ a₂ : α), p a₁ → p a₂ → p (a₁ ⊔ a₂)) (hs : ∀ b ∈ s, p (f b)) : p (s.sup' H f) :=
begin
  let p' := @option.rec α (fun _, Prop) true p,
  change p' ↑(s.sup' H f),
  rw coe_sup'_eq_sup_coe,
  refine of_sup_of_forall trivial _ hs,
  intros a₁ a₂ h₁ h₂,
  cases a₁,
  { rwa [with_bot.none_eq_bot, bot_sup_eq], },
  { cases a₂,
    exact h₁,
    exact hp a₁ a₂ h₁ h₂, },
end

end sup'

section inf'
variable [semilattice_inf α]

lemma inf_of_mem {s : finset β} (f : β → α) {b : β} (h : b ∈ s) :
  ∃ (a : α), @inf (with_top α) _ _ s (coe ∘ f) = ↑a :=
@sup_of_mem (order_dual α) _ _ _ _ _ h

lemma inf_le_of_mem {s : finset β} (f : β → α) {b : β} (h₁ : b ∈ s) {a : α}
  (h₂ : @inf (with_top α) _ _ s (coe ∘ f) = ↑a) : a ≤ f b :=
@le_sup_of_mem (order_dual α) _ _ _ _ _ h₁ _ h₂

def inf' (s : finset β) (H : s.nonempty) (f : β → α) : α :=
@sup' (order_dual α) _ _ s H f

@[simp] lemma coe_inf'_eq_inf_coe {s : finset β} (H : s.nonempty) (f : β → α) :
  ((s.inf' H f : α) : with_top α) = s.inf (coe ∘ f) :=
@coe_sup'_eq_sup_coe (order_dual α) _ _ _ H f

variables {s : finset β} (H : s.nonempty) {f : β → α}

lemma lt_inf'_iff [is_total α (≤)] {a : α} : a < s.inf' H f ↔ (∀ b ∈ s, a < f b) :=
@sup'_lt_iff (order_dual α) _ _ _ H _ _ _

lemma of_inf'_of_forall {p : α → Prop}
  (hp : ∀ (a₁ a₂ : α), p a₁ → p a₂ → p (a₁ ⊓ a₂)) (hs : ∀ b ∈ s, p (f b)) : p (s.inf' H f) :=
@of_sup'_of_forall (order_dual α) _ _ _ H _ _ hp hs

end inf'

section sup
variable [semilattice_sup_bot α]
variables {s : finset β} (H : s.nonempty) {f : β → α}

lemma sup'_eq_sup : s.sup' H f = s.sup f :=
begin
  rw ← with_bot.coe_eq_coe,
  rw coe_sup'_eq_sup_coe,
  induction s using finset.induction' with c s hc ih,
  { exfalso,
    exact not_nonempty_empty H, },
  { rw [sup_cons, sup_cons],
    rcases s.eq_empty_or_nonempty with rfl | h,
    { rw [sup_empty, sup_empty, sup_bot_eq, sup_bot_eq], },
    { rw ih h,
      refl, }, },
end

-- a simplified proof of sup_closed_of_sup_closed
lemma sup_closed_of_sup_closed' {s : set α} (t : finset α) (htne : t.nonempty) (h_subset : ↑t ⊆ s)
  (h : ∀⦃a b⦄, a ∈ s → b ∈ s → a ⊔ b ∈ s) : t.sup id ∈ s :=
begin
  rw ← sup'_eq_sup htne,
  exact of_sup'_of_forall _ h h_subset,
end

end sup

section inf
variable [semilattice_inf_top α]
variables {s : finset β} (H : s.nonempty) {f : β → α}

lemma inf'_eq_inf : s.inf' H f = s.inf f :=
@sup'_eq_sup (order_dual α) _ _ _ H _

lemma inf_closed_of_inf_closed {s : set α} (t : finset α) (htne : t.nonempty) (h_subset : ↑t ⊆ s)
  (h : ∀⦃a b⦄, a ∈ s → b ∈ s → a ⊓ b ∈ s) : t.inf id ∈ s :=
@sup_closed_of_sup_closed (order_dual α) _ _ t htne h_subset h

end inf

section sup
variables {C : β → Type*} [Π (b : β), semilattice_sup_bot (C b)]

protected lemma sup_apply (s : finset α) (f : α → Π (b : β), C b) (b : β) :
  s.sup f b = s.sup (fun a, f a b) :=
begin
  induction s using finset.induction' with c s hc ih,
  { refl, },
  { rw [sup_cons, sup_cons, sup_apply, ih], },
end

end sup

section inf
variables {C : β → Type*} [Π (b : β), semilattice_inf_top (C b)]

protected lemma inf_apply (s : finset α) (f : α → Π (b : β), C b) (b : β) :
  s.inf f b = s.inf (fun a, f a b) :=
@finset.sup_apply _ _ (fun b, order_dual (C b)) _ s f b

end inf

section sup'
variables {C : β → Type*} [Π (b : β), semilattice_sup (C b)]

lemma sup'_apply {s : finset α} (h : s.nonempty) (f : α → Π (b : β), C b) (b : β) :
  s.sup' h f b = s.sup' h (fun a, f a b) :=
begin
  rw [← with_bot.coe_eq_coe, coe_sup'_eq_sup_coe],
  let g := @option.rec (Π b, C b) (fun _, with_bot (C b)) ⊥ (fun f, ↑(f b)),
  change g ↑(s.sup' h f) = s.sup (fun a, g ↑(f a)),
  rw coe_sup'_eq_sup_coe,
  refine comp_sup_eq_sup_comp g _ rfl,
  intros f₁ f₂,
  cases f₁,
  { rw [with_bot.none_eq_bot, bot_sup_eq],
    exact bot_sup_eq.symm, },
  { cases f₂;
    refl, },
end

end sup'

section inf'
variables {C : β → Type*} [Π (b : β), semilattice_inf (C b)]

lemma inf'_apply {s : finset α} (h : s.nonempty) (f : α → Π (b : β), C b) (b : β) :
  s.inf' h f b = s.inf' h (fun a, f a b) :=
@sup'_apply _ _ (fun b, order_dual (C b)) _ _ h f b

end inf'

end finset
