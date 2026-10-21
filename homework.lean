section hw1
variable (α β γ δ : Type)
  -- Define any functions with the following types.
  -- If you can't, explain why

  def ex1 : α → β → α := fun x _ ↦ x
  def ex2 : (α → β → γ) → β → α → γ := fun f x y ↦ f y x
  def ex3 : (α → (β → γ)) → (α → β) → α → γ := fun f g x ↦ f x (g x)
  def ex4 : ((α → β) → γ) → (β → γ → δ) → (α → β) → α → δ :=
      fun f g h x ↦ g (h x) (f h)
  def ex5 : (α → β) → β → α := sorry --impossible
end hw1

section hw2
-- unsolved propositions from the text:
  variable (p q r: Prop)
  example : p → p := id

  theorem comp' {α β γ: Prop} (f: α→β)(g: β→γ): α → γ := g ∘ f
  example : (p → q) → (q → r) → p → r := comp'
-- other methods
  example : (p → q) → (q → r) → p → r := λ hpq hqr hp ↦ hqr (hpq hp)
  example : (p → q) → (q → r) → p → r := λ hpq hqr ↦ hqr ∘ hpq

  example : (p → (q → r)) → (p → q) → p → r := λ hpqr hpq hp ↦ (hpqr hp) (hpq hp)

  example : p ∧ q → q ∧ p := λ ⟨hp, hq⟩ ↦ ⟨hq, hp⟩
  theorem andswap' {α β: Prop} (x: α ∧ β): β ∧ α := ⟨x.2, x.1⟩

  example : (p ∨ True) ∧ True := ⟨Or.inr trivial, trivial⟩

  example : (p → q) → (¬ q → ¬ p) := λ hpq hnq hp ↦ hnq (hpq hp)

  example : p ∧ q ↔ q ∧ p := ⟨andswap', andswap'⟩
-- classical
  example : ¬(p ∧ ¬q) → (p → q) := λ hnpnq hp ↦ Or.elim (Classical.em q)
    id
    (λ nq ↦ False.elim (hnpnq ⟨hp, nq⟩))

-- homework
  /- Classical.em is not required: -/
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := ⟨
      λ ⟨⟨hp, hq⟩, hr⟩ ↦ ⟨hp, ⟨hq, hr⟩⟩, λ ⟨hp, ⟨hq, hr⟩⟩ ↦ ⟨⟨hp, hq⟩, hr⟩⟩
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := ⟨
      λ hpqr ↦ Or.elim hpqr
        (λ hpq ↦ Or.elim hpq
          (Or.inl)
          (Or.inr ∘ Or.inl))
        (Or.inr ∘ Or.inr),
      λ hpqr ↦ Or.elim hpqr
        (Or.inl ∘ Or.inl)
        (λ hqr ↦ Or.elim hqr
          (Or.inl ∘ Or.inr)
          (Or.inr))⟩

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := ⟨
     λ hpqr ↦ Or.elim hpqr
      (λ hp ↦ ⟨Or.inl hp, Or.inl hp⟩)
      (λ ⟨hq, hr⟩ ↦ ⟨Or.inr hq, Or.inr hr⟩),
     λ ⟨hpq, hpr⟩ ↦ Or.elim hpq
      (Or.inl)
      (λ hq ↦ Or.elim hpr
        (Or.inl)
        (λ hr ↦ Or.inr ⟨hq, hr⟩)
      )⟩

  example : (p → (q → r)) ↔ (p ∧ q → r) := ⟨
    λ hpqr ⟨hp, hq⟩ ↦ hpqr hp hq,
    λ hpqr hp hq ↦ hpqr ⟨hp, hq⟩⟩

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := ⟨
    λ hpqr ↦ ⟨hpqr ∘ Or.inl,  hpqr ∘ Or.inr⟩,
    λ ⟨hpr, hqr⟩ hpq ↦ Or.elim hpq hpr hqr⟩

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := ⟨
    λ hnpq ↦ ⟨hnpq ∘ Or.inl, hnpq ∘ Or.inr⟩,
    λ ⟨hnp, hnq⟩ hpq ↦ Or.elim hpq hnp hnq⟩

  example : ¬p ∨ ¬q → ¬(p ∧ q) := λ npnq ↦ Or.elim npnq
    (λ hnp ⟨hp, _⟩ ↦ hnp hp)
    (λ hnq ⟨_, hq⟩ ↦ hnq hq)

  example : ¬(p ∧ ¬p) := λ ⟨hp, hnp⟩ ↦ hnp hp

  example : p ∧ ¬q → ¬(p → q) := λ ⟨hp, hnq⟩ hpq ↦ hnq (hpq hp)

  example : ¬p → (p → q) := λ hnp hp ↦ False.elim (hnp hp)

  example : (¬p ∨ q) → (p → q) := λ hnpq hp ↦ Or.elim hnpq
    (λ hnp ↦ Not.elim hnp hp)
    (id)

  example : p ∨ False ↔ p := ⟨λ hpf ↦ Or.elim hpf id False.elim, Or.inl⟩

  example : p ∧ False ↔ False := ⟨And.right, False.elim⟩

  example : (p → q) → (¬q → ¬p) := λ hpq hnq hp ↦ hnq (hpq hp)

  /- Classical.em is required: -/
  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := λ hpqr ↦
    Or.elim (Classical.em p)
      (λ hp ↦ Or.elim (hpqr hp)
        (λ hq ↦ Or.inl (λ _ ↦ hq))
        (λ hr ↦ Or.inr (λ _ ↦ hr)))
      (Or.inl ∘ Not.elim)

  example : ¬(p ∧ q) → ¬p ∨ ¬q := λ hnpq ↦ Or.elim (Classical.em p)
    (λ hp ↦ Or.elim (Classical.em q) (λ hq ↦ False.elim (hnpq ⟨hp, hq⟩)) (Or.inr))
    (Or.inl)

  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := sorry
  example : (((p → q) → p) → p) := sorry
end hw2

section hw3
-- unsolved propositions from the text
variable (α : Type) (P Q : α → Prop)
example : (∀ (x : α), P x ∧ Q x) ↔ (∀ x : α, P x) ∧ (∀ x : α, Q x) :=
  sorry

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  sorry

/- 2^α ≃ α → Prop (at least classicaly) -/
theorem cantor (f : α → (α → Prop)) :
 ¬∀ S : α → Prop, ∃ x : α, ∀ y : α, S y ↔ f x y :=
  sorry

theorem forall_or_exists_not : (∀ x : α, P x) ∨ (∃ x : α, ¬ P x) :=
  sorry

example (people : Type) (Joe : people) (drinks : people → Prop) :
  ∃ x : people, drinks x → ∀ y : people, drinks y :=
  sorry

-- tactics
variable (p q r : Prop)
example : (p → q) → (¬ q → ¬ p) := by
  sorry

example : p ∧ q ↔ q ∧ p := by
  sorry

example (p q r : Prop) (hp : p) :
  (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  sorry

-- homework
example : ∀ p q : Prop, p ∧ q ↔ ∀ r : Prop, (p → q → r) → r :=
    sorry

  example : ∀ p q : Prop, p ∨ q ↔ ∀ r : Prop, (p → r) → (q → r) → r :=
    sorry

  example : (∃ x : α, P x) ↔ ∀ r : Prop, (∀ x : α, P x → r) → r :=
    sorry

  theorem knaster_tarski
    (R : α → α → Prop)
    (trans : ∀ x y z : α, R x y → R y z → R x z)
    (inf : ∀ P : α → Prop, ∃ m : α,
      (∀ x : α, P x → R m x) ∧
      (∀ z : α, (∀ x : α, P x → R z x) → R z m))
    (f : α → α)
    (mono : ∀ x y : α, R x y → R (f x) (f y)) :
    ∃ p : α, R (f p) p ∧ R p (f p) := sorry

  /-- Explain what this theorem means --/
  theorem girard
    (π : (Type → Type) → Type)
    (Λ : ∀ {X : Type → Type}, ((α : Type) → X α) → π X)
    (ε : ∀ {X : Type → Type}, π X → (α : Type) → X α)
    (β : ∀ {X : Type → Type} (f : (α : Type) → X α) (α : Type),
      ∀ (P : X α → Prop), P (ε (Λ f) α) ↔ P (f α))
    : False :=
    sorry

end hw3
