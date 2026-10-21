variable (p q r: Prop)

theorem EM : p ∨ ¬p := by
  grind

#print EM
#print EM._proof_1_1

-- intuitionistic theoremы
example : p → ¬¬p := λ hp hnp ↦ hnp hp

example : (p → q) → (q → r) → (p → r) := λ hpq hqr ↦ hqr ∘ hpq

example : p → p ∨ q := Or.inl

example : q → p ∨ q := Or.inr

example : (p → r) → (q → r) → (p ∨ q → r) := λ hpr hqr hpq ↦ Or.elim hpq hpr hqr

example : p ∧ q → p := And.left

example : p ∧ q → q := And.right

example : (p → q) → (p → r) → (p → q ∧ r) := λ hpq hpr hp ↦ ⟨hpq hp, hpr hp⟩

example : (p → q → r) ↔ p ∧ q → r := ⟨
  λ hpqr ⟨hp, hq⟩ ↦ hpqr hp hq,
  λ hpq_r hp hq ↦ hpq_r ⟨hp, hq⟩⟩

example : (p ∧ ¬p) → q := λ ⟨hp, hnp⟩ ↦ False.elim (hnp hp)

example : (p → (p ∧ ¬p)) → ¬p := λ hppnp hp ↦ (hppnp hp).right hp

example : (¬p ∨ q) → (p → q) := λ hnpq hp ↦ Or.elim hnpq
  (λ hnp ↦ False.elim (hnp hp))
  (id)

example : ¬¬¬p → ¬p := λ hnnnp hp ↦ Not.elim hnnnp (λ hnp ↦ hnp hp)

example : (p → q) → (¬q → ¬p) := λ hpq hnq ↦ hnq ∘ hpq

example : (p → ¬q) → (q → ¬p) := λ hpnq hq hp ↦ (hpnq hp) hq

example : ¬¬(p → q) → (p → ¬¬q) := λ hnnpq hp hnq ↦ Not.elim hnnpq (λ hpq ↦ hnq (hpq hp))


-- classical theorems
example : ¬¬p → p := Classical.byContradiction

example : (p → q) → ¬p ∨ q := λ hpq ↦ Or.elim (Classical.em p)
  (Or.inr ∘ hpq)
  (Or.inl)
