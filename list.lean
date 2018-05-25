
universe variables uu vv

variables {α : Type uu} {β : Type vv}

namespace list

inductive perm : list α → list α → Prop
| nil   : perm [] []
| skip  : Π (x : α) {l₁ l₂ : list α}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : Π (x y : α) (l : list α), perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃
open perm

infix ~ := perm

@[refl] protected theorem perm.refl : ∀ (l : list α), l ~ l
| []      := perm.nil
| (x::xs) := skip x (perm.refl xs)

@[symm] protected theorem perm.symm {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
perm.rec_on p
  perm.nil
  (λ x l₁ l₂ p₁ r₁, skip x r₁)
  (λ x y l, swap y x l)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₂ r₁)

@[simp] theorem perm_cons_app (a : α) (l : list α) : l ++ [a] ~ a::l := sorry

theorem perm_cons (a : α) {l₁ l₂ : list α} : a::l₁ ~ a::l₂ ↔ l₁ ~ l₂ := sorry

end list

def rotate : nat → list α → list α 
| n [] := []
| 0 (h::t) := (h::t)
| (n+1) (h::t) := (rotate n t) ++ [h]

lemma perm_rotate : ∀ (n) (as : list α), as ~ rotate n as 
| 0 [] := list.perm.refl _
| (n+1) [] := list.perm.refl _
| 0 (a::as) := list.perm.refl _
| (n+1) (a::as) := 
  begin
    simp [rotate], 
    apply list.perm.symm,
    apply list.perm.trans,
    apply list.perm_cons_app,
    rewrite list.perm_cons,
    apply list.perm.symm,
    apply perm_rotate
  end
  