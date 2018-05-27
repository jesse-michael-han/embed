import data.list.perm

universe variables uu vv

variables {α : Type uu} {β : Type vv}

namespace list

def rotate : nat → list α → list α 
| n [] := []
| 0 (h::t) := (h::t)
| (n+1) (h::t) := (rotate n t) ++ [h]

lemma perm_rotate : ∀ (n) (as : list α), rotate n as ~ as
| 0 [] := list.perm.refl _
| (n+1) [] := list.perm.refl _
| 0 (a::as) := list.perm.refl _
| (n+1) (a::as) := 
  begin
    simp [rotate], 
    apply perm.trans,
    apply perm_cons_app,
    rewrite perm_cons,
    apply perm_rotate
  end
  
theorem forall_mem_singleton {p : α → Prop} {a : α} :
  (∀ x ∈ [a] , p x) ↔ p a  :=
begin
  rewrite forall_mem_cons, apply iff.intro; intro h,
  apply h.elim_left, apply and.intro h (forall_mem_nil _)
end

end list