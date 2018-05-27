def list.max {α : Type} [decidable_linear_order α]  (a : α) : list α → α 
| [] := a 
| (a'::as) := max a' (list.max as)

def lconcat : list string → string 
| [] := ""
| (h::t) := h ++ lconcat t

def lst2str {α : Type} (f : α → string) : list α → string
| [] := ""
| [a] := f a
| (a::as) := f a ++ ", " ++ lst2str as 

open tactic

meta def dec_triv_tac : tactic unit :=
do t ← target, 
   to_expr ``(@of_as_true %%t) >>= apply,
   triv

meta def showmem : nat → tactic unit 
| 0 := to_expr ``(or.inl) >>= apply >> to_expr ``(eq.refl) >>= apply >> skip
| (n+1) := to_expr ``(or.inr) >>= apply >> showmem n
