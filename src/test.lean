import lia.cooper.main

set_option pp.all true
-- lemma foo [ordered_comm_group int] : false := sorry 

-- lemma bar : false := foo 

lemma foo : ∃ {a : int}, a = 5 := 
by cooper

#exit
∀ x y, (x = y ↔ ∀ z, (x + z = y + z)), a + c ≠ b + c ⊢ a ≠ b 