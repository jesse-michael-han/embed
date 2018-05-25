import .exp

variable {α : Type}

open expr tactic

def sqt2str (exp2str : exp α → string) (Γ Δ : list (exp α)) : string := 
lst2str exp2str Γ ++ " ⊢ " ++ lst2str exp2str Δ