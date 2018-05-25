import .exp .print

namespace prop

variable {α : Type}

class is_symb (α : Type) :=
(true : α) (false : α) (not : α)
(and : α) (or : α) (imp : α)

def true [is_symb α] := @exp.cst α (is_symb.true α)
notation  `⊤'` := true

def false [is_symb α] := @exp.cst α (is_symb.false α)
notation  `⊥'` := false

def not [is_symb α] (p : exp α) := exp.app (exp.cst (is_symb.false α)) p
notation  `¬'` p := not p

def and [is_symb α] (p q : exp α) := exp.app (exp.app (exp.cst (is_symb.and α)) p) q
notation  p `∧'` q := and p q

def or [is_symb α] (p q : exp α) := exp.app (exp.app (exp.cst (is_symb.or α)) p) q
notation  p `∨'` q := or p q

def imp [is_symb α] (p q : exp α) := exp.app (exp.app (exp.cst (is_symb.imp α)) p) q
notation  p `→'` q := imp p q

inductive symb : Type 
| atom : string → symb 
| true : symb
| false : symb
| not : symb
| and : symb
| or  : symb
| imp : symb

instance : decidable_eq symb :=
by tactic.mk_dec_eq_instance

instance : is_symb symb := 
{ true  := symb.true,
  false := symb.false,
  not   := symb.not,
  and   := symb.and,
  or    := symb.or,
  imp   := symb.imp }

def A' (s : string) := @exp.cst symb (symb.atom s)

inductive thm [is_symb α] : list (exp α) → list (exp α) → Prop
| id : ∀ Γ Δ p, thm (p::Γ) (p::Δ) 
| truer : ∀ Γ Δ, thm Γ (⊤'::Δ) 
| falsel : ∀ Γ Δ, thm (⊥'::Γ) Δ 
| andl : ∀ Γ Δ p q, thm ((p ∧' q)::Γ) Δ → thm (p::q::Γ) Δ 
| andr : ∀ Γ Δ p q, 
    thm Γ (p::Δ) → thm Γ (q::Δ) 
    → thm Γ ((p ∧' q)::Δ)
| orl : ∀ Γ Δ p q, 
    thm (p::Γ) Δ → thm (q::Γ) Δ 
    → thm ((p ∨' q)::Γ) Δ 
| orr : ∀ Γ Δ p q, thm Γ (p::q::Δ) → thm Γ ((p ∨' q)::Δ)
| impl : ∀ Γ Δ p q, 
    thm Γ (p::Δ) → thm (q::Γ) Δ 
    → thm ((p →' q)::Γ) Δ 
| impr : ∀ Γ Δ p q, thm (p::Γ) (q::Δ) → thm Γ ((p →' q)::Δ) 
| wl : ∀ Γ Δ p, thm Γ Δ → thm (p::Γ) Δ 
| wr : ∀ Γ Δ p, thm Γ Δ → thm Γ (p::Δ) 
| cl : ∀ Γ Δ p, thm (p::p::Γ) Δ → thm (p::Γ) Δ 
| cr : ∀ Γ Δ p, thm Γ (p::p::Δ) → thm Γ (p::Δ) 
| pl : ∀ Γ Γ' Δ, Γ ~ Γ' → thm Γ Δ → thm Γ' Δ 
| pr : ∀ Γ Δ Δ', Δ ~ Δ' → thm Γ Δ → thm Γ Δ' 

lemma thm.rl [is_symb α] : 
  ∀ n (Γ Δ : list (exp α)), thm (rotate n Γ) Δ → thm Γ Δ :=
begin
  intros n Γ Δ h, apply thm.pl _ _ _ _ h, 
  apply list.perm.symm, apply perm_rotate
end
 
lemma thm.rr [is_symb α] : 
  ∀ n (Γ Δ : list (exp α)), thm Γ (rotate n Δ) → thm Γ Δ :=
begin
  intros n Γ Δ h, apply thm.pr _ _ _ _ h, 
  apply list.perm.symm, apply perm_rotate
end

open expr tactic

meta def getsqt : tactic (list (exp symb) × list (exp symb)) :=
do `(thm %%Γe %%Δe) ← tactic.target,
    Γ ← eval_expr (list (exp symb)) Γe, 
    Δ ← eval_expr (list (exp symb)) Δe, 
    return (Γ,Δ)

def fml2str : exp symb → string 
| (exp.app (exp.cst s) p) := 
  if s = (is_symb.not symb)
  then "¬" ++ fml2str p
  else "ERROR"
| (exp.app (exp.app (exp.cst s) p) q) := 
  if s = (is_symb.and symb)
  then "(" ++ fml2str p ++ " ∧ " ++ fml2str q ++ ")" else 
  if s = (is_symb.or symb)
  then "(" ++ fml2str p ++ " ∨ " ++ fml2str q ++ ")" else 
  if s = (is_symb.imp symb)
  then "(" ++ fml2str p ++ " → " ++ fml2str q ++ ")" else "ERROR"
| (exp.cst s) := 
  if s = is_symb.true symb
  then "⊤" else
  if s = is_symb.false symb
  then "⊥" else
  match s with 
  | (symb.atom str) := str 
  | _ := "ERROR"
  end
| _ := "ERROR"

meta def showgoal : tactic unit :=
(do (Γ,Δ) ← getsqt, trace (sqt2str fml2str Γ Δ)) <|> trace "No Goals"

/- Examples (Hilbert System Axioms) -/

example : thm [] [A' "φ" →' A' "φ"] :=
begin
  showgoal,
  apply thm.impr,
  apply thm.id,
  showgoal
end

example : thm [] [A' "φ" →' (A' "ψ" →' A' "φ")] :=
begin
  showgoal,
  apply thm.impr,
  apply thm.impr,
  apply thm.rl 1, 
  apply thm.id,
  showgoal
end

example : thm [] [(A' "φ" →' (A' "ψ" →' A' "χ")) →' ((A' "φ" →' A' "ψ") →' (A' "φ" →' A' "χ"))] :=
begin
  showgoal,
  apply thm.impr,
  apply thm.impr,
  apply thm.impr,
  apply thm.rl 2, 
  apply thm.impl,
  apply thm.rl 1, 
  apply thm.id,
  apply thm.impl,
  apply thm.impl,
  apply thm.id,
  apply thm.id,
  apply thm.id,
  showgoal
end

end prop
