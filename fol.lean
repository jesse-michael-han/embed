import .prop

namespace fol

variable {α : Type}

class is_symb (α : Type) extends prop.is_symb α :=
(fa : α) (ex : α)

inductive symb : Type 
| fn : string → symb 
| prd : string → symb 
| true : symb
| false : symb
| not : symb
| and : symb
| or  : symb
| imp : symb
| fa  : symb
| ex  : symb

instance : decidable_eq symb :=
by tactic.mk_dec_eq_instance

instance : is_symb symb := 
{ true  := symb.true,
  false := symb.false,
  not   := symb.not,
  and   := symb.and,
  or    := symb.or,
  imp   := symb.imp,
  fa    := symb.fa,
  ex    := symb.ex }

def fa [is_symb α] (p : exp α) := exp.app (exp.cst (is_symb.fa α)) (exp.lam p)
notation  `∀'` p := fa p

def ex [is_symb α] (p : exp α) := exp.app (exp.cst (is_symb.ex α)) (exp.lam p)
notation  `∃'` p := ex p

def pred (P : string) (args : list (exp symb)) : exp symb := 
list.foldl exp.app (exp.cst (symb.prd P)) args

def func (F : string) (args : list (exp symb)) : exp symb := 
list.foldl exp.app (exp.cst (symb.fn F)) args

inductive thm [is_symb α] : list (exp α) → list (exp α) → Prop
| prop : ∀ Γ Δ, prop.thm Γ Δ → thm Γ Δ 
| fal :  ∀ t Γ Δ p, thm ((inst t p)::Γ) Δ → thm ((∀' p)::Γ) Δ
| far :  ∀ k Γ Δ p, k ∉ fvrs_list Γ → k ∉ fvrs_list Δ   
  → thm Γ ((inst (exp.fvr α k) p)::Δ) → thm Γ ((∀' p)::Δ)
| exl :  ∀ k Γ Δ p, k ∉ fvrs_list Γ → k ∉ fvrs_list Δ   
  → thm ((inst (exp.fvr α k) p)::Γ) Δ → thm ((∃' p)::Γ) Δ 
| exr :  ∀ t Γ Δ p, thm Γ ((inst t p)::Δ) → thm Γ ((∃' p)::Δ)

open expr tactic

meta def getsqt : tactic (list (exp symb) × list (exp symb)) :=
do `(thm %%Γe %%Δe) ← tactic.target,
    Γ ← eval_expr (list (exp symb)) Γe, 
    Δ ← eval_expr (list (exp symb)) Δe, 
    return (Γ,Δ)

def fml2str : exp symb → string 
| (exp.app (exp.app e p) q) := 
  if e = exp.cst (prop.is_symb.and symb)
  then "(" ++ fml2str p ++ " ∧ " ++ fml2str q ++ ")" else 
  if e = exp.cst (prop.is_symb.or symb)
  then "(" ++ fml2str p ++ " ∨ " ++ fml2str q ++ ")" else 
  if e = exp.cst (prop.is_symb.imp symb)
  then "(" ++ fml2str p ++ " → " ++ fml2str q ++ ")" else 
    fml2str (exp.app e p) ++ " " ++ fml2str q
| (exp.app e1 e2) := fml2str e1 ++ " " ++ fml2str e2
| (exp.lam e) := fml2str e
| (exp.cst s) := 
  if s = prop.is_symb.true symb
  then "⊤" else
  if s = prop.is_symb.false symb
  then "⊥" else
  match s with 
  | (symb.fa) := "∀"
  | (symb.ex) := "∃"
  | (symb.not) := "¬"
  | (symb.prd str) := str 
  | (symb.fn str) := str 
  | _ := "ERROR 1"
  end
| (exp.bvr _ n) := "#" ++ to_string n
| (exp.fvr _ n) := "&" ++ to_string n

meta def showgoal : tactic unit :=
(do (Γ,Δ) ← getsqt, trace (sqt2str fml2str Γ Δ)) <|> trace "No Goals"

meta def dec_triv_tac : tactic unit :=
do t ← target, 
   to_expr ``(@of_as_true %%t) >>= apply,
   triv

example : thm [∀' (pred "P" [# 0])] [∀' (pred "P" [# 0])] :=
begin
  apply thm.far 0, dec_triv_tac, dec_triv_tac,
  apply thm.fal (& 0), 
  apply thm.prop, apply prop.thm.id,
end

example : thm [∃' (pred "P" [# 0])] [∃' (pred "P" [# 0])] :=
begin
  apply thm.exl 0, dec_triv_tac, dec_triv_tac,
  apply thm.exr (& 0),
  apply thm.prop, apply prop.thm.id,
end

example : thm [] [∀' ((pred "P" [# 0]) →' (pred "P" [# 0]))] :=
begin
  apply thm.far 0, dec_triv_tac, dec_triv_tac,
  apply thm.prop, apply prop.thm.impr, apply prop.thm.id
end

end fol


#exit 

namespace fol

notation  `⊤'` := ldex.cst fol.true
notation  `⊥'` := ldex.cst fol.false
notation  `¬'` p := ldex.app (ldex.cst fol.not) p
notation  p `∧'` q := ldex.app (ldex.app (ldex.cst fol.and) p) q
notation  p `∨'` q := ldex.app (ldex.app (ldex.cst fol.or) p) q
notation  p `→'` q := ldex.app (ldex.app (ldex.cst fol.imp) p) q
notation  t `='` s := ldex.app (ldex.app (ldex.cst fol.eq) t) s
notation  t `<'` s := ldex.app (ldex.app (ldex.cst fol.lt) t) s
notation  t `>'` s := ldex.app (ldex.app (ldex.cst fol.gt) t) s
notation  t `-'` s := ldex.app (ldex.app (ldex.cst fol.mns) t) s
notation  t `+'` s := ldex.app (ldex.app (ldex.cst fol.pls) t) s