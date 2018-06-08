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

inductive inf [is_symb α] : list (seq α) → seq α → Prop
| prop : ∀ S s, prop.inf S s → inf S s
| fal : ∀ t Γ Δ p, inf [(inst t p)::Γ ==> Δ] ((∀' p)::Γ ==> Δ)
| far : ∀ k Γ Δ p, k ∉ fvrs_list Γ → k ∉ fvrs_list Δ   
  → inf [Γ ==> (inst (exp.fvr α k) p)::Δ] (Γ ==> (∀' p)::Δ)
| exl : ∀ k Γ Δ p, k ∉ fvrs_list Γ → k ∉ fvrs_list Δ   
  → inf [(inst (exp.fvr α k) p)::Γ ==> Δ] ((∃' p)::Γ ==> Δ) 
| exr : ∀ t Γ Δ p, inf [Γ ==> (inst t p)::Δ] (Γ ==> (∃' p)::Δ)

inductive thm [is_symb α] : (seq α) → Prop  
| inf : ∀ {s S}, inf S s → (∀ s' ∈ S, thm s') → thm s 


/- Derived rules -/

open list

lemma thm.id [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, thm (p::Γ ==> p::Δ) :=
begin
  intros Γ Δ p, apply thm.inf, apply inf.prop,
  apply prop.inf.id, apply forall_mem_nil 
end
 
lemma thm.truer [is_symb α] : 
  ∀ (Γ Δ : list (exp α)), thm (Γ ==> ⊤'::Δ) :=
begin
  intros Γ Δ, apply thm.inf, apply inf.prop,
  apply prop.inf.truer, apply forall_mem_nil
end

lemma thm.falsel [is_symb α] : 
  ∀ (Γ Δ : list (exp α)), thm (⊥'::Γ ==> Δ) :=
begin
  intros Γ Δ, apply thm.inf, apply inf.prop,
  apply prop.inf.falsel, apply forall_mem_nil
end

lemma thm.andl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q,
  thm ((p ∧' q)::Γ ==> Δ) → thm (p::q::Γ ==> Δ) :=
begin
  intros Γ Δ p q h, apply thm.inf, apply inf.prop, apply prop.inf.andl, 
  rewrite forall_mem_singleton, apply h 
end

lemma thm.andr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q, 
  thm (Γ ==> p::Δ) → thm (Γ ==> q::Δ) 
  → thm (Γ ==> (p ∧' q)::Δ) :=
begin
  intros Γ Δ p q h1 h2, 
  apply thm.inf, apply inf.prop, apply prop.inf.andr, intros s hs,
  rewrite mem_cons_iff at hs, cases hs with hs hs,
  rewrite hs, apply h1, rewrite mem_singleton at hs,
  rewrite hs, apply h2
end

lemma thm.orl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q,
  thm (p::Γ ==> Δ) → thm (q::Γ ==> Δ)
  → thm ((p ∨' q)::Γ ==> Δ) :=
begin
  intros Γ Δ p q h1 h2, 
  apply thm.inf, apply inf.prop, apply prop.inf.orl, intros s hs,
  rewrite mem_cons_iff at hs, cases hs with hs hs,
  rewrite hs, apply h1, rewrite mem_singleton at hs,
  rewrite hs, apply h2
end

lemma thm.orr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q, 
  thm (Γ ==> p::q::Δ) → thm (Γ ==> (p ∨' q)::Δ) := 
begin
  intros Γ Δ p q h, apply thm.inf, apply inf.prop, apply prop.inf.orr, 
  rewrite forall_mem_singleton, apply h 
end

lemma thm.impl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q, 
  thm (Γ ==> p::Δ) → thm (q::Γ ==> Δ) 
  → thm ((p →' q)::Γ ==> Δ) :=
begin
  intros Γ Δ p q h1 h2, apply thm.inf, apply inf.prop, apply prop.inf.impl, 
  intros s hs, rewrite mem_cons_iff at hs, 
  cases hs with hs hs, rewrite hs, apply h1, 
  rewrite mem_singleton at hs, rewrite hs, apply h2
end

lemma thm.impr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p q, 
  thm (p::Γ ==> q::Δ) → thm (Γ ==> (p →' q)::Δ) :=
begin
  intros Γ Δ p q h, apply thm.inf, apply inf.prop, apply prop.inf.impr, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.wl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, 
  thm (Γ ==> Δ) → thm (p::Γ ==> Δ) :=  
begin
  intros Γ Δ p h, apply thm.inf, apply inf.prop, apply prop.inf.wl, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.wr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, 
  thm (Γ ==> Δ) → thm (Γ ==> p::Δ) :=
begin
  intros Γ Δ p h, apply thm.inf, apply inf.prop, apply prop.inf.wr, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.cl [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, 
  thm (p::p::Γ ==> Δ) → thm (p::Γ ==> Δ) := 
begin
  intros Γ Δ p h, apply thm.inf, apply inf.prop, apply prop.inf.cl, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.cr [is_symb α] : 
  ∀ (Γ Δ : list (exp α)) p, 
  thm (Γ ==> p::p::Δ) → thm (Γ ==> p::Δ) := 
begin
  intros Γ Δ p h, apply thm.inf, apply inf.prop, apply prop.inf.cr, 
  rewrite forall_mem_singleton, apply h
end

lemma thm.rl [is_symb α] : 
  ∀ n (Γ Δ : list (exp α)), thm (rotate n Γ ==> Δ) → thm (Γ ==> Δ) :=
begin
  intros n Γ Δ h, apply thm.inf, apply inf.prop,
  apply prop.inf.pl (rotate n Γ), 
  apply perm_rotate, intros s' hs', 
  rewrite list.mem_singleton at hs', 
  rewrite hs', apply h
end
 
lemma thm.rr [is_symb α] : 
  ∀ n (Γ Δ : list (exp α)), thm (Γ ==> rotate n Δ) → thm (Γ ==> Δ) :=
begin
  intros n Γ Δ h, apply thm.inf, apply inf.prop,
  apply prop.inf.pr _ (rotate n Δ), 
  apply perm_rotate, intros s' hs', 
  rewrite list.mem_singleton at hs', 
  rewrite hs', apply h
end

lemma thm.fal [is_symb α] : 
  ∀ t (Γ Δ : list (exp α)) p, 
  thm ((inst t p)::Γ ==> Δ) → thm ((∀' p)::Γ ==> Δ) :=
begin
  intros t Γ Δ p h, apply thm.inf, apply inf.fal t, 
  rewrite list.forall_mem_singleton, apply h
end

lemma thm.far [is_symb α] : 
  ∀ k (Γ Δ : list (exp α)) p, 
  k ∉ fvrs_list Γ → k ∉ fvrs_list Δ   
  → thm (Γ ==> (inst (exp.fvr α k) p)::Δ) → thm (Γ ==> (∀' p)::Δ) :=
begin
  intros k Γ Δ p h1 h2 h3, 
  apply thm.inf, apply inf.far k; try {assumption},
  rewrite list.forall_mem_singleton, apply h3
end

lemma thm.exl [is_symb α] : 
  ∀ k (Γ Δ : list (exp α)) p, 
  k ∉ fvrs_list Γ → k ∉ fvrs_list Δ   
  → thm ((inst (exp.fvr α k) p)::Γ ==> Δ) → thm ((∃' p)::Γ ==> Δ) :=
begin
  intros k Γ Δ p h1 h2 h3, 
  apply thm.inf, apply inf.exl k; try {assumption},
  rewrite list.forall_mem_singleton, apply h3
end

lemma thm.exr [is_symb α] : 
  ∀ t (Γ Δ : list (exp α)) p, 
  thm (Γ ==> (inst t p)::Δ) → thm (Γ ==> (∃' p)::Δ) :=
begin
  intros t Γ Δ p h, apply thm.inf, apply inf.exr t, 
  rewrite list.forall_mem_singleton, apply h
end

open tactic

meta def apply_exl (n : nat) : tactic unit := 
do to_expr ``(thm.exl %%(`(n))) >>= apply, 
   dec_triv_tac, dec_triv_tac

meta def apply_far (n : nat) : tactic unit := 
do to_expr ``(thm.far %%(`(n))) >>= apply, 
   dec_triv_tac, dec_triv_tac


/- Printing -/

open expr 

meta def getsqt : tactic (list (exp symb) × list (exp symb)) :=
do `(thm (%%Γe ==> %%Δe)) ← tactic.target,
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


/- Examples -/

example : thm ([] ==> [∀' (pred "P" [# 0]) →' ∃' (pred "P" [# 0])]) :=
begin
  showgoal,
  apply thm.impr, apply thm.fal (& 0),
  apply thm.exr (& 0), apply thm.id, 
  showgoal
end

example : thm ([∃' (pred "P" [# 0] ∨' pred "Q" [# 0])] ==> [∃' (pred "P" [# 0]) ∨' ∃' (pred "Q" [# 0])]) :=
begin
  showgoal,
  apply_exl 0, apply thm.orr, apply thm.orl, 
  apply thm.exr (& 0), apply thm.id, apply thm.rr 1,
  apply thm.exr (& 0), apply thm.id,
  showgoal
end

example : thm ([∀' (pred "P" [# 0]), ∀' ((pred "P" [# 0]) →' (pred "Q" [# 0]))] ==> [∀' (pred "Q" [# 0])]) :=
begin
  showgoal,
  apply_far 0, apply thm.fal (& 0),
  apply thm.rl 1, apply thm.fal (& 0),
  apply thm.impl, apply thm.id, apply thm.id,
  showgoal
end

example : thm ([∀' (pred "P" [# 0]), (pred "P" [& 0]) →' ((pred "P" [& 1]) →' (pred "Q" []))] ==> [pred "Q" []]) :=
begin
  showgoal,
  apply thm.rl 1, apply thm.impl, 
  apply thm.fal (& 0), apply thm.id,
  apply thm.impl, apply thm.fal (& 1), 
  apply thm.id, apply thm.id,
  showgoal
end

end fol
