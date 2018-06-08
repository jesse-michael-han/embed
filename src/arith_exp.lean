inductive exp
| var      {} : nat → exp
-- | mvar        : name → exp
| const    {} : string → exp
| local_const : string → exp → exp
| app         : exp → exp → exp
| lam         : string → exp → exp → exp

instance : inhabited exp :=
⟨exp.const "foo"⟩

namespace exp

def mk_var (n : nat) : exp := var n

instance : decidable_eq exp := by tactic.mk_dec_eq_instance

-- TODO: alpha equiv: ignore binder names
-- TODO: has_to_string, has_to_format, has_coe_to_fun

/- Coercion for letting users write (f a) instead of (expr.app f a) -/
instance : has_coe_to_fun exp :=
{ F := λ e, exp → exp, coe := λ e, exp.app e }

-- hashing?

def is_var : exp → bool
| (var _) := tt
| _       := ff

def is_const : exp → bool
| (const _) := tt
| _       := ff

def const_str : exp → string
| (const s) := s
| _         := ""

def app_of_list : exp → list exp → exp
| f []      := f
| f (p::ps) := app_of_list (f p) ps

def is_app : exp → bool
| (app f a) := tt
| e         := ff

def app_fn : exp → exp
| (app f a) := f
| a         := a

def app_arg : exp → exp
| (app f a) := a
| a         := a

def get_app_fn : exp → exp
| (app f a) := get_app_fn f
| a         := a

def get_app_num_args : exp → nat
| (app f a) := get_app_num_args f + 1
| e         := 0

def get_app_args_aux : list exp → exp → list exp
| r (app f a) := get_app_args_aux (a::r) f
| r e         := r

def get_app_args : exp → list exp :=
get_app_args_aux []

def mk_app : exp → list exp → exp
| e []      := e
| e (x::xs) := mk_app (e x) xs
end exp

open exp

inductive is_arith_exp : exp → Prop
-- | is_var (n : nat) : is_arith_exp (var n) 
| is_zero          : is_arith_exp (const "zero")
| is_one           : is_arith_exp (const "one")
| is_plus {e₁ e₂ : exp} (h₁ : is_arith_exp e₁) (h₂ : is_arith_exp e₂) : 
                     is_arith_exp (app (app (const "plus") e₁) e₂)
| is_times {e₁ e₂ : exp} (h₁ : is_arith_exp e₁) (h₂ : is_arith_exp e₂) : 
                     is_arith_exp (app (app (const "times") e₁) e₂)

def eval_exp_of_is_arith_exp : Π e, is_arith_exp e → nat 
| (var n) h := by {exfalso, cases h} 
| (const s) h :=  
  if h0 : s = "zero" then 0
  else if h1 : s = "one" then 1
  else by {exfalso, cases h; contradiction}
| (local_const s e) h := by {exfalso, cases h}
| (lam s e1 e2) h := by {exfalso, cases h}
| (app (var n) e₂) h := by {exfalso, cases h}
| (app (const s) e₂) h := by {exfalso, cases h}
| (app (local_const s e) e₂) h := by {exfalso, cases h}
| (app (lam s e1' e2') e2) h := by {exfalso, cases h}
| (app (app (var n) e1) e2) h := by {exfalso, cases h}
| (app (app (local_const s e) e1) e2) h := by {exfalso, cases h}
| (app (app (lam s e1' e2') e1) e2) h := by {exfalso, cases h}
| (app (app (app e1' e2') e1) e2) h := by {exfalso, cases h}
| (app (app (const s) e1) e2) h := 
  if h0 : s = "plus" then 
    (have he1 : is_arith_exp e1, {cases h; assumption}, 
     have he2 : is_arith_exp e2, {cases h; assumption}, 
     (eval_exp_of_is_arith_exp e1 he1) + (eval_exp_of_is_arith_exp e2 he2))
  else if h1 : s = "times" then 
    (have he1 : is_arith_exp e1, {cases h; assumption}, 
     have he2 : is_arith_exp e2, {cases h; assumption}, 
     (eval_exp_of_is_arith_exp e1 he1) * (eval_exp_of_is_arith_exp e2 he2))
  else by {exfalso, cases h; contradiction}

  def arith_exp : Type := {e : exp // is_arith_exp e}

  def eval_arith_exp : arith_exp → nat 
  | ⟨e,h⟩ := eval_exp_of_is_arith_exp e h

  def dec_is_arith_exp : 
    ∀ e, decidable (is_arith_exp e)
  | (var n) := decidable.is_false (λ h, by cases h)
  | (const s) :=  
    if h0 : "zero" = s then 
      decidable.is_true (h0 ▸ is_arith_exp.is_zero)
    else if h1 : "one" = s then 
      decidable.is_true (h1 ▸ is_arith_exp.is_one)
    else decidable.is_false (λ h, by {cases h; contradiction})
  | (local_const s e) := decidable.is_false (λ h, by cases h)
  | (lam s e1 e2) := decidable.is_false (λ h, by cases h)
  | (app (var n) e₂) := decidable.is_false (λ h, by cases h)
  | (app (const s) e₂) := decidable.is_false (λ h, by cases h)
  | (app (local_const s e) e₂) := decidable.is_false (λ h, by cases h)
  | (app (lam s e1' e2') e2) := decidable.is_false (λ h, by cases h)
  | (app (app (var n) e1) e2) := decidable.is_false (λ h, by cases h)
  | (app (app (local_const s e) e1) e2) := decidable.is_false (λ h, by cases h)
  | (app (app (lam s e1' e2') e1) e2) := decidable.is_false (λ h, by cases h)
  | (app (app (app e1' e2') e1) e2) := decidable.is_false (λ h, by cases h)
  | (app (app (const s) e1) e2) := 
    begin
      cases (dec_is_arith_exp e1) with _ he1, 
      apply decidable.is_false, 
      intro hc, cases hc; contradiction,
      cases (dec_is_arith_exp e2) with _ he2, 
      apply decidable.is_false, 
      intro hc, cases hc; contradiction,
      exact 
        (if h0 : "plus" = s then 
          decidable.is_true (h0 ▸ is_arith_exp.is_plus he1 he2)
         else if h1 : "times" = s then 
          decidable.is_true (h1 ▸ is_arith_exp.is_times he1 he2)
         else 
          decidable.is_false (λ h, by {cases h; contradiction}) )
    end

  instance : decidable_pred is_arith_exp := 
  dec_is_arith_exp
  
  meta def dec_triv_tac : tactic unit :=
  do t ← tactic.target, 
     tactic.to_expr ``(@of_as_true %%t) >>= tactic.apply,
     tactic.triv
  
  def Zero := exp.const "zero"
  def One := exp.const "one"
    
  notation a `+'` b := exp.app (exp.app (exp.const "plus") a) b
  notation a `*'` b := exp.app (exp.app (exp.const "times") a) b
  
  #eval eval_arith_exp ⟨Zero, by dec_triv_tac⟩ 
  #eval eval_arith_exp ⟨Zero +' One, by dec_triv_tac⟩ 
  #eval eval_arith_exp ⟨Zero *' One, by dec_triv_tac⟩ 
  #eval eval_arith_exp ⟨(Zero +' One +' One) *' (One +' Zero +' One), by dec_triv_tac⟩ 