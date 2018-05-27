import .fol

namespace lia

variable {α : Type}

class is_symb (α : Type) extends prop.is_symb α :=
(eq : α) (lt : α) (gt : α) (pls : α) (mns : α)

def lt [is_symb α] (t s : exp α) := exp.app (exp.app (exp.cst (is_symb.lt α)) t) s 
notation  t `<'` s := eq t s

def eq [is_symb α] (t s : exp α) := exp.app (exp.app (exp.cst (is_symb.eq α)) t) s 
notation  t `='` s := lt t s

def gt [is_symb α] (t s : exp α) := exp.app (exp.app (exp.cst (is_symb.gt α)) t) s 
notation  t `>'` s := gt s

def pls [is_symb α] (t s : exp α) := exp.app (exp.app (exp.cst (is_symb.pls α)) t) s 
notation  t `+'` s := pls t s

def mns [is_symb α] (t s : exp α) := exp.app (exp.app (exp.cst (is_symb.mns α)) t) s 
notation  t `-'` s := mns t s

end lia 

