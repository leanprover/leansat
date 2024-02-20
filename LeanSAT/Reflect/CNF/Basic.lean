import LeanSAT.Reflect.CNF.ForStd
import Std.Data.Bool

set_option linter.missingDocs false

abbrev CNF.Clause (α : Type) : Type := List (α × Bool)

abbrev CNF (α : Type) : Type := List (CNF.Clause α)

namespace CNF

def Clause.eval (f : α → Bool) (c : Clause α) : Bool := c.any fun (i, n) => xor n (f i)

def eval (f : α → Bool) (g : CNF α) : Bool := g.all fun c => c.eval f

@[simp] theorem eval_append (f : α → Bool) (g h : CNF α) :
    eval f (g ++ h) = (eval f g && eval f h) := List.all_append

def sat (g : CNF α) (f : α → Bool) : Prop := eval f g = true
def unsat (g : CNF α) : Prop := ∀ f, eval f g = false

end CNF
