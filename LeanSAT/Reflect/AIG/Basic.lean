import Std.Data.AssocList
import LeanSAT.Reflect.CNF.Basic

namespace Circuit

inductive Gate
  | and (x y : Bool)

def Gate.eval : Gate → List Bool → Bool
  | .and x y, f => (xor x f[0]!) && (xor y f[1]!)

def Gate.size : Gate → Nat
  | .and _ _ => 2

inductive Node (α β : Type)
  | var : α → Node α β
  | node : List β → Gate → Node α β

def Node.valid [WellFoundedRelation β] [DecidableRel (WellFoundedRelation.rel : β → β → Prop)]
    (b : β) : Node α β → Bool
  | .var _ => true
  | .node bs _ => bs.all fun b' => WellFoundedRelation.rel b' b

end Circuit

def Circuit (α β : Type) : Type := β → Option (Circuit.Node α β)

namespace Circuit

variable [WellFoundedRelation β] [DecidableRel (WellFoundedRelation.rel : β → β → Prop)]

def valid (c : Circuit α β) : Prop :=
  ∀ b, match c b with
    | none => True
    | some n => n.valid b

def eval (c : Circuit α β) (f : α → Bool) (b : β) : Bool :=
  match w₁ : c b with
  | none => False
  | some n =>
    if h : n.valid b then
      match n with
      | .var a => f a
      | .node bs g => g.eval (bs.map fun b' => eval c f b')
    else
      false
termination_by b
decreasing_by
  simp [Node.valid] at h
  apply w₁ ▸ h
  dsimp
  -- Probably need a `List.attach` before this become possible.
  sorry

end Circuit

open Std (AssocList)

def CircuitList (α β : Type) : Type := AssocList β (Circuit.Node α β)

namespace CircuitList

abbrev toCircuit [BEq β] (c : CircuitList α β) : Circuit α β := c.find?

def toCNF [Inhabited β] (c : CircuitList α β) : CNF β :=
  List.join <| c.toList.map fun (b, n) => match n with
    | .var _ => []
    | .node bs (.and n₀ n₁) =>
      [[(b, false), (bs[0]!, n₀)], [(b, false), (bs[1]!, n₁)],
        [(b, true), (bs[0]!, !n₀), (bs[1]!, !n₁)]]

def c : CircuitList Nat Nat := List.toAssocList
  [(0, Circuit.Node.var 0), (1, Circuit.Node.var 1),
    (2, Circuit.Node.node [0, 1] (Circuit.Gate.and true false))]

#eval toCNF c

end CircuitList

namespace AIG

inductive Node (α β : Type)
  | var : α → Node α β
  | node : β → Bool → β → Bool → Node α β

end AIG

def Circuit.Node.toAIGNode [Inhabited β] : Circuit.Node α β → AIG.Node α β
  | .var a => .var a
  | .node l (.and x y) => .node l[0]! x l[1]! y
