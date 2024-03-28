import LeanSAT.AIG.Relabel

open Std

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α]

namespace AIG

structure State (α : Type) [BEq α] [Hashable α] [DecidableEq α] where
  max : Nat
  map : HashMap α Nat
  -- TODO: some invariant

def State.empty : State α :=
  { max := 0, map := {} }

def State.addVar (state : State α) (x : α) : State α :=
  match state.map.find? x with
  | some _ => state
  | none => { max := state.max + 1, map := state.map.insert x state.max }

def State.addDecl (state : State α) (decl : Decl α) : State α :=
  match decl with
  | .atom x => state.addVar x
  | _ => state

def State.ofAIG (aig : AIG α) : State α :=
  aig.decls.foldl (init := State.empty) State.addDecl

def relabelNat (aig : AIG α) : AIG Nat :=
  let state := State.ofAIG aig
  -- The getD branch never gets hit.
  aig.relabel fun x => state.map.find? x |>.getD 0

/-
Idea: meta theorem: relabel (fun x => if x ∈ aig then foo x else idk) = relabel foo.
That way I can smuggle my assumption in here
-/

theorem relabelNat_unsat_iff {aig : AIG α} {hidx1} {hidx2}
    : (aig.relabelNat).unsatAt idx hidx1 ↔ aig.unsatAt idx hidx2 := sorry

namespace Entrypoint

def relabelNat (entry : Entrypoint α) : Entrypoint Nat :=
  { entry with
      aig := entry.aig.relabelNat
      inv := by sorry
  }

theorem relabelNat_unsat_iff {entry : Entrypoint α}
    : (entry.relabelNat).unsat ↔ entry.unsat:= sorry

end Entrypoint
end AIG

