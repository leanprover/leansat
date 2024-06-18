import LeanSAT.External.LRAT
import Lean.Data.RBMap

open Lean

namespace LRAT

namespace trim

/--
The context used for trimming LRAT proofs.
-/
structure Context where
  /--
  The proof as a map from proof step ids to their actions.
  -/
  proof : HashMap Nat IntAction
  /--
  The id of the empty proof step.
  -/
  addEmptyId : Nat

structure State where
  /--
  The set of used proof step ids.
  -/
  used : RBMap Nat Unit compare := {}
  /--
  A mapping from old proof step ids to new ones. Used such that the proof remains a sequence without
  gaps.
  -/
  mapped : HashMap Nat Nat := {}

abbrev M : Type → Type := ReaderT Context <| StateRefT State IO

namespace M

def run (proof : Array IntAction) (x : M α) : IO α := do
  let addEmptyId ←
    match proof[proof.size - 1]! with
    | .addEmpty id .. => pure id
    | _ => throw <| .userError "Last proof step is not the empty clause"

  let folder acc a :=
    match a with
    | .addEmpty id .. | .addRup id .. | .addRat id .. => acc.insert id a
    | .del .. => acc
  let proof := proof.foldl (init := mkHashMap proof.size) folder

  ReaderT.run x { proof, addEmptyId } |>.run' {}

@[inline]
def getEmptyId : M Nat := do
  let ctx ← read
  return ctx.addEmptyId

@[inline]
def getProofStep (id : Nat) : M (Option IntAction) := do
  let ctx ← read
  return ctx.proof.find? id

@[inline]
def isUsed (id : Nat) : M Bool := do
  let s ← get
  return s.used.contains id

@[inline]
def markUsed (id : Nat) : M Unit := do
  -- If we are referring to a proof step that is not part of the proof, it is part of the CNF.
  -- We do not trim the CNF so just forget about the fact that this step was used.
  if (← getProofStep id).isSome then
    modify (fun s => { s with used := s.used.insert id () })

@[inline]
def getUsedSet : M (RBMap Nat Unit Ord.compare) := do
  let s ← get
  return s.used

def registerIdMap (oldId : Nat) (newId : Nat) : M Unit := do
  modify (fun s => { s with mapped := s.mapped.insert oldId newId })

def mapStep (step : IntAction) : M IntAction := do
  match step with
  | .addEmpty id hints =>
    let newId ← mapIdent id
    let newHints ← hints.mapM mapIdent
    return .addEmpty newId newHints
  | .addRup id c hints =>
    let newId ← mapIdent id
    let newHints ← hints.mapM mapIdent
    return .addRup newId c newHints
  | .addRat id c pivot rupHints ratHints =>
    let newId ← mapIdent id
    let newRupHints ← rupHints.mapM mapIdent
    let mapper hint := do
      let newHint ← mapIdent hint.fst
      let newHints ← hint.snd.mapM mapIdent
      return (newHint, newHints)
    let newRatHints ← ratHints.mapM mapper
    return .addRat newId c pivot newRupHints newRatHints
  | .del ids =>
    return .del (← ids.mapM mapIdent)
where
  @[inline]
  mapIdent (ident : Nat) : M Nat := do
    let s ← get
    return s.mapped.find? ident |>.getD ident

end M

/--
Perform a use-def analysis of LRAT proof steps, starting at the empty clause and working its way
up with DFS.
-/
partial def useAnalysis : M Unit := do
  let emptyId ← M.getEmptyId
  go [emptyId]
where
  go (workList : List Nat) : M Unit := do
    match workList with
    | [] => return ()
    | id :: workList =>
      if ← M.isUsed id then
        go workList
      else
        M.markUsed id
        let step? ← M.getProofStep id
        match step? with
        | some step =>
          match step with
          | .addEmpty _ hints =>
            let workList := hints.toList ++ workList
            go workList
          | .addRup _ _ hints =>
            let workList := hints.toList ++ workList
            go workList
          | .addRat _ _ _ rupHints ratHints =>
            let folder acc a :=
              a.fst :: a.snd.toList ++ acc
            let ratHints := ratHints.foldl (init := []) folder
            let workList := rupHints.toList ++ ratHints ++ workList
            go workList
          | .del .. => go workList
        | none => go workList

/--
Map the set of used proof steps to a new LRAT proof that has no holes in the sequence of proof
identifiers.
-/
def mapping : M (Array IntAction) := do
  let used ← M.getUsedSet
  let (min, _) := used.min!
  let mut nextMapped := min
  let mut newProof := Array.mkEmpty used.size
  for (id, _) in used do
    M.registerIdMap id nextMapped
    let step := (← M.getProofStep id).get!
    let newStep ← M.mapStep step
    newProof := newProof.push newStep
    nextMapped := nextMapped + 1
  return newProof

def go : M (Array IntAction) := do
  useAnalysis
  mapping

end trim

/--
Trim an LRAT proof stored in one file and output it to the other.
-/
def trim (input : System.FilePath) (output : System.FilePath) : IO Unit := do
  let proof ← loadLRATProof input
  let trimmed ← trim.go.run proof
  dumpLRATProof output trimmed

end LRAT
