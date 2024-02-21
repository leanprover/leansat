import LeanSAT.External.LRAT

open LRAT Lean Parser Elab Command

syntax (name := loadLRATCommand) "loadLRAT " strLit : command

@[command_elab loadLRATCommand] def elabLoadLRAT : CommandElab := fun stx => do
  match stx with
  | `(loadLRAT $file) =>
    match Syntax.isStrLit? file with
    | some file =>
        let proof ← loadLRATProof file
        IO.println s!"{proof}"
    | _ => throwError "Expected strLit: {file}"
  | _ => throwError "Failed to parse loadLRAT command"

loadLRAT "./pigeon-hole/hole6.lrat"
