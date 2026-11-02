import Lean

open Lean

-- Use Lim's segment-preserving identities, never reparsed display names.
-- Numeric components and strings containing dots must stay distinguishable.
def declarationIdentity : Name → String
  | .anonymous => "$lean:"
  | .str pre part => declarationIdentity pre ++ s!"s{part.utf8ByteSize}:{part}"
  | .num pre part => declarationIdentity pre ++ s!"n{part};"

def main (arguments : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let environment ← importModules #[{ module := `Source }] {}
  let declarations := environment.constants.fold (init := #[]) fun names name _ =>
    if arguments.contains (declarationIdentity name) then names.push name else names
  for argument in arguments do
    let candidates := declarations.filter fun name => declarationIdentity name == argument
    unless candidates.size == 1 do
      throw <| IO.userError s!"missing or ambiguous declaration name: {argument}"
    let declaration := candidates[0]!
    let some index := environment.getModuleIdxFor? declaration
      | throw <| IO.userError s!"missing source module: {argument}"
    let some sourceModule := environment.header.moduleNames[index.toNat]?
      | throw <| IO.userError s!"invalid module index: {argument}"
    IO.println <| Json.compress <| Json.mkObj [
      ("identity", toJson argument),
      ("module", toJson sourceModule.toString)
    ]
