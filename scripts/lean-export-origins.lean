import Lean

open Lean

def main (arguments : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let environment ← importModules #[{ module := `Source }] {}
  for argument in arguments do
    let some declaration := Syntax.decodeNameLit ("`" ++ argument)
      | throw <| IO.userError s!"invalid declaration name: {argument}"
    let some index := environment.getModuleIdxFor? declaration
      | throw <| IO.userError s!"missing source module: {argument}"
    let some sourceModule := environment.header.moduleNames[index.toNat]?
      | throw <| IO.userError s!"invalid module index: {argument}"
    IO.println <| Json.compress <| Json.mkObj [
      ("declaration", toJson argument),
      ("module", toJson sourceModule.toString)
    ]
