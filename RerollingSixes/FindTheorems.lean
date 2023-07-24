import Lean

set_option autoImplicit false

open Lean

syntax (name := find_theorems) "#find_theorems" " [" name+ "]" : command

@[command_elab find_theorems]
def findTheoremsElab : Elab.Command.CommandElab := λ stx => do
  match stx with
  | `(#find_theorems [ $snames:name* ]) =>
    let needles := snames.map Lean.TSyntax.getName
    let hits := (← getEnv).constants.fold (init := []) fun es name ci =>
      let consts := Lean.Expr.getUsedConstants ci.type
      if needles.all fun needle => consts.elem needle
      then name :: es
      else es
    let hits_e <- hits.mapM mkConstWithLevelParams
    Lean.logInfo $
      m!"Found {hits.length} constants:" ++ Format.line ++
      (MessageData.joinSep (hits_e.map .ofExpr) Format.line)
  | _ =>
    Elab.throwUnsupportedSyntax

-- #find_theorems [ `find_theorems ]