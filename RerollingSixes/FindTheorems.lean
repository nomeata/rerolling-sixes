import Lean
import Std.Lean.Delaborator
import Mathlib.Lean.Expr.Basic

set_option autoImplicit false

open Lean

syntax (name := find_theorems) "#find_theorems" "[" ident+ "]" : command

@[command_elab find_theorems]
def findTheoremsElab : Elab.Command.CommandElab := λ stx => do
  match stx with
  | `(#find_theorems [ $sidents:ident* ]) =>
    let needles <- sidents.mapM fun sident => do
      let n := Lean.TSyntax.getId sident
      unless ((← getEnv).contains n) do
        throwErrorAt sident "Name {n} not in scope"
      return n
    let hits := (← getEnv).constants.fold (init := []) fun es name ci =>
      if name.isInternal' then es
      else
      let consts := Lean.Expr.getUsedConstants ci.type
      if needles.all consts.elem
      then name :: es
      else es
    let hits_e <- hits.mapM mkConstWithLevelParams
    Lean.logInfo $
      m!"Found {hits.length} constants:" ++ Format.line ++
      (MessageData.joinSep (hits_e.map ppConst) Format.line)
  | _ =>
    Elab.throwUnsupportedSyntax

-- #find_theorems [ find_theorems ]