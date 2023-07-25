import Lean
import Std.Lean.Delaborator
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Cache
import Mathlib.Lean.Expr.Basic

set_option autoImplicit false

open Lean

open Mathlib.Tactic

-- from Lean.Server.Completion
-- from Mathlib.Tactic.Find
private def isBlackListed (declName : Name) : MetaM Bool := do
  let env ← getEnv
  pure $ declName.isInternal
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName
  <||> Meta.isMatcher declName



initialize findDeclsByConsts : DeclCache (NameMap NameSet) ←
  DeclCache.mk "#find_theorems: init cache" {} fun _ c m ↦ do
    if (← isBlackListed c.name) then
      return m
    let consts := c.type.foldConsts {} (flip NameSet.insert)
    return consts.fold (init := m) (fun m n =>
      m.insert n (
        m.findD n {} |> flip .insert c.name
      )
    )

syntax (name := find_theorems) "#find_theorems" "[" ident+ "]" : command


-- Faster implementation possible?
def NameSet.intersects (ss : Array NameSet) : NameSet :=
  ss.back.fold (init := {}) fun s m =>
    if ss.pop.all (fun s' => s'.contains m) then s.insert m else s

@[command_elab find_theorems]
def findTheoremsElab : Elab.Command.CommandElab := λ stx => do
  profileitM Exception "find_theorems" (← getOptions) do
    match stx with
    | `(#find_theorems [ $sidents:ident* ]) =>
      let needles <- sidents.mapM fun sident => do
        let n := Lean.TSyntax.getId sident
        unless ((← getEnv).contains n) do
          throwErrorAt sident "Name {n} not in scope"
        return n
      -- let hits := (← getEnv).constants.fold (init := []) fun es name ci =>
      --   if name.isInternal' then es
      --   else
      --   let consts := Lean.Expr.getUsedConstants ci.type
      --   if needles.all consts.elem
      --   then name :: es
      --   else es
      let c <- Elab.Command.liftTermElabM findDeclsByConsts.get
      let hits := NameSet.intersects (needles.map (fun needle => c.findD needle {}))
      let hits_e <- hits.toList.mapM mkConstWithLevelParams
      Lean.logInfo $
        m!"Found {hits_e.length} constants:" ++ Format.line ++
        (MessageData.joinSep (hits_e.map ppConst) Format.line)
    | _ =>
      Elab.throwUnsupportedSyntax

-- #find_theorems [ find_theorems ]