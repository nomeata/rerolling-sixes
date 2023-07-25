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
-- (someone should put it somewhere public)
private def isBlackListed (declName : Name) : MetaM Bool := do
  let env ← getEnv
  pure $ declName.isInternal
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName
  <||> Meta.isMatcher declName

private def NameRel := NameMap NameSet

-- The declaration cache keeps library declarations separate
-- from non-library declarations, cargo-culting a bit what's being done
-- in Mathlib.Tactic.Cache.DiscrTreeCache

instance : EmptyCollection NameRel :=
  inferInstanceAs $ EmptyCollection (NameMap NameSet)

instance : Nonempty NameRel :=
  inferInstanceAs $ Nonempty (NameMap NameSet)

private def NameRel.addDecl (c : ConstantInfo) (m : NameRel) := do
  if (← isBlackListed c.name) then
    return m
  let consts := c.type.foldConsts {} (flip NameSet.insert)
  return consts.fold (init := m) fun m n =>
    m.insert n (
      m.findD n {} |> flip .insert c.name
    )

initialize findDeclsByConsts : DeclCache (NameRel × NameRel) ←
  DeclCache.mk 
    (profilingName := "#find_theorems: init cache")
    (empty := ({}, {}))
    (addLibraryDecl := fun _ c (m₁, m₂) ↦ return (← NameRel.addDecl c m₁, m₂))
    (addDecl := fun _ c (m₁, m₂) ↦ return (m₁, ← NameRel.addDecl c m₂))


-- Faster implementations possible?
def NameSet.intersects (ss : Array NameSet) : NameSet :=
  ss.back.fold (init := {}) fun s m =>
    if ss.pop.all (fun s' => s'.contains m) then s.insert m else s
def NameSet.union (s₁ : NameSet) (s₂ : NameSet) : NameSet :=
  s₂.fold (init := s₁) .insert

syntax (name := find_theorems) withPosition("#find_theorems" (colGt ident)+) : command

@[command_elab find_theorems]
def findTheoremsElab : Elab.Command.CommandElab := λ stx => do
  profileitM Exception "find_theorems" (← getOptions) do
    match stx with
    | `(#find_theorems $sidents:ident*) =>
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
      let (m₁, m₂) <- Elab.Command.liftTermElabM findDeclsByConsts.get
      let hits := NameSet.intersects $ needles.map $ fun needle =>
        NameSet.union (m₁.findD needle {}) (m₂.findD needle {})
      let hits := hits.toArray.qsort Name.lt
      let hits_e <- hits.mapM mkConstWithLevelParams
      Lean.logInfo $
        m!"Found {hits_e.size} constants:" ++ Format.line ++
        (MessageData.joinSep (hits_e.toList.map ppConst) Format.line)
    | _ =>
      Elab.throwUnsupportedSyntax

-- #find_theorems [ find_theorems ]