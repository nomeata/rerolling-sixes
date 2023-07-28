import Lean
import Init.Data.Array.QSort
import Std.Lean.Delaborator
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Cache
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Find

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


-- This code is cargo-culted from Mathlib.Tactic.Find
namespace Mathlib.Tactic.Find

open Lean.Meta
open Lean.Elab

def preparePat (t : Expr) : MetaM AbstractMVarsResult :=
  withReducible $ do abstractMVars (← instantiateMVars t)

private partial def matchHyps : List Expr → List Expr → List Expr → MetaM Bool
  | p::ps, oldHyps, h::newHyps => do
    let pt ← inferType p
    let t ← inferType h
    if (← isDefEq pt t) then
      matchHyps ps [] (oldHyps ++ newHyps)
    else
      matchHyps (p::ps) (h::oldHyps) newHyps
  | [], _, _    => pure true
  | _::_, _, [] => pure false

def matchPat (pat : AbstractMVarsResult) (c : ConstantInfo) : MetaM Bool := do
  let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
  forallTelescopeReducing cTy fun cParams cTy' ↦ do
    let pat := pat.expr.instantiateLevelParamsArray pat.paramNames
      (← mkFreshLevelMVars pat.numMVars).toArray
    let (_, _, pat) ← lambdaMetaTelescope pat
    let (patParams, _, pat) ← forallMetaTelescopeReducing pat
    isDefEq cTy' pat <&&> matchHyps patParams.toList [] cParams.toList

end Mathlib.Tactic.Find


private def NameRel := NameMap NameSet

-- The declaration cache keeps library declarations separate
-- from non-library declarations, cargo-culting a bit what's being done
-- in Mathlib.Tactic.Cache.DiscrTreeCache
-- (Although I expect a linear scan through the local decls is faster than
-- building a full cache on every invocation)

instance : EmptyCollection NameRel :=
  inferInstanceAs $ EmptyCollection (NameMap NameSet)

instance : Nonempty NameRel :=
  inferInstanceAs $ Nonempty (NameMap NameSet)

private def NameRel.addDecl (c : ConstantInfo) (m : NameRel) := do
  if ← isBlackListed c.name then
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
  -- sort shortest set to the back
  let ss := ss.qsort (fun s1 s2 => s1.size > s2.size)
  ss.back.fold (init := {}) fun s m =>
    if ss.pop.all (fun s' => s'.contains m) then s.insert m else s
  
def NameSet.union (s₁ : NameSet) (s₂ : NameSet) : NameSet :=
  s₂.fold (init := s₁) .insert


open Lean.Parser

-- def ident_or_term := leading_parser
--   ident <|> termParser
-- syntax (name := ident_or_term)
--   ident <|> termParser : ident_or_term

syntax (name := find_theorems)
  withPosition("#find_theorems" (colGt (ident <|> term:max))+) : command

open Lean.Meta
open Lean.Elab
open Lean.Elab.Command

def Array.mapOrM {m α β γ} [Monad m]
  (as : Array α) (f : α -> m (β ⊕ γ)) : m (Array β × Array γ) := do
  let mut bs := #[]
  let mut cs := #[]
  for a in as do
    match ← f a with
    | .inl b => bs := bs.push b
    | .inr c => cs := cs.push c
  return (bs, cs)
  
private def maxShown := 200

@[command_elab find_theorems]
def findTheoremsElab : CommandElab := λ stx => liftTermElabM $ do
  profileitM Exception "find_theorems" (← getOptions) do
    let (idents, terms) <- stx[1].getArgs.mapOrM fun s => match s with
      | `($i:ident) => do
        let n := Lean.TSyntax.getId i
        unless (← getEnv).contains n do
          throwErrorAt i "Name {n} not in scope"
        return .inl n
      | _ => .inr <$> Lean.Elab.Term.elabTerm s none
    let pats <- liftM $ terms.mapM Find.preparePat
    let needles : NameSet :=
          {} |> idents.foldl NameSet.insert
             |> terms.foldl (fun s t => t.foldConsts s (flip NameSet.insert))

    let (m₁, m₂) <- findDeclsByConsts.get
    let hits := NameSet.intersects $ needles.toArray.map $ fun needle =>
      NameSet.union (m₁.findD needle {}) (m₂.findD needle {})
    let hits := hits.toArray.qsort Name.lt
    let hits2 <- hits.filterM fun n => do
      let env <- getEnv
      if let some ci := env.find? n then do
        pats.allM fun pat => Mathlib.Tactic.Find.matchPat pat ci
      else return false

    let hits2_e <- hits2.mapM mkConstWithLevelParams
    Lean.logInfo $
      m!"Found {hits2.size} definitions mentioning all of {needles.toArray}" ++
      (if hits2_e.size > maxShown then m!" (only {maxShown} shown)" else "") ++ ":" ++ Format.line ++
      (MessageData.joinSep ((hits2_e.toList.take maxShown).map ppConst) Format.line)

-- #find_theorems (id id) id (_ + _)