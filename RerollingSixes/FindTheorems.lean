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


-- This code is cargo-culted from Mathlib.Tactic.Find
namespace Mathlib.Tactic.Find

open Lean.Meta
open Lean.Elab

structure PreparedPattern extends  AbstractMVarsResult where
  headIndex : HeadIndex

def preparePat (t : Expr) : MetaM PreparedPattern := do
  let amr <- withReducible $ do abstractMVars (← instantiateMVars t)
  pure { toAbstractMVarsResult := amr, headIndex := t.toHeadIndex }

def matchPatAnywhere (pat : PreparedPattern) (c : ConstantInfo) : MetaM Bool := do
  let found  ← IO.mkRef false
  withReducible do
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    Lean.Meta.forEachExpr' cTy fun sub_e => do
      if pat.headIndex == sub_e.toHeadIndex then do
        withNewMCtxDepth $ do
          let pat := pat.expr.instantiateLevelParamsArray pat.paramNames
            (← mkFreshLevelMVars pat.numMVars).toArray
          let (_, _, pat) ← lambdaMetaTelescope pat
          -- dbg_trace (pat, sub_e)
          if ← isDefEq pat sub_e
          then found.set true
      -- keep searching if we haven't found it yet
      not <$> found.get 
  found.get


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

def matchPatConclusion (pat : PreparedPattern) (c : ConstantInfo) : MetaM Bool :=
  withReducible do
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    forallTelescopeReducing cTy fun cParams cTy' ↦ do
      if pat.headIndex == cTy'.toHeadIndex then
        let pat := pat.expr.instantiateLevelParamsArray pat.paramNames
          (← mkFreshLevelMVars pat.numMVars).toArray
        let (_, _, pat) ← lambdaMetaTelescope pat
        let (patParams, _, pat) ← forallMetaTelescopeReducing pat
        isDefEq cTy' pat <&&> matchHyps patParams.toList [] cParams.toList
      else
        pure false

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
  if ← c.name.isBlackListed then
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
  let ss := ss.qsort (·.size > ·.size)
  ss.back.fold (init := {}) fun s m =>
    if ss.pop.all (·.contains m) then s.insert m else s
  
def NameSet.union (s₁ : NameSet) (s₂ : NameSet) : NameSet :=
  s₂.fold (init := s₁) .insert


open Lean.Parser

-- def ident_or_term := leading_parser
--   ident <|> termParser
-- syntax (name := ident_or_term)
--   ident <|> termParser : ident_or_term


syntax (name := find_theorems)
  withPosition("#find_theorems" (colGt (strLit <|> ident <|> ("⊢ " term:max) <|> term:max))+) : command

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

-- until https://github.com/leanprover/std4/pull/178 lands
def String.isInfixOf (needle : String) (hey : String) := Id.run do
  let mut i := hey.mkIterator
  while not i.atEnd do
    if needle.isPrefixOf i.remainingToString
    then return true
    else i := i.next
  return false

/-- 
 Puts `MessageData` into a bulleted list
-/
def MessageData.bulletList (xs : List MessageData) : MessageData :=
  MessageData.joinSep (xs.map (m!"• " ++ ·)) Format.line 

def MessageData.andList (xs : Array MessageData) : MessageData :=
  match xs with
  | #[] => m!"– none –"
  | #[x] => x
  | _ => MessageData.joinSep xs.pop.toList m!" " ++ m!" and " ++ xs.back

/--
Formats a list of names, as you would expect from a lemma-searching command.
-/
def listOfConsts {m} [Monad m] [MonadEnv m] [MonadError m]
  (names : List Name) : m MessageData := do
    let es <- names.mapM mkConstWithLevelParams
    pure (MessageData.bulletList (es.map ppConst))


@[command_elab find_theorems]
def findTheoremsElab : CommandElab := λ stx => liftTermElabM $ do
  profileitM Exception "find_theorems" (← getOptions) do
    -- Parse the filters into the various categories
    let mut idents := #[]
    let mut name_pats := #[]
    let mut terms := #[]
    for s in stx[1].getArgs do
      match s with
      | `($ss:str) => do
        let str := Lean.TSyntax.getString ss
        name_pats := name_pats.push str
      | `($i:ident) => do
        let n := Lean.TSyntax.getId i
        unless (← getEnv).contains n do
          throwErrorAt i "Name {n} not in scope"
        idents := idents.push n
      | `(group "⊢" $st:term) => do
        let t ← Lean.Elab.Term.elabTerm st none
        terms := terms.push (true, t)
      | _ => do
        let t ← Lean.Elab.Term.elabTerm s none
        terms := terms.push (false, t)

    let pats <- liftM $ terms.mapM fun (conclusion, t) => do
      let pat ← Find.preparePat t
      if conclusion
      then pure (Mathlib.Tactic.Find.matchPatConclusion pat)
      else pure (Mathlib.Tactic.Find.matchPatAnywhere pat)

    let needles : NameSet :=
          {} |> idents.foldl NameSet.insert
             |> terms.foldl (fun s (_,t) => t.foldConsts s (flip NameSet.insert))
    if needles.isEmpty
    then do
      Lean.logWarningAt stx[1] m!"Cannot search: No constants in search pattern."
    else do
      let (m₁, m₂) <- findDeclsByConsts.get
      let hits := NameSet.intersects $ needles.toArray.map $ fun needle =>
        NameSet.union (m₁.findD needle {}) (m₂.findD needle {})

      -- Filter by name
      let hits2 := hits.toArray.filter fun n => name_pats.all fun p =>
        p.isInfixOf n.toString

      let hits3 <- hits2.filterM fun n => do
        let env <- getEnv
        if let some ci := env.find? n then do pats.allM (· ci)
        else return false

      let hits4 := hits3.qsort Name.lt
      
      let summary ← IO.mkRef MessageData.nil
      let add_line line := do summary.set $ (← summary.get) ++ line ++ Format.line


      let needles_list := MessageData.andList (needles.toArray.map .ofName)
      add_line $ m!"Found {hits.size} definitions mentioning {needles_list}."
      unless (name_pats.isEmpty) do
        let name_list := MessageData.andList <| name_pats.map fun s => m!"\"{s}\""
        add_line $ m!"Of these, {hits2.size} have a name containing {name_list}."
      unless (pats.isEmpty) do
        add_line $ m!"Of these, {hits3.size} have mention your pattern(s)."
      unless (hits4.size ≤ maxShown) do
        add_line $ m!"Of these, the first {maxShown} are shown."

      Lean.logInfo $ (← summary.get) ++ (← listOfConsts (hits4.toList.take maxShown))

-- #find_theorems "foo"
-- #find_theorems (id id) id (_ + _)