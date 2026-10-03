import SigGolfCandidate.Rv.Exec

namespace SigGolfCandidate.Rv
open Lean Meta Elab Tactic Command
unsafe def evalOptResultUnsafe (e : Expr) : MetaM (Option Result) :=
  evalExpr (Option Result) (mkApp (mkConst ``Option [0]) (mkConst ``Result)) e
@[implemented_by evalOptResultUnsafe]
opaque evalOptResult (e : Expr) : MetaM (Option Result)
unsafe def evalExprExprUnsafe (e : Expr) : MetaM Expr := evalExpr Expr (mkConst ``Expr) e
@[implemented_by evalExprExprUnsafe]
opaque evalExprExpr (e : Expr) : MetaM Expr
def evalToLiteral (lhs : Expr) : MetaM Expr := do
  let lhs ← instantiateMVars lhs
  if lhs.hasFVar || lhs.hasMVar then
    throwError "sym_eval: the left-hand side must be a closed term, got{indentExpr lhs}"
  let α ← inferType lhs
  let u ← getLevel α
  let some u' := u.dec | throwError "sym_eval: type must live in `Type u`"
  let inst ← synthInstance (mkApp (mkConst ``Lean.ToExpr [u']) α)
  evalExprExpr (mkApp3 (mkConst ``Lean.toExpr [u']) α inst lhs)
def kernelEq (lhs lit : Expr) : MetaM Expr := do
  let ty ← mkEq lhs lit
  let pf ← mkEqRefl lit
  let name ← mkAuxLemma [] ty pf
  return mkConst name
elab "sym_eval" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "sym_eval: goal is not an equation"
  let lit ← evalToLiteral lhs
  unless ← isDefEq rhs lit do
    throwError "sym_eval: result mismatch; the computation returned{indentExpr lit}"
  goal.assign (← kernelEq lhs lit)
  replaceMainGoal []
section Shared
open Std
abbrev ShareM := StateM (HashMap USize Expr)
unsafe def eToExprShared (e : E) : ShareM Expr := do
  let key := ptrAddrUnsafe e
  if let some x := (← get).get? key then return x
  let x ← match e with
    | .c _ | .reg _ => pure (toExpr e)
    | .ld a => do pure (mkApp (mkConst ``E.ld) (← eToExprShared a))
    | .un op a => do pure (mkApp2 (mkConst ``E.un) (toExpr op) (← eToExprShared a))
    | .bin op a b => do
      pure (mkApp3 (mkConst ``E.bin) (toExpr op) (← eToExprShared a) (← eToExprShared b))
    | .ite op x y a b => do
      pure (mkApp5 (mkConst ``E.ite) (toExpr op) (← eToExprShared x) (← eToExprShared y)
        (← eToExprShared a) (← eToExprShared b))
  modify (·.insert key x)
  return x
unsafe def addrToExprShared (a : Addr) : ShareM Expr := do
  let b ← match a.base with
    | none => pure (mkApp (mkConst ``Option.none [0]) (mkConst ``E))
    | some b => do
      let x ← eToExprShared b
      pure (mkApp2 (mkConst ``Option.some [0]) (mkConst ``E) x)
  return mkApp2 (mkConst ``Addr.mk) b (toExpr a.off)
unsafe def obligToExprShared : Oblig → ShareM Expr
  | .valid a w => return mkApp2 (mkConst ``Oblig.valid) (← addrToExprShared a) (toExpr w)
  | .align8 b => return mkApp (mkConst ``Oblig.align8) (← eToExprShared b)
  | .ne a b => return mkApp2 (mkConst ``Oblig.ne) (← addrToExprShared a) (← addrToExprShared b)
def listLit (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
    (mkApp (mkConst ``List.nil [0]) ty)
unsafe def resultToExprSharedM (r : Result) : ShareM Expr := do
  let regs ← r.st.regs.fields.mapM eToExprShared
  let regsE := mkAppN (mkConst ``RegFile.mk) regs.toArray
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Addr) (mkConst ``E)
  let mem ← r.st.mem.mapM fun (k, v) => do
    return mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Addr) (mkConst ``E)
      (← addrToExprShared k) (← eToExprShared v)
  let obl ← r.st.obl.mapM obligToExprShared
  let st := mkApp3 (mkConst ``SymState.mk) regsE (listLit pairTy mem)
    (listLit (mkConst ``Oblig) obl)
  return mkApp5 (mkConst ``Result.mk) st (← eToExprShared r.pc) (toExpr r.stop)
    (toExpr r.steps) (toExpr r.cycles)
unsafe def resultToExprSharedUnsafe (r : Result) : Expr :=
  (resultToExprSharedM r).run' {}
@[implemented_by resultToExprSharedUnsafe]
opaque resultToExprShared (r : Result) : Expr
end Shared
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "kernel_rfl: goal is not an equation"
  if t.hasFVar || t.hasMVar then throwError "kernel_rfl: goal must be closed"
  let pf ← mkEqRefl lhs
  let name ← mkAuxLemma [] t (← mkExpectedTypeHint pf t)
  let _ := rhs
  goal.assign (mkConst name)
  replaceMainGoal []
elab "sym_block " id:ident " := " t:term : command => do
  liftTermElabM do
    let e ← Term.elabTermEnsuringType t (mkApp (mkConst ``Option [0]) (mkConst ``Result))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasFVar || e.hasMVar then
      throwError "sym_block: the executor call must be a closed term"
    let v ← evalOptResult e
    let some r := v | throwError "sym_block: symbolic execution returned `none`{indentExpr e}"
    let base := (← getCurrNamespace) ++ id.getId
    let resName := base ++ `res
    addDecl <| Declaration.defnDecl {
      name := resName, levelParams := [], type := mkConst ``Result, value := resultToExprShared r,
      hints := .abbrev, safety := .safe }
    enableRealizationsForConst resName
    compileDecls #[resName]
    let lit := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Result) (mkConst resName)
    let ty ← mkEq e lit
    let pf ← mkEqRefl lit
    addDecl <| Declaration.thmDecl { name := base, levelParams := [], type := ty, value := pf }
    enableRealizationsForConst base
end SigGolfCandidate.Rv
