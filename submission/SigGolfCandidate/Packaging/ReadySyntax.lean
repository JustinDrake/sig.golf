import Lean

/- Compact syntax for the unchanged generated list-membership proofs. -/
open Lean in
macro "wct_piece " b:num p:num i:num : tactic => do
  let digits := toString b.getNat
  let suffix := if b.getNat < 10 then "0" ++ digits else digits
  let batch := mkIdent <| Name.str `W9Machine ("chainBatch" ++ suffix)
  let evidence := mkIdent <| Name.str `W9Machine ("chainBatch" ++ suffix ++ "_evidence")
  let piece := mkIdent <| Name.str `W9Machine ("piece" ++ toString p.getNat)
  `(tactic| (apply ($evidence:ident $piece:ident)
             unfold $batch
             iterate $i apply List.mem_cons_of_mem
             exact List.mem_cons_self))
open Lean in
macro "wct_ready_start " r:num b:num i:num : tactic => do
  let digits := toString b.getNat
  let suffix := if b.getNat < 10 then "0" ++ digits else digits
  let ready := mkIdent `W9Machine.Chain.ready_of_checks
  let routine := mkIdent <| Name.str `W9Machine ("routine" ++ toString r.getNat)
  let batch := mkIdent <| Name.str `W9Machine ("routineBatch" ++ suffix)
  let checked := mkIdent <| Name.str `W9Machine ("routineBatch" ++ suffix ++ "_checked")
  let guard := mkIdent <| Name.str `W9Machine ("guardBatch" ++ suffix ++ "_checked")
  let terminal := mkIdent <| Name.str `W9Machine ("terminalBatch" ++ suffix ++ "_checked")
  `(tactic| (have hm : $routine ∈ $batch := by
               unfold $batch
               iterate $i apply List.mem_cons_of_mem
               exact List.mem_cons_self
             apply ($ready:ident _ _ rfl
               (List.all_eq_true.mp $checked _ hm)
               (List.all_eq_true.mp $guard _ hm)
               ?_ (List.all_eq_true.mp $terminal _ hm))))
open Lean in
macro "wct_cases " "[" ns:num,* "]" : tactic => do
  let pieces := ns.getElems.map fun n => mkIdent <| Name.str `W9Machine ("piece" ++ toString n.getNat)
  let pats ← ns.getElems.mapM fun _ => `(rcasesPat| rfl)
  `(tactic| (intro p hp
             change p ∈ [$[$pieces],*] at hp
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
             rcases hp with $[$pats:rcasesPat]|*
             all_goals subst_vars))
