import Formalizacao.MinimaxFinal
import Lean.Util.FoldConsts

open Lean Elab Command

#print axioms FormalizacaoMinimax.minimax_nh
#print axioms FormalizacaoMinimax.lower_bound_NH
#print axioms FormalizacaoMinimax.upper_bound_NH
#print axioms FormalizacaoMinimax.upper_bound_dyadic
#print axioms FormalizacaoMinimax.critical_upper_dyadic
#print axioms FormalizacaoAltura.nodal_variable_height
#print axioms FormalizacaoAltura.l1_linear_height

private def auditedRoots : List Name :=
  [`FormalizacaoMinimax.minimax_nh, `FormalizacaoMinimax.lower_bound_NH,
   `FormalizacaoMinimax.upper_bound_NH, `FormalizacaoMinimax.upper_bound_dyadic,
   `FormalizacaoMinimax.critical_upper_dyadic, `FormalizacaoAltura.nodal_variable_height,
   `FormalizacaoAltura.l1_linear_height]

private def moduleFor (env : Environment) (decl : Name) : Name :=
  match env.getModuleIdxFor? decl with
  | some idx => env.allImportedModuleNames[idx.toNat]!
  | none => Name.anonymous

private def projectModule (mod : Name) : Bool :=
  ["Formalizacao", "Pendencias", "RequestProject"].any
    fun pfx => mod.toString.startsWith (pfx ++ ".")

private def directDependencies (env : Environment) (decl : Name) : List Name :=
  match env.checked.get.find? decl with
  | none => []
  | some ci =>
      let fromType := ci.type.getUsedConstants.toList
      let fromValue := match ci with
        | .defnInfo v => v.value.getUsedConstants.toList
        | .thmInfo v => v.value.getUsedConstants.toList
        | .opaqueInfo v => v.value.getUsedConstants.toList
        | .inductInfo v => v.ctors
        | _ => []
      (fromType ++ fromValue).eraseDups

private partial def reachableConstants (env : Environment) (queue : List Name)
    (seen : NameSet := {}) : NameSet :=
  match queue with
  | [] => seen
  | n :: rest =>
      if seen.contains n then reachableConstants env rest seen
      else reachableConstants env (directDependencies env n ++ rest) (seen.insert n)

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let all := reachableConstants env auditedRoots
  let central := reachableConstants env [`FormalizacaoMinimax.minimax_nh]
  let project := all.toList.filter (fun n => projectModule (moduleFor env n))
  let centralProject := central.toList.filter (fun n => projectModule (moduleFor env n))
  logInfo m!"F6TOTAL\t{central.toList.length}\t{centralProject.length}\t{all.toList.length}\t{project.length}"
  for n in project do
    let mod := moduleFor env n
    let inCentral := if central.contains n then "yes" else "no"
    let kind := match env.checked.get.find? n with
      | some (.axiomInfo _) => "axiom"
      | some (.opaqueInfo _) => "opaque"
      | some (.thmInfo _) => "theorem"
      | some (.defnInfo _) => "def"
      | _ => "other"
    logInfo m!"F6NODE\t{n}\t{mod}\t{inCentral}\t{kind}"
    for dep in directDependencies env n do
      let depMod := moduleFor env dep
      if projectModule depMod then
        logInfo m!"F6EDGE\t{n}\t{dep}\t{mod}\t{depMod}"
