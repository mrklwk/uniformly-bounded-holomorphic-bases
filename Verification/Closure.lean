module
public import Solution
public meta import Lean
public meta import Lean.Replay

/- Reproducible logical-closure traversal and replay. Not a production dependency. -/
set_option maxHeartbeats 0
open Lean Elab Command
namespace FinalScopeAudit
structure Closure where
  seen : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}
  deriving Inhabited
partial def visit (env : Environment) (n : Name) : StateM Closure Unit := do
  if (← get).seen.contains n then return
  modify fun s => { s with seen := s.seen.insert n }
  let some ci := env.find? n | do
    modify fun s => { s with missing := s.missing.insert n }
    return
  if ci.isAxiom then modify fun s => { s with axioms := s.axioms.insert n }
  if let .quotInfo _ := ci then visit env ``Eq
  ci.type.getUsedConstants.forM (visit env)
  if let some value := ci.value? true then value.getUsedConstants.forM (visit env)
  if let .inductInfo i := ci then
    i.all.forM (visit env)
    i.ctors.forM (visit env)
run_cmd do
  -- Explicitly load transitive private proof bodies, not just module interfaces.
  let env ← importModules #[{ module := `Solution }] {} (level := .private)
  let root := ``BourgainBasis.uniformly_bounded_homogeneous_basis
  let (_, mainClosure) := (visit env root).run {}
  let (_, s) := (visit env ``BourgainStatement.manuscript_main).run mainClosure
  logInfo m!"MAIN THEOREM CLOSURE: {mainClosure.seen.size} declarations"
  unless s.missing.isEmpty do throwError "Missing declarations: {s.missing.toArray}"
  unless s.seen.contains ``BourgainBasis.coupled_quadratic_cancellation do
    throwError "Expected actual coupled cancellation dependency was not found"
  if s.seen.contains ``BourgainBasis.QuadraticCancellation then
    throwError "General SPD proposition unexpectedly occurs in final theorem closure"
  for ax in s.axioms.toArray do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Disallowed axiom: {ax}"
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for name in s.seen.toArray do
    let some ci := env.find? name | throwError "Missing declaration: {name}"
    if ci.isUnsafe || ci.isPartial then
      throwError "Unsafe or partial declaration in logical closure: {name}"
    constants := constants.insert name ci
  if let some output ← IO.getEnv "BOURGAIN_AUDIT_OUTPUT" then
    IO.FS.writeFile output
      (String.intercalate "\n" ((s.seen.toArray.qsort Name.lt).toList.map Name.toString) ++ "\n")
  logInfo m!"SCOPE: coupled_quadratic_cancellation present; general QuadraticCancellation absent"
  logInfo m!"AXIOMS {s.axioms.toArray.qsort Name.lt}; unsafe/partial/missing: none"
  let empty ← mkEmptyEnvironment
  let replayed ← empty.toKernelEnv.replay constants
  unless (replayed.find? root).isSome do throwError "Missing final theorem after replay"
  unless (replayed.find? ``BourgainStatement.manuscript_main).isSome do
    throwError "Missing manuscript statement after replay"
  logInfo m!"FRESH FINAL THEOREM CLOSURE PASS: {constants.size} declarations, 2 roots"
end FinalScopeAudit
