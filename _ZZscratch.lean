import PdtNorm
import PdtLinks
import PdtTraceLink
import PdtTraceSignature
import PdtTraceCompositum
import PdtTraceTensor
open Polynomial PDT

example : @PDT.factIrreducible_fQ = (inferInstance : Fact (Irreducible PDT.fQ)) := rfl
example : @PDT.factIrreducible_fρ = (inferInstance : Fact (Irreducible PDT.fρ)) := rfl
noncomputable example : Field (AdjoinRoot PDT.fQ) := inferInstance
noncomputable example : Field (AdjoinRoot PDT.fρ) := inferInstance
example : @AdjoinRoot.instField ℚ _ PDT.fQ PDT.factIrreducible_fQ =
          (inferInstance : Field (AdjoinRoot PDT.fQ)) := rfl
-- how many Fact instances now sit on the same proposition:
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut hits := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.startsWith "PDT." && (s.splitOn "Fact").length > 1 then hits := hits.push n
  logInfo m!"{hits}"
