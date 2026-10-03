import Lean
import Comparator
import Export.Parse

/-!
Standalone declarative certificate checker. Compile in the installed comparator
package with `lake env lean --root=/path/to/verifier -o ... -c ... CertificateCheck.lean`,
Then link the C file with the pinned Comparator and Export.Parse native objects
using `lake env leanc`; their paths are in .lake/build/bin/comparator.rsp.
`lake env lean --run` also works without linking.
Usage: certificate-check config.json trusted-challenge.export candidate.export [report.json]
   or: certificate-check --serve organizer-owned-base.export

The caller owns the config and trusted export and enforces input/resource limits.
No candidate modules, oleans, plugins, or native code are loaded. Default mode
always replays into an empty environment. Serve mode replays its immutable base
once from empty; requests cannot select or update that base. Every actual base
constant must match the full candidate ConstantInfo, including theorem proofs,
before reuse. Missing/conflicting base entries fall back to fresh replay. Used
dependencies must exist in the full candidate map, not merely in the base.
Image binding is an ordinary selected theorem: its trusted literal dependency must
not be a definition hole, so compareAt checks that dependency including its value.
-/

namespace CertificateCheck

structure Config where
  theorem_names : Array String
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  enable_nanoda : Bool
  deriving Lean.FromJson

-- Keep this list identical to Comparator/Main.lean for the pinned Lean kernel.
def primitiveTargets : Array Lean.Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div,
  ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor,
  ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,
  ``List, ``eagerReduce
]

structure Phases where
  parse : Float := 0
  compare : Float := 0
  axioms : Float := 0
  kernel : Float := 0
  deriving Lean.ToJson

structure Counts where
  trusted : Nat := 0
  candidate : Nat := 0
  deriving Lean.ToJson

structure Report where
  status : String := "rejected"
  phase : String := "config"
  phases_seconds : Phases := {}
  declaration_counts : Counts := {}
  error : Option String := none
  deriving Lean.ToJson

-- A thunk keeps pure comparison work inside the measured interval.
def timed (report : IO.Ref Report) (phase : String) (action : Unit -> IO a) : IO a := do
  report.modify fun r => { r with phase }
  let start <- IO.monoNanosNow
  try
    action ()
  finally
    let seconds := (Float.ofNat ((<- IO.monoNanosNow) - start)) / 1000000000
    report.modify fun r => { r with phases_seconds := match phase with
      | "parse" => { r.phases_seconds with parse := seconds }
      | "compare" => { r.phases_seconds with compare := seconds }
      | "axioms" => { r.phases_seconds with axioms := seconds }
      | "kernel" => { r.phases_seconds with kernel := seconds }
      | _ => r.phases_seconds }

def parseExport (path : System.FilePath) : IO Export.ExportedEnv :=
  IO.FS.withFile path .read fun handle =>
    Export.parseStream (IO.FS.Stream.ofHandle handle)

def runKernel (candidate : Export.ExportedEnv) : IO Unit := do
  let env <- Lean.mkEmptyEnvironment
  -- Adding Quot installs these three kernel declarations automatically.
  let constants := candidate.constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.replay constants

structure VerifiedBase where
  env : Lean.Environment
  constants : Std.HashMap Lean.Name Lean.ConstantInfo

def loadBase (path : String) : IO VerifiedBase := do
  let parsed <- parseExport path
  let empty <- Lean.mkEmptyEnvironment
  let constants := parsed.constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  let env <- empty.replay constants
  -- Use actual kernel-generated declarations, not unchecked export metadata.
  return { env, constants := Std.HashMap.ofList env.constants.toList }

def runKernelWithBase (candidate : Export.ExportedEnv) (base : VerifiedBase)
    (reused : Option (IO.Ref Nat)) : IO Unit := do
  for (name, info) in base.constants do
    if candidate.constMap[name]? != some info then
      return <- runKernel candidate
  -- Reuse cannot supply declarations omitted from the submitted certificate.
  for (_, info) in candidate.constMap do
    for dependency in info.getUsedConstantsAsSet do
      unless candidate.constMap.contains dependency do
        throw <| IO.userError s!"Constant not found in candidate: '{dependency}'"
    if let .inductInfo info := info then
      for dependency in info.all ++ info.ctors do
        unless candidate.constMap.contains dependency do
          throw <| IO.userError s!"Inductive group member not found in candidate: '{dependency}'"
  let mut delta := candidate.constMap
  for (name, _) in base.constants do
    delta := delta.erase name
  delta := delta.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  if let some reused := reused then reused.set base.constants.size
  -- Environment updates are persistent; never promote the request-local result.
  discard <| base.env.replay delta

def verify (report : IO.Ref Report) (configPath trustedPath candidatePath : String)
    (base : Option VerifiedBase := none) (reused : Option (IO.Ref Nat) := none) : IO Unit := do
  let config : Config <- IO.ofExcept <| Lean.fromJson? <|
    <- IO.ofExcept <| Lean.Json.parse (<- IO.FS.readFile configPath)
  if config.enable_nanoda then
    throw <| IO.userError "enable_nanoda=true is unsupported by the standalone certificate checker"
  let theoremNames := config.theorem_names.map String.toName
  let definitionNames := config.definition_names.getD #[] |>.map String.toName
  let legalAxioms := config.permitted_axioms.map String.toName
  let (trusted, candidate) <- timed report "parse" fun _ => do
    let trusted <- parseExport trustedPath
    report.modify fun r => { r with declaration_counts.trusted := trusted.constMap.size }
    let candidate <- parseExport candidatePath
    report.modify fun r => { r with declaration_counts.candidate := candidate.constMap.size }
    pure (trusted, candidate)
  timed report "compare" fun _ => IO.ofExcept <|
    Comparator.compareAt trusted candidate (theoremNames ++ legalAxioms)
      definitionNames primitiveTargets
  timed report "axioms" fun _ => IO.ofExcept <|
    Comparator.checkAxioms candidate theoremNames definitionNames legalAxioms
  timed report "kernel" fun _ => match base with
    | none => runKernel candidate
    | some base => runKernelWithBase candidate base reused
  report.modify fun r => { r with status := "verified", phase := "complete" }

structure Request where
  id : Lean.Json
  config : String
  trusted : String
  candidate : String
  fresh_kernel : Bool := false
  deriving Lean.FromJson

partial def serveLoop (base : VerifiedBase) (input output : IO.FS.Stream) : IO Unit := do
  let line <- input.getLine
  if line.isEmpty then return
  let report <- IO.mkRef ({} : Report)
  let reused <- IO.mkRef (0 : Nat)
  let id <- IO.mkRef Lean.Json.null
  try
    let json <- IO.ofExcept <| Lean.Json.parse line
    id.set <| (json.getObjVal? "id").toOption.getD .null
    let request : Request <- IO.ofExcept <| Lean.fromJson? json
    verify report request.config request.trusted request.candidate
      (if request.fresh_kernel then none else some base) (some reused)
  catch e =>
    report.modify fun r => { r with error := some e.toString }
  let count <- reused.get
  let json := Lean.toJson (<- report.get)
    |>.setObjVal! "id" (<- id.get)
    |>.setObjVal! "reused_declarations" (Lean.toJson count)
    |>.setObjVal! "fresh_kernel" (Lean.toJson (count == 0))
  output.putStrLn json.compress
  output.flush
  serveLoop base input output

def serve (path : String) : IO UInt32 := do
  try
    let base <- loadBase path
    serveLoop base (<- IO.getStdin) (<- IO.getStdout)
    return 0
  catch e =>
    IO.eprintln <| (Lean.toJson ({ phase := "base", error := some e.toString } : Report)).compress
    return 1

end CertificateCheck

def main (args : List String) : IO UInt32 := do
  if let ["--serve", base] := args then
    return <- CertificateCheck.serve base
  let report <- IO.mkRef ({} : CertificateCheck.Report)
  let outputPath : Option String := if args.length == 4 then args[3]? else none
  try
    match args with
    | [config, trusted, candidate] | [config, trusted, candidate, _] =>
      CertificateCheck.verify report config trusted candidate
    | _ =>
      throw <| IO.userError
        "Usage: certificate-check config.json trusted-challenge.export candidate.export [report.json]"
  catch e =>
    report.modify fun r => { r with error := some e.toString }
  let result <- report.get
  let json := (Lean.toJson result).compress
  -- Write the optional report before emitting acceptance, so output failures fail closed.
  if let some path := outputPath then
    try
      IO.FS.writeFile path (json ++ "\n")
    catch e =>
      let rejected := { result with
        status := "rejected"
        phase := "output"
        error := some e.toString }
      IO.println <| (Lean.toJson rejected).compress
      return 1
  IO.println json
  return if result.status == "verified" then 0 else 1
