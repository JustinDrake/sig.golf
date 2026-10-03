import CertificateCheck

/-!
Run from verifier/.tools/comparator after compiling/linking CertificateCheck:
  lake env lean ../../tests/CertificateTests.lean
Only these organizer-owned fixtures are elaborated/exported by the tests. The
checker itself sees declarative files, including deliberately corrupted exports.
-/

namespace CertificateTests

open Lean

def execute (cmd : String) (args : Array String) : IO String := do
  let output <- IO.Process.output { cmd, args }
  if output.exitCode != 0 then
    throw <| IO.userError s!"{cmd} failed ({output.exitCode}): {output.stderr}\n{output.stdout}"
  pure output.stdout

def exportModule (module : String) (targets : Array String) : IO String :=
  execute ".lake/packages/lean4export/.lake/build/bin/lean4export" (#[module, "--"] ++ targets)

def check (config trusted candidate : String) (expected : String) : IO Unit := do
  let dir : System.FilePath := ".lake/certificate-tests"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "config.json") config
  IO.FS.writeFile (dir / "trusted.export") trusted
  IO.FS.writeFile (dir / "candidate.export") candidate
  let output <- IO.Process.output {
    cmd := ".lake/build/bin/certificate-check"
    args := #[(dir / "config.json").toString, (dir / "trusted.export").toString,
      (dir / "candidate.export").toString, (dir / "report.json").toString]
  }
  let json <- IO.ofExcept <| Json.parse output.stdout
  let status <- IO.ofExcept <| json.getObjValAs? String "status"
  let phase <- IO.ofExcept <| json.getObjValAs? String "phase"
  unless phase == expected && (status == "verified") == (expected == "complete") &&
      (output.exitCode == 0) == (expected == "complete") do
    throw <| IO.userError s!"Expected {expected}, got {output.exitCode}: {output.stdout} {output.stderr}"
  let file <- IO.FS.readFile (dir / "report.json")
  unless file == output.stdout do
    throw <| IO.userError "stdout and optional report differ"
  let phases <- IO.ofExcept <| json.getObjVal? "phases_seconds"
  for key in #["parse", "compare", "axioms", "kernel"] do
    let seconds <- IO.ofExcept <| phases.getObjValAs? Float key
    unless seconds >= 0 do throw <| IO.userError s!"Negative phase duration: {key}"
    if expected == "complete" then
      unless seconds > 0 do throw <| IO.userError s!"Unmeasured successful phase: {key}"
  if expected == "complete" then
    let counts <- IO.ofExcept <| json.getObjVal? "declaration_counts"
    let trustedCount <- IO.ofExcept <| counts.getObjValAs? Nat "trusted"
    let candidateCount <- IO.ofExcept <| counts.getObjValAs? Nat "candidate"
    unless trustedCount > 0 && candidateCount > 0 do
      throw <| IO.userError "Missing declaration counts"

def nameIndex (items : Array Json) (suffix : String) : IO Nat := do
  let mut names : Std.HashMap Nat Name := { (0, .anonymous) }
  for item in items do
    if let .ok data := item.getObjVal? "str" then
      let pre <- IO.ofExcept <| data.getObjValAs? Nat "pre"
      let str <- IO.ofExcept <| data.getObjValAs? String "str"
      let idx <- IO.ofExcept <| item.getObjValAs? Nat "in"
      let name := Name.str names[pre]! str
      names := names.insert idx name
      if name.toString == suffix || (!suffix.contains '.' && str == suffix) then return idx
    if let .ok data := item.getObjVal? "num" then
      let pre <- IO.ofExcept <| data.getObjValAs? Nat "pre"
      let n <- IO.ofExcept <| data.getObjValAs? Nat "i"
      let idx <- IO.ofExcept <| item.getObjValAs? Nat "in"
      names := names.insert idx (.num names[pre]! n)
  throw <| IO.userError s!"Missing fixture name {suffix}"

def changeDecl (items : Array Json) (kind : String) (name : Nat)
    (change : Json -> Json) : IO (Array Json) := do
  let mut found := false
  let changed := items.map fun item =>
    if let .ok info := item.getObjVal? kind then
      if (info.getObjValAs? Nat "name").toOption == some name then
        change info |> fun info => item.setObjVal! kind info
      else item
    else item
  for item in items do
    if let .ok info := item.getObjVal? kind then
      if (info.getObjValAs? Nat "name").toOption == some name then found := true
  unless found do throw <| IO.userError s!"Missing declaration {kind} {name}"
  return changed

def encode (items : Array Json) : String :=
  String.intercalate "\n" (items.toList.map Json.compress) ++ "\n"

def config : Json := Json.mkObj [
  ("theorem_names", toJson #["SigGolf.Challenge.certificate", "SigGolf.Challenge.image_binding",
    "SigGolf.Challenge.box_certificate"]),
  ("definition_names", toJson #["SigGolf.Challenge.submission"]),
  ("permitted_axioms", toJson #["propext", "Quot.sound", "Classical.choice"]),
  ("enable_nanoda", toJson false)
]

def intrinsicInvalidInductive : IO Unit := do
  let name := `Negative
  let ctor := `Negative.mk
  let ty := Expr.sort (.succ .zero)
  let self := Expr.const name []
  let negative := Expr.forallE `x self (.sort .zero) .default
  let ctorType := Expr.forallE `f negative self .default
  let constants : Std.HashMap Name ConstantInfo := {}
  let constants := constants.insert name (.inductInfo {
    name, levelParams := [], type := ty, numParams := 0, numIndices := 0,
    all := [name], ctors := [ctor], numNested := 0, isRec := true,
    isUnsafe := false, isReflexive := false })
  let constants := constants.insert ctor (.ctorInfo {
    name := ctor, levelParams := [], type := ctorType, induct := name,
    cidx := 0, numParams := 0, numFields := 1, isUnsafe := false })
  let mut rejected := false
  try
    CertificateCheck.runKernel { constMap := constants, constOrder := #[name, ctor] }
  catch _ => rejected := true
  unless rejected do throw <| IO.userError "Kernel accepted an intrinsic non-positive inductive"
  IO.println "PASS intrinsic non-positive inductive rejected by empty replay"

def checkServe (base trusted : String)
    (requests : Array (Prod String (Prod String (Prod Bool (Prod String Bool))))) : IO Unit := do
  let dir : System.FilePath := ".lake/certificate-tests"
  IO.FS.writeFile (dir / "base.export") base
  IO.FS.writeFile (dir / "serve-trusted.export") trusted
  IO.FS.writeFile (dir / "serve-config.json") config.compress
  let mut lines := #[]
  for i in [:requests.size] do
    let (id, candidate, fresh, _, _) := requests[i]!
    let path := dir / s!"serve-candidate-{i}.export"
    IO.FS.writeFile path candidate
    lines := lines.push <| Json.mkObj [
      ("id", toJson id), ("config", toJson (dir / "serve-config.json").toString),
      ("trusted", toJson (dir / "serve-trusted.export").toString),
      ("candidate", toJson path.toString), ("fresh_kernel", toJson fresh)]
  let output <- IO.Process.output {
    cmd := ".lake/build/bin/certificate-check"
    args := #["--serve", (dir / "base.export").toString]
  } (some (encode lines))
  unless output.exitCode == 0 do
    throw <| IO.userError s!"Serve failed: {output.stderr} {output.stdout}"
  let responses := output.stdout.splitOn "\n" |>.filter (fun line => !line.isEmpty) |>.toArray
  unless responses.size == requests.size do throw <| IO.userError "Incorrect serve response count"
  for i in [:requests.size] do
    let (id, _, _, expected, reuse) := requests[i]!
    let json <- IO.ofExcept <| Json.parse responses[i]!
    let gotId <- IO.ofExcept <| (json.getObjValAs? String "id").mapError
      (fun error => s!"{error}: {json.compress}")
    let status <- IO.ofExcept <| json.getObjValAs? String "status"
    let phase <- IO.ofExcept <| json.getObjValAs? String "phase"
    let reused <- IO.ofExcept <| json.getObjValAs? Nat "reused_declarations"
    let fresh <- IO.ofExcept <| json.getObjValAs? Bool "fresh_kernel"
    unless gotId == id && phase == expected && (status == "verified") == (expected == "complete") &&
        (reused > 0) == reuse && fresh == !reuse do
      throw <| IO.userError s!"Unexpected serve response for {id}: {json.compress}"
    IO.println s!"PASS serve {id} (reused={reused}, fresh={fresh})"
  let badStartup <- IO.Process.output {
    cmd := ".lake/build/bin/certificate-check", args := #["--serve", (dir / "absent.export").toString] }
  unless badStartup.exitCode != 0 && badStartup.stdout.isEmpty do
    throw <| IO.userError "Invalid base startup did not fail closed"
  discard <| IO.ofExcept <| Json.parse badStartup.stderr
  IO.println "PASS serve invalid base startup fails closed on stderr"

def run : IO Unit := do
  discard <| execute "lean" #["--root=../../tests", "-o", ".lake/build/lib/lean/CertificateFixture.olean",
    "../../tests/CertificateFixture.lean"]
  let targets := CertificateCheck.primitiveTargets.map Name.toString ++
    #["propext", "Quot.sound", "Classical.choice", "SigGolf.Challenge.submission",
      "SigGolf.Challenge.certificate", "SigGolf.Challenge.image_binding", "SigGolf.Challenge.box_certificate",
      "CertificateBase.helper"]
  let trusted <- exportModule "CertificateFixture" targets
  let items <- trusted.splitOn "\n" |>.filter (fun line => !line.isEmpty) |>.toArray.mapM
    (fun line => IO.ofExcept <| Json.parse line)
  check config.compress trusted trusted "complete"
  let fixtureDir : System.FilePath := ".lake/certificate-tests"
  IO.FS.writeFile (fixtureDir / "valid-config.json") config.compress
  IO.FS.writeFile (fixtureDir / "valid-trusted.export") trusted
  IO.FS.writeFile (fixtureDir / "valid-candidate.export") trusted
  IO.println "PASS valid declarative certificate, timings/counts, optional report"
  check (config.setObjVal! "enable_nanoda" (toJson true)).compress trusted trusted "config"
  IO.println "PASS unsupported nanoda refused"
  check config.compress trusted "not an export\nnot JSON\n" "parse"
  IO.println "PASS malformed export rejected"
  let literal <- nameIndex items "trustedLiteral"
  let badImage <- changeDecl items "def" literal fun data =>
    data.setObjVal! "value" (toJson (999999 : Nat))
  let badImage := badImage.push <| Json.mkObj [("ie", toJson (999999 : Nat)), ("natVal", toJson "18")]
  -- Expressions must precede their references in the declarative format.
  let badImage := #[badImage[0]!, badImage.back!] ++ badImage.extract 1 (badImage.size - 1)
  check config.compress trusted (encode badImage) "compare"
  IO.println "PASS exact image literal dependency mismatch rejected"
  let cert <- nameIndex items "certificate"
  let badProof <- changeDecl items "thm" cert fun data => data.setObjVal! "value" (toJson (999999 : Nat))
  let badProof := #[badProof[0]!, Json.mkObj [("ie", toJson (999999 : Nat)), ("sort", toJson (0 : Nat))]] ++
    badProof.extract 1 badProof.size
  check config.compress trusted (encode badProof) "kernel"
  IO.println "PASS intrinsically ill-typed theorem proof rejected by kernel"
  let badStatement <- changeDecl badProof "thm" cert fun data => data.setObjVal! "type" (toJson (999999 : Nat))
  check config.compress trusted (encode badStatement) "compare"
  IO.println "PASS selected theorem statement mismatch rejected"
  let gcd <- nameIndex items "Nat.gcd"
  let missingPrimitive := items.filter fun item =>
    match item.getObjVal? "def" with
    | .ok data => (data.getObjValAs? Nat "name").toOption != some gcd
    | .error _ => true
  check config.compress trusted (encode missingPrimitive) "compare"
  IO.println "PASS missing kernel primitive rejected"
  let box <- nameIndex items "Box"
  let badRecursor <- items.mapM fun item => do
    match item.getObjVal? "inductive" with
    | .error _ => pure item
    | .ok data =>
      let recs <- IO.ofExcept <| data.getObjValAs? (Array Json) "recs"
      let recs <- recs.mapM fun recursor => do
        let all <- IO.ofExcept <| recursor.getObjValAs? (Array Nat) "all"
        if all.contains box then
          let motives <- IO.ofExcept <| recursor.getObjValAs? Nat "numMotives"
          pure <| recursor.setObjVal! "numMotives" (toJson (motives + 1))
        else pure recursor
      pure <| item.setObjVal! "inductive" (data.setObjVal! "recs" (toJson recs))
  check config.compress trusted (encode badRecursor) "kernel"
  IO.println "PASS invalid recursor metadata rejected by kernel"
  let illegalName := Json.mkObj [("in", toJson (999998 : Nat)),
    ("str", Json.mkObj [("pre", toJson (0 : Nat)), ("str", toJson "forbidden")])]
  let mut certType := 0
  for item in items do
    if let .ok data := item.getObjVal? "thm" then
      if (data.getObjValAs? Nat "name").toOption == some cert then
        certType <- IO.ofExcept <| data.getObjValAs? Nat "type"
  let illegalAxiom := Json.mkObj [("axiom", Json.mkObj [
    ("name", toJson (999998 : Nat)), ("levelParams", toJson (#[] : Array Nat)),
    ("type", toJson certType), ("isUnsafe", toJson false)])]
  let illegalExpr := Json.mkObj [("ie", toJson (999998 : Nat)), ("const", Json.mkObj [
    ("name", toJson (999998 : Nat)), ("us", toJson (#[] : Array Nat))])]
  let badAxiom <- changeDecl items "thm" cert fun data => data.setObjVal! "value" (toJson (999998 : Nat))
  -- The axiom's type is already present immediately before the selected theorem.
  let mut augmented := #[]
  for item in badAxiom do
    if let .ok data := item.getObjVal? "thm" then
      if (data.getObjValAs? Nat "name").toOption == some cert then
        augmented := augmented ++ #[illegalName, illegalAxiom, illegalExpr]
    augmented := augmented.push item
  check config.compress trusted (encode augmented) "axioms"
  IO.println "PASS forbidden axiom rejected"
  intrinsicInvalidInductive
  let base <- exportModule "CertificateFixture" <| CertificateCheck.primitiveTargets.map Name.toString ++
    #["propext", "Quot.sound", "Classical.choice", "CertificateBase.helper"]
  let helper <- nameIndex items "helper"
  let badBaseProof <- changeDecl items "thm" helper fun data => data.setObjVal! "value" (toJson (999999 : Nat))
  let badBaseProof := #[badBaseProof[0]!, Json.mkObj [("ie", toJson (999999 : Nat)), ("sort", toJson (0 : Nat))]] ++
    badBaseProof.extract 1 badBaseProof.size
  let missing := items ++ #[
    Json.mkObj [("in", toJson (999997 : Nat)), ("str", Json.mkObj [("pre", toJson (0 : Nat)), ("str", toJson "missing")])],
    Json.mkObj [("in", toJson (999996 : Nat)), ("str", Json.mkObj [("pre", toJson (0 : Nat)), ("str", toJson "unused")])],
    Json.mkObj [("ie", toJson (999997 : Nat)), ("const", Json.mkObj [("name", toJson (999997 : Nat)), ("us", toJson (#[] : Array Nat))])],
    Json.mkObj [("def", Json.mkObj [("name", toJson (999996 : Nat)), ("levelParams", toJson (#[] : Array Nat)),
      ("type", toJson (999997 : Nat)), ("value", toJson (999997 : Nat)), ("hints", toJson "opaque"),
      ("safety", toJson "safe"), ("all", toJson (#[] : Array Nat))])]]
  checkServe base trusted #[
    ("valid", trusted, false, "complete", true),
    ("bad-delta-proof", encode badProof, false, "kernel", true),
    ("valid-after-rejection", trusted, false, "complete", true),
    ("forced-fresh", trusted, true, "complete", false),
    ("bad-base-proof-same-kind-and-type", encode badBaseProof, false, "kernel", false),
    ("valid-after-fallback", trusted, false, "complete", true),
    ("image-literal-mismatch", encode badImage, false, "compare", false),
    ("missing-dependency", encode missing, false, "kernel", false),
    ("invalid-delta-recursor", encode badRecursor, false, "kernel", true)]
  -- A differing definition hole also prevents reuse when present in the verified base.
  let submission <- nameIndex items "submission"
  let badDefinition <- changeDecl items "def" submission fun data => data.setObjVal! "value" (toJson (999999 : Nat))
  let badDefinition := #[badDefinition[0]!, Json.mkObj [("ie", toJson (999999 : Nat)), ("natVal", toJson "18")]] ++
    badDefinition.extract 1 badDefinition.size
  checkServe trusted trusted #[("changed-base-definition", encode badDefinition, false, "kernel", false)]
  -- Reuse the upstream comparator fixtures without changing their source/config.
  for project in #["simple_match", "simple_mismatch", "simple_kind_mismatch", "simple_axiom_issue",
      "def_hole", "def_hole_type_mismatch", "def_hole_kind_mismatch", "def_hole_axiom_issue",
      "theorem_hole_issue", "opaque_value", "primitive_issue", "char_ofnat_issue"] do
    let dir : System.FilePath := "tests/projects" / project
    let cfgText <- IO.FS.readFile (dir / "config.json")
    let cfg : CertificateCheck.Config <- IO.ofExcept <| fromJson? (<- IO.ofExcept <| Json.parse cfgText)
    let expectedJson <- IO.ofExcept <| Json.parse (<- IO.FS.readFile (dir / "test.json"))
    let expectedCode <- IO.ofExcept <| expectedJson.getObjValAs? Nat "exit_code"
    for module in #["Challenge", "Solution"] do
      discard <| execute "lean" #[s!"--root={dir}", "-o", s!".lake/build/lib/lean/{module}.olean",
        (dir / s!"{module}.lean").toString]
    let targets := CertificateCheck.primitiveTargets.map Name.toString ++ cfg.theorem_names ++
      cfg.permitted_axioms ++ cfg.definition_names.getD #[]
    let challenge <- exportModule "Challenge" targets
    let solution <- exportModule "Solution" targets
    let report <- IO.mkRef ({} : CertificateCheck.Report)
    let dir : System.FilePath := ".lake/certificate-tests"
    IO.FS.writeFile (dir / "config.json") cfgText
    IO.FS.writeFile (dir / "trusted.export") challenge
    IO.FS.writeFile (dir / "candidate.export") solution
    let mut accepted := true
    try
      CertificateCheck.verify report (dir / "config.json").toString
        (dir / "trusted.export").toString (dir / "candidate.export").toString
    catch _ => accepted := false
    unless accepted == (expectedCode == 0) do
      throw <| IO.userError s!"Upstream comparator fixture disagrees: {project}"
    IO.println s!"PASS upstream comparator fixture {project} (accepted={accepted})"

end CertificateTests

#eval CertificateTests.run
