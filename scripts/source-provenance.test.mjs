import {test} from 'node:test';
import {mkdtempSync, writeFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join, resolve} from 'node:path';
import {execFileSync} from 'node:child_process';

test('source provenance preserves legacy, analysis and via-IR admission boundaries', () => {
  const dir = mkdtempSync(join(tmpdir(), 'solidity-provenance-'));
  try {
    const check = join(dir, 'Check.lean');
    writeFileSync(check, `import Solidity.Frontend.Source
open Lean Solidity.Frontend.Source
private def put (json : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((json.getObj?.toOption.map (·.toList)).getD []).filter (·.1 != key))
#eval do
  let load (name : String) : IO (Json × Json × Provenance) := do
    let fixture ← IO.ofExcept (Json.parse (← IO.FS.readFile
      (${JSON.stringify(resolve('tests/solc'))} ++ "/" ++ name ++ ".ast.json")))
    let ast ← IO.ofExcept (fixture.getObjVal? "ast")
    let provenance ← IO.ofExcept (read fixture ast)
    pure (fixture, ast, provenance)
  let (fixture, ast, legacyPipeline) ← load "SourceCoder"
  unless !legacyPipeline.legacyFixture && legacyPipeline.pipeline == some Pipeline.legacy &&
      legacyPipeline.requestedCoder == AbiCoder.v1 && legacyPipeline.effectiveCoder == some AbiCoder.v1 do
    throw (IO.userError "analysed legacy-pipeline v1 changed")
  let (irFixture, _, ir) ← load "SourceCoderIR"
  unless !ir.legacyFixture && ir.pipeline == some Pipeline.viaIR &&
      ir.requestedCoder == AbiCoder.v1 && ir.effectiveCoder == some AbiCoder.v2 do
    throw (IO.userError "via-IR must retain requested v1 but use effective v2")
  for (fixture, provenance) in [(fixture, legacyPipeline), (irFixture, ir)] do
    let header : Json ← IO.ofExcept (fixture.getObjVal? "header")
    let settings ← IO.ofExcept (header.getObjVal? "settings")
    unless provenance.settings == settings.compress do
      throw (IO.userError "recorded analysis settings changed")
  let (_, _, modern) ← load "SourceAdmission"
  unless !modern.legacyFixture && modern.effectiveCoder == some AbiCoder.v2 do
    throw (IO.userError "modern default v2 changed")
  let (_, _, historical) ← load "TestSuite"
  unless historical.legacyFixture && historical.pipeline.isNone &&
      historical.settings.isEmpty && historical.effectiveCoder == some AbiCoder.v2 do
    throw (IO.userError "historical default boundary changed")
  let header : Json ← IO.ofExcept (fixture.getObjVal? "header")
  let .obj headerFields := header | throw (IO.userError "header is not an object")
  let fields : List (String × Json) := headerFields.toList
  let historicalHeader := Json.mkObj (fields.filter fun (key, _) =>
    ["solcVersion", "sourceSha256", "solkeyCommit", "source"].contains key)
  let historicalFixture := put fixture "header" historicalHeader
  let v1 ← IO.ofExcept (read historicalFixture ast)
  unless v1.legacyFixture && v1.pipeline.isNone && v1.settings.isEmpty &&
      v1.requestedCoder == AbiCoder.v1 && v1.effectiveCoder.isNone do
    throw (IO.userError "historical v1 gained an invented effective coder")
  unless !(readCompilerCode (put historicalFixture "compilerCode" (Json.mkObj [])) ast v1).isOk do
    throw (IO.userError "historical input acquired static compiler code")
  let downgraded := Json.mkObj (fields.filter (·.1 != "provenanceVersion"))
  unless !(read (put fixture "header" downgraded) ast).isOk do
    throw (IO.userError "partial modern metadata became historical")
  let settings ← IO.ofExcept (header.getObjVal? "settings")
  let malformed := put header "settings" (put settings "viaIR" (.str "true"))
  unless !(read (put fixture "header" malformed) ast).isOk do
    throw (IO.userError "malformed pipeline setting admitted")
  let mismatch := put header "acceptedPragmas" (.arr #[])
  unless !(read (put fixture "header" mismatch) ast).isOk do
    throw (IO.userError "mismatched pragma provenance admitted")
`);
    execFileSync('lake', ['--quiet', '--no-build', 'lean', check, '--', '--tstack=131072'],
      {stdio:'pipe', encoding:'utf8', timeout:60000});
  } finally {
    rmSync(dir, {recursive:true, force:true});
  }
});
