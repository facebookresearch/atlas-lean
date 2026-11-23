/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Header JSON exporter using Lean's official parser.
The header/import syntax patterns follow Lake.CLI.Shake (Mario Carneiro and
Sebastian Ullrich); no source lexer is used here.
-/
import Lean.Parser.Module
import Lean.Data.Json

open Lean

private structure SourcePositions where
  parsed : FileMap
  original : FileMap
  normalized : Bool

private def originalPos (positions : SourcePositions) (pos : String.Pos.Raw) : String.Pos.Raw :=
  if positions.normalized then
    positions.original.ofPosition (positions.parsed.toPosition pos)
  else pos

private def byteSpan (positions : SourcePositions) (start stop : String.Pos.Raw) : Json :=
  Json.mkObj [
    ("start_byte", toJson (originalPos positions start).byteIdx),
    ("end_byte", toJson (originalPos positions stop).byteIdx)]

private def syntaxSpan (positions : SourcePositions) (stx : Syntax) : Json :=
  match stx.getPos?, stx.getTailPos? with
  | some start, some stop => byteSpan positions start stop
  | _, _ => Json.null

private def leadingSpan (positions : SourcePositions) (stx : Syntax) : Json :=
  match stx.getHeadInfo? with
  | some (.original leading _ _ _) => byteSpan positions leading.startPos leading.stopPos
  | _ => Json.null

private def trailingSpan (positions : SourcePositions) (stx : Syntax) : Json :=
  match stx.getTailInfo? with
  | some (.original _ _ trailing _) => byteSpan positions trailing.startPos trailing.stopPos
  | _ => Json.null

private def tokenJson (positions : SourcePositions) (stx : Syntax) (kind spelling : String) : Json :=
  let text := match stx.getPos?, stx.getTailPos? with
    | some start, some stop =>
      let source := positions.original.source
      source.extract (source.pos! (originalPos positions start))
        (source.pos! (originalPos positions stop))
    | _, _ => spelling
  Json.mkObj [
    ("kind", toJson kind), ("text", toJson text), ("parsed_text", toJson spelling),
    ("span", syntaxSpan positions stx),
    ("leading_span", leadingSpan positions stx), ("trailing_span", trailingSpan positions stx)]

private partial def tokensJson (positions : SourcePositions) (stx : Syntax) : Array Json :=
  match stx with
  | .node _ _ args => args.foldl (fun result arg => result ++ tokensJson positions arg) #[]
  | .atom _ text => #[tokenJson positions stx "atom" text]
  | .ident _ spelling _ _ => #[tokenJson positions stx "ident" spelling.toString]
  | .missing => #[]

private def syntaxJson (positions : SourcePositions) (stx : Syntax) : Json :=
  Json.mkObj [
    ("span", syntaxSpan positions stx), ("leading_span", leadingSpan positions stx),
    ("trailing_span", trailingSpan positions stx), ("tokens", toJson (tokensJson positions stx))]

private def importJson (positions : SourcePositions) (stx : TSyntax ``Parser.Module.import) : Json :=
  match stx with
  | `(Parser.Module.import| $[public%$publicTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id) =>
    let modifiers := (if publicTk?.isSome then #["public"] else #[]) ++
      (if metaTk?.isSome then #["meta"] else #[]) ++
      (if allTk?.isSome then #["all"] else #[])
    Json.mkObj [
      ("module", toJson id.getId.toString), ("modifiers", toJson modifiers),
      ("is_exported", toJson publicTk?.isSome), ("is_meta", toJson metaTk?.isSome),
      ("import_all", toJson allTk?.isSome), ("source", syntaxJson positions stx.raw)]
  | _ => Json.mkObj [
      ("status", toJson "invalid_import_syntax"), ("source", syntaxJson positions stx.raw)]

private def messageJson (msg : Message) : IO Json := do
  let severity := match msg.severity with
    | .error => "error"
    | .warning => "warning"
    | .information => "information"
  return Json.mkObj [
    ("severity", toJson severity), ("message", toJson (← msg.data.toString)),
    ("formatted", toJson (← msg.toString)), ("line", toJson msg.pos.line),
    ("column", toJson msg.pos.column)]

private def probe (file : String) : IO (Json × Bool) := do
  let text ← IO.FS.readFile file
  let input := Parser.mkInputContext text file
  let normalized := input.inputString != text
  let positions : SourcePositions := {
    parsed := input.fileMap,
    original := if normalized then FileMap.ofString text else input.fileMap,
    normalized }
  let (header, state, messages) ← Parser.parseHeader input
  let errors ← messages.toList.toArray.mapM messageJson
  let failed := messages.hasErrors || state.recovering
  let bodyBoundary := originalPos positions state.pos
  match header with
  | `(Parser.Module.header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $imports*) =>
    let headerEnd := originalPos positions (header.raw.getTailPos?.getD state.pos)
    let newline := text.pos! headerEnd |>.find '\n'
    let shakeInsertion := (newline.next?.getD newline).offset.byteIdx
    let insertion := if moduleTk?.isNone && preludeTk?.isNone && imports.isEmpty then
        bodyBoundary.byteIdx
      else shakeInsertion
    return (Json.mkObj [
      ("path", toJson file), ("status", toJson (if failed then "parse_error" else "parsed")),
      ("source_utf8_bytes", toJson text.utf8ByteSize),
      ("is_module", toJson moduleTk?.isSome), ("is_prelude", toJson preludeTk?.isSome),
      ("module_token", toJson (moduleTk?.map (syntaxJson positions))),
      ("prelude_token", toJson (preludeTk?.map (syntaxJson positions))),
      ("imports", toJson (imports.map (importJson positions))),
      ("header_span", syntaxSpan positions header.raw),
      ("header_end_byte", toJson headerEnd.byteIdx),
      ("insertion_byte", toJson insertion), ("shake_insertion_byte", toJson shakeInsertion),
      ("body_boundary_byte", toJson bodyBoundary.byteIdx), ("parse_errors", toJson errors)], failed)
  | _ =>
    return (Json.mkObj [
      ("path", toJson file), ("status", toJson "invalid_header_syntax"),
      ("source_utf8_bytes", toJson text.utf8ByteSize),
      ("body_boundary_byte", toJson bodyBoundary.byteIdx), ("parse_errors", toJson errors)], true)

def main (files : List String) : IO UInt32 := do
  if files.isEmpty then
    (← IO.getStderr).putStrLn "usage: header_probe SOURCE.lean [SOURCE.lean ...]"
    return 2
  let mut failed := false
  for file in files do
    try
      let (result, hasError) ← probe file
      IO.println result.compress
      failed := failed || hasError
    catch error =>
      IO.println (Json.mkObj [
        ("path", toJson file), ("status", toJson "io_error"),
        ("parse_errors", toJson #[error.toString])]).compress
      failed := true
  return if failed then 1 else 0
