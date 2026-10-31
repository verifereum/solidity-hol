signature solidityImportLib =
sig
  include Abbrev

  (* An unknown nodeType or unsupported feature, naming the offending node.
   * Missing or ill-typed required fields raise MalformedInput instead.
   *)
  exception ImportError of string
  (* Missing or ill-typed required JSON fields. *)
  exception MalformedInput of string

  (* Raw, unchecked SourceUnit import. Validate valid_src_unit and the generated
   * core before execution; use solidityPrepareLib for artifact consumers.
   * A SourceUnit AST node as a src_unit term, given the compiler's contracts
   * output for that source, which holds the storage layouts.
   *)
  val import_source_unit : JSON.value -> JSON.value -> term

  (* Raw artifact import, checking only the artifact format. Callers own the
   * compiler/profile/settings contract and source/core validation; normal
   * artifact consumers use solidityPrepareLib.prepare_artifact.
   *)
  val import_artifact : string -> string -> term

  (* The deployed bytecode of a contract of an artifact, as hex digits. *)
  val artifact_deployed_bytecode : string -> string -> string -> string
end
