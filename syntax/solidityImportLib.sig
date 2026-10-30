signature solidityImportLib =
sig
  include Abbrev

  (* Raised, with a message naming the offending node, for any JSON outside the
   * admitted vocabulary: an unknown nodeType, a missing or ill-typed required
   * field, or an unsupported feature. Nothing is dropped or defaulted.
   *)
  exception ImportError of string

  (* A SourceUnit AST node as a src_unit term, given the compiler's contracts
   * output for that source, which holds the storage layouts.
   *)
  val import_source_unit : JSON.value -> JSON.value -> term

  (* The named source unit of a solidity-hol-solc-artifact-v1 file written by
   * tools/export_solc_artifacts.py.
   *)
  val import_artifact : string -> string -> term

  (* The deployed bytecode of a contract of an artifact, as hex digits. *)
  val artifact_deployed_bytecode : string -> string -> string -> string
end
