signature solidityPrepareLib =
sig
  include Abbrev

  datatype failure = MalformedInput | UnsupportedImport | UnsupportedLowering
                   | SourceRejected | InvalidCore
  exception PreparationError of failure * string
  val failure_name : failure -> string

  type prepared = {unit : term, program : term, source_valid : thm,
                   elaborates : thm, core_wf : thm}

  (* Check artifact format, compiler identity, pinned profile and exact settings.
   * root contains SOLIDITY_PIN and profiles/solc-0.8.37-via-ir-osaka.json.
   *)
  val read_artifact : {root : string, path : string} -> JSON.value

  (* Checked semantic preparation for an already imported unit. The caller
   * owns compiler/profile provenance when using this lower-level entry point.
   * SourceRejected includes source-subset restrictions of valid_src_unit.
   * HOL evaluation failures propagate; they are never input rejections.
   *)
  val prepare_unit : term -> prepared

  (* The normal consumer entry point. *)
  val prepare_artifact : {root : string, path : string, source : string} -> prepared
end
