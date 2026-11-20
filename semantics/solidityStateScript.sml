(* Source-facing state blueprint. EVM correspondence beyond this observable
 * projection is deliberately not claimed; see docs/implementation-blueprint.md.
 *)
Theory solidityState
Ancestors
  solidityCore finite_map

(* original and to_delete are the transaction's EVM bookkeeping that
 * SELFDESTRUCT needs (EIP-6780): the original accounts are the world at the
 * transaction's start, with the accounts created since marked empty, and
 * to_delete lists the accounts the transaction's calls left pending deletion,
 * deleted when it settles (settle_source_world). The source never reads them;
 * it threads them through the message calls it hands to Verifereum. *)
Datatype:
  source_world = <|
    accounts : evm_accounts;
    transient : transient_storage;
    logs : event list;
    original : evm_accounts;
    to_delete : address list
  |>
End

(* Any single-typed binding may be captured and written (the checker's
 * convention), so a binding records no assignability.
 *)
Datatype:
  source_binding = <|
    binding_type : core_value_type;
    binding_value : runtime_value
  |>
End

Datatype:
  source_frame = <|
    self_address : address;
    code_address : address;
    sender_address : address;
    call_value : num;
    call_data : byte list;
    static_context : bool;
    tx_params : transaction_parameters
  |>
End

(* Scopes and targets are num-keyed finite maps (keyed by the ast_id's
 * number), which cv encodes as sptrees. Memory is the frame's EVM memory, a
 * byte per address (absent bytes are zero) with its active size, as the
 * compiled code sees it: the free memory pointer is the word at 0x40, and
 * memory references are addresses in it. Scopes are innermost
 * first. The immutables are the values of the contract's immutables the
 * deployed code holds, keyed by their declarations (one not there is zero);
 * NONE during creation, where they are words in the frame's reserved memory
 * instead, as the compiled constructor keeps them. The return
 * data is the frame's return data buffer, the last message call's return or
 * revert bytes, where the source knows it: NONE after a call whose return data
 * the source computes no bytes for (the ecrecover precompile).
 *)
Datatype:
  source_state = <|
    world : source_world;
    frame : source_frame;
    immutables : (num |-> scalar) option;
    scopes : (num |-> source_binding) list;
    memory : num |-> word8;
    memory_size : num;
    targets : num |-> captured_target;
    return_data : byte list option
  |>
End

(* Execution evidence is separate from persistent world and rollback state.
 * These tags reserve query-specific observations; call/create meanings are NOT
 * settled. An authoritative gas projection must follow Vyper-HOL issue #98.
 *)
Datatype:
  gas_observation
  = GasLeftObservation num
  | CallGasObservation num
  | CreateGasObservation num
End

Datatype:
  source_result = <|
    completion : source_completion;
    state : source_state;
    unused_gas_evidence : gas_observation list
  |>
End

(* Requested gas is a source operand, not an oracle replacement. Available gas
 * and concrete CALL overhead remain adapter/simulation obligations.
 *)
Datatype:
  bytecode_request
  = CallRequest external_kind address (byte list) num (num option)
  | CreateRequest (byte list) num (num option) (bytes32 option)
End

Definition project_evm_world_def:
  project_evm_world (es : execution_state) =
    case es.contexts of
      [] => NONE
    | (ctxt, checkpoint)::rest => SOME <|
        accounts := es.rollback.accounts;
        transient := es.rollback.tStorage;
        logs := ctxt.logs;
        original := es.originalAccounts;
        to_delete := es.rollback.toDelete
      |>
End

(* Raw results retain provisional state. Commit policy does not treat invalid
 * input/fuel exhaustion as either success or a Solidity revert.
 *)
Datatype:
  frame_observation
  = FrameSuccess (runtime_value list) source_world
  | FrameRevert (byte list) source_world
  | FrameAbort source_world
  | FrameHalt (byte list) source_world
  | FramePanic num source_world
  | FrameInvalid string
  | FrameResourceLimit
End

Definition finish_source_frame_def:
  finish_source_frame initial final completion =
    case completion of
      NormalCompletion => FrameSuccess [] final
    | ReturnCompletion values => FrameSuccess values final
    | RevertCompletion data => FrameRevert data initial
    | AbortCompletion => FrameAbort initial
    | HaltCompletion data => FrameHalt data final
    | PanicCompletion code => FramePanic code initial
    | FuelExhausted => FrameResourceLimit
    | InvalidCompletion reason => FrameInvalid reason
    | BreakCompletion => FrameInvalid "break escaped frame"
    | ContinueCompletion => FrameInvalid "continue escaped frame"
End

Theorem source_revert_restores_world:
  finish_source_frame initial final (RevertCompletion data) =
    FrameRevert data initial
Proof
  simp[finish_source_frame_def]
QED

Theorem source_exhaustion_does_not_commit:
  finish_source_frame initial final FuelExhausted = FrameResourceLimit
Proof
  simp[finish_source_frame_def]
QED
