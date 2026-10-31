(* The machine a Yul runtime frame runs on.
 *
 * A frame is split the way the EVM boundary is: the frame's own fields
 * (address, call value, call data, memory, local scopes) are transient, while
 * the accounts and the log are the caller-observable world. Raw execution
 * leaves both changed; finish_yul_frame says which of them survives, rolling
 * the world back to its initial value for revert, invalid and out-of-fuel and
 * keeping it for a normal stop or a return. The world is a projection of the
 * machine rather than a nested record, so the evaluator's updates stay one
 * record deep.
 *
 * Memory is concrete and byte-addressed: a byte per address, absent bytes
 * being zero, with its active size beside it. A memory access raises the size
 * to the end of the highest word it touches, as the EVM's expansion does, and
 * an access of no bytes touches nothing. The pinned compiler never emits
 * msize(), so there is no builtin for it; the size is still there for the
 * frame's caller to read (yul_memory_size).
 *
 * Gas is not modelled: nothing in the pinned subset reads it.
 *)
Theory yulState
Ancestors
  vfmContext

Datatype:
  yul_world = <|
    accounts : evm_accounts;
    logs : event list
  |>
End

Datatype:
  yul_machine = <|
    accounts : evm_accounts;
    logs : event list;
    self_address : address;
    call_value : bytes32;
    call_data : byte list;
    memory : num |-> word8;
    memory_size : num;
    scopes : (string |-> bytes32) list
  |>
End

(* YulNormal is running off the end of the code, which the EVM sees as STOP.
 * Break, continue and leave are control outcomes inside the frame; one that
 * reaches the frame's end is an error rather than a halt.
 *)
Datatype:
  yul_completion
  = YulNormal
  | YulReturn (byte list)
  | YulRevert (byte list)
  | YulInvalid string
  | YulOutOfFuel
  | YulBreak
  | YulContinue
  | YulLeave
End

Datatype:
  yul_result = <| completion : yul_completion; machine : yul_machine |>
End

Datatype:
  yul_frame_observation
  = YulFrameSuccess (byte list) yul_world
  | YulFrameRevert (byte list) yul_world
  | YulFrameInvalid string
  | YulFrameResourceLimit
End

Definition yul_machine_world_def:
  yul_machine_world (m : yul_machine) : yul_world =
  <| accounts := m.accounts; logs := m.logs |>
End

(* What the frame's caller sees: a stop or a return commits what the frame
 * did, everything else that ends the frame leaves the world as it was.
 *)
Definition finish_yul_frame_def:
  finish_yul_frame initial final completion =
    case completion of
      YulNormal => YulFrameSuccess [] (yul_machine_world final)
    | YulReturn data => YulFrameSuccess data (yul_machine_world final)
    | YulRevert data => YulFrameRevert data (yul_machine_world initial)
    | YulInvalid reason => YulFrameInvalid reason
    | YulOutOfFuel => YulFrameResourceLimit
    | YulBreak => YulFrameInvalid "break escaped frame"
    | YulContinue => YulFrameInvalid "continue escaped frame"
    | YulLeave => YulFrameInvalid "leave escaped frame"
End

Definition yul_memory_size_def:
  yul_memory_size (m : yul_machine) = m.memory_size
End

Theorem finish_yul_frame_normal[simp]:
  finish_yul_frame initial final YulNormal =
  YulFrameSuccess [] (yul_machine_world final)
Proof
  simp[finish_yul_frame_def]
QED

Theorem finish_yul_frame_return[simp]:
  finish_yul_frame initial final (YulReturn data) =
  YulFrameSuccess data (yul_machine_world final)
Proof
  simp[finish_yul_frame_def]
QED

Theorem finish_yul_frame_revert[simp]:
  finish_yul_frame initial final (YulRevert data) =
  YulFrameRevert data (yul_machine_world initial)
Proof
  simp[finish_yul_frame_def]
QED

Theorem finish_yul_frame_escaped[simp]:
  finish_yul_frame initial final YulBreak =
    YulFrameInvalid "break escaped frame" ∧
  finish_yul_frame initial final YulContinue =
    YulFrameInvalid "continue escaped frame" ∧
  finish_yul_frame initial final YulLeave =
    YulFrameInvalid "leave escaped frame"
Proof
  simp[finish_yul_frame_def]
QED
