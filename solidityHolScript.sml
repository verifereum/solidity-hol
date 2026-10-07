(*
 * Project build roll-up.
 *
 * Project theories should be added as ancestors here as they are introduced so
 * that building solidityHolTheory builds the complete development.
 *)
Theory solidityHol
Ancestors
  solidityAST solidityCore solidityState solidityEVMCall solidityEVMBoundaryProps
  solidityEVMCallTest solidityEVMCreateTest solidityEVMFrameTest
  solidityEVMReentryTest solidityEVMBookkeepingTest
  solidityValue solidityInterpreter solidityInterpreterTest
  verifereum
