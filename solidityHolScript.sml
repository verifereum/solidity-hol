(*
 * Project build roll-up.
 *
 * Project theories should be added as ancestors here as they are introduced so
 * that building solidityHolTheory builds the complete development.
 *)
Theory solidityHol
Ancestors
  solidityAST solidityCore solidityCoreWf solidityState solidityEVMCall
  solidityEVMBoundaryProps solidityCoreWfTest
  solidityEVMCallTest solidityEVMCreateTest solidityEVMFrameTest
  solidityEVMReentryTest solidityEVMBookkeepingTest
  verifereum
