(* Concrete storage interfaces shared by execution and observation. *)
Theory solidityStorage
Ancestors
  solidityState solidityScalar vfmCompute keccak
Libs
  cv_transLib wordsLib intLib

(* Verifereum storage is a total function. Its canonical sparse cv encoding
 * omits zero entries, so encoding equality decides full extensional equality.
 *)
Theorem storage_encoding_injective:
  from_storage left = from_storage right ⇔ left = right
Proof
  metis_tac[vfmStateTheory.from_to_storage, cv_typeTheory.from_to_def]
QED

Theorem storage_equality_cv_rep[cv_rep]:
  b2c ((left : storage) = right) = cv_eq (from_storage left) (from_storage right)
Proof
  Cases_on ‘left = right’ >>
  simp[cvTheory.cv_eq_def, cvTheory.b2c_def, storage_encoding_injective]
QED
