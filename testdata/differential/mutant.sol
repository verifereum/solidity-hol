// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// A deliberately different contract with the signature of PureCore.add
// (testdata/frontend/pure_core.sol): its addition wraps instead of panicking.
// tests/solidityDifferentialTestScript.sml runs it against the elaborated
// PureCore to check that the comparison reports a mismatching fixture.
contract Mutant {
    function add(uint8 x, uint8 y) public pure returns (uint8) {
        unchecked {
            return x + y;
        }
    }
}
