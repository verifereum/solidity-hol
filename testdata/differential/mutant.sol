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

// Token.mint (testdata/differential/token.sol) with the Transfer event's
// indexed arguments swapped: the same outcome and storage, different logs.
contract LogMutant {
    event Transfer(address indexed from, address indexed to, uint256 value);

    mapping(address => uint256) private balances;
    mapping(address => mapping(address => uint256)) private allowances;
    uint256 private supply;

    function mint(address to, uint256 value) external {
        require(to != address(0), "mint to zero");
        supply += value;
        balances[to] += value;
        emit Transfer(to, address(0), value);
    }
}
