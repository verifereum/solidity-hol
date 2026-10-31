// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract ShadowedBuiltins {
    function require(bool x) internal pure returns (uint256) { if (x) return 1; return 2; }
    function assert(bool x) internal pure returns (uint256) { if (x) return 3; return 4; }
    function revert() internal pure returns (uint256) { return 5; }
    function run(bool x) public pure returns (uint256, uint256, uint256) {
        return (require(x), assert(x), revert());
    }
}
