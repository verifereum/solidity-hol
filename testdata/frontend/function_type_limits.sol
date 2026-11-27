// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;

contract FunctionTypeLimits {
    struct Entry {
        function(uint256) internal pure returns (uint256) operation;
    }

    function fromCalldata() public pure returns (uint256) {
        Entry calldata entry;
        assembly { entry := 4 }
        return entry.operation(5);
    }

    function inc(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }

    function local(uint256 x) public pure returns (uint256) {
        function(uint256) pure returns (uint256) f = inc;
        return f(x);
    }

    function compares() public pure returns (bool) {
        function(uint256) pure returns (uint256) f = inc;
        return f == inc;
    }

    function inAssembly() public pure returns (uint256 r) {
        function(uint256) pure returns (uint256) f = inc;
        assembly { r := f }
    }
}
