// SPDX-License-Identifier: MIT
pragma solidity >=0.8.0;

contract ExternalFunctionTargetCode {
    uint256 private counter;

    function quote(uint256 x) external pure returns (uint256) {
        return x + 10;
    }

    function mutate() external returns (uint256) {
        return ++counter;
    }

    function ping() external {}
}
