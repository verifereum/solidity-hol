// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Dispatch with only a nonpayable fallback: it runs on any calldata, empty
// included, and reverts on value.
contract FallbackOnly {
    uint256 private calls;

    fallback() external {
        calls += 1;
    }
}
