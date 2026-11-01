// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Dispatch with only receive: it runs on empty calldata, and anything else
// reverts.
contract ReceiveOnly {
    uint256 private received;

    receive() external payable {
        received += msg.value;
    }
}
