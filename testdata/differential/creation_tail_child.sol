// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;

contract TailChild {
    uint256 public value;

    constructor(uint256 n) payable {
        require(n != 13, "rejected");
        value = 100 / n;
    }
}
