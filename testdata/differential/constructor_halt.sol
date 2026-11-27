// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;

contract ConstructorHalt {
    uint256 public mark;

    constructor(uint256 mode) {
        mark = mode;
        if (mode == 1) {
            assembly {
                stop()
            }
        }
        if (mode == 2) {
            // deploys code that returns 42
            assembly {
                mstore(0, 0x602a60005260206000f3)
                return(22, 10)
            }
        }
        mark = mode + 100;
    }
}
