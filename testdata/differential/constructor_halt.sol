// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;

contract ConstructorHalt {
    uint256 public mark;
    uint256 public immutable tag;

    constructor(uint256 mode) {
        mark = mode;
        tag = mode * 7;
        if (mode == 1) {
            assembly {
                stop()
            }
        }
        if (mode == 2) {
            // deploys 1024 bytes of 0x11, which cover the immutable's offset
            assembly {
                let p := mload(0x40)
                for { let i := 0 } lt(i, 0x400) { i := add(i, 32) } {
                    mstore(add(p, i), 0x1111111111111111111111111111111111111111111111111111111111111111)
                }
                return(p, 0x400)
            }
        }
        mark = mode + 100;
    }
}
