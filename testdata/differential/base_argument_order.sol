// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

// Storage objects copied to base constructor memory parameters before a later
// argument's call changes that storage.
abstract contract BaseArgumentOrderBase {
    uint256 public n;

    constructor(uint256[] memory a, bytes memory b, uint256 x) {
        n = a.length * 100 + b.length * 10 + x;
    }
}

contract BaseArgumentOrder is BaseArgumentOrderBase {
    uint256[] s;
    bytes t;

    constructor() BaseArgumentOrderBase(s, t, bump()) {}

    function bump() internal returns (uint256) {
        s.push(7);
        t.push(0x2a);
        return 1;
    }
}
