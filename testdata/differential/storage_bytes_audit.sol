// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;
contract StorageBytesAudit {
    bytes b;

    function pushDirty() external returns (bytes1, bytes1) {
        assembly { sstore(b.slot, shl(240, 0x1122)) }
        bytes1 r1 = b.push();
        bytes1 r2 = b.push();
        return (r1, r2);
    }

    function pushValueDirty() external returns (bytes1) {
        assembly { sstore(b.slot, shl(240, 0x1122)) }
        b.push(0x33);
        return b.push();
    }

    function pushShortDirty() external returns (bytes1, bytes1) {
        assembly { sstore(b.slot, 0x111111111111111111111111111111111111111111111111111111111111223c) }
        bytes1 r1 = b.push();
        bytes1 r2 = b.push();
        return (r1, r2);
    }

    function pushShortValueDirty() external returns (bytes1, bytes1) {
        assembly { sstore(b.slot, 0x111111111111111111111111111111111111111111111111111111111111223c) }
        b.push(0x33);
        return (b[29], b[30]);
    }
}
