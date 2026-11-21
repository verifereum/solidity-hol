// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// The encoder reach suite's peer: it takes a byte sequence and returns its
// length.
contract ReachPeer {
    function take(bytes calldata b) external pure returns (uint256) {
        return b.length;
    }
}
