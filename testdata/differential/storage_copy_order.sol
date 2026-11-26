// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Storage array assignment resizes the destination, then copies element by
// element against live storage. Cases seed lengths and elements directly, so
// sources can overlap their destinations and headers can be corrupt.
contract StorageCopyOrder {
    struct Pair {
        uint256 a;
        uint256 b;
    }

    uint256[3][] words;
    uint128[6][] packed;
    bytes[] blobs;
    uint8[] small;
    Pair[] pairs;
    uint16[] wide;

    function copyWords(uint256 k) external returns (uint256[3] memory) {
        words[0] = words[k];
        return words[0];
    }

    function copyPacked(uint256 k) external returns (uint128[6] memory) {
        packed[0] = packed[k];
        return packed[0];
    }

    function assignBlobs(bytes[] calldata d) external returns (uint256) {
        blobs = d;
        return blobs.length;
    }

    function clearSmall() external returns (uint256) {
        uint8[] memory empty;
        small = empty;
        return small.length;
    }

    function widenSmall() external returns (uint16[] memory) {
        wide = small;
        return wide;
    }

    function replacePairs() external returns (uint256) {
        Pair[] memory one = new Pair[](1);
        pairs = one;
        return pairs.length;
    }
}
