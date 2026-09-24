// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract Types {
    type Price is uint128;

    enum State { Empty, Ready }

    struct Pair {
        uint128 left;
        int64 right;
    }

    function conversions(uint8 x, int16 y, bytes4 z)
        external
        pure
        returns (uint256, int256, bytes32)
    {
        return (uint256(x), int256(y), bytes32(z));
    }

    function located(uint256[] calldata xs)
        external
        pure
        returns (uint256[] memory ys)
    {
        ys = xs;
    }
}
