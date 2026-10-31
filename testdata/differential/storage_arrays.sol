// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract StorageArrays {
    uint8[32 + 3] packed;
    int16[0x11] signedValues;
    bytes3[12] tags;
    uint24[11][2] rows;
    uint256 counter;
    bool[34] flags;
    address[2] owners;
    uint256[2] wide;

    function lengths() public view returns (uint256, uint256, uint256) {
        return (packed.length, rows.length, rows[0].length);
    }

    function put(uint256 i, uint8 x) public returns (uint8) {
        packed[i] = x;
        return packed[i];
    }

    function get(uint256 i) public view returns (uint8) {
        return packed[i];
    }

    function flagPut(uint256 i, bool x) public returns (bool) {
        flags[i] = x;
        return flags[i];
    }

    function flagGet(uint256 i) public view returns (bool) {
        return flags[i];
    }

    function ownerPut(uint256 i, address x) public returns (address) {
        owners[i] = x;
        return owners[i];
    }

    function widePut(uint256 i, uint256 x) public returns (uint256) {
        wide[i] = x;
        return wide[i];
    }

    function signedPut(uint256 i, int16 x) public returns (int16) {
        signedValues[i] = x;
        return signedValues[i];
    }

    function tagPut(uint256 i, bytes3 x) public returns (bytes3) {
        tags[i] = x;
        return tags[i];
    }

    function rowPut(uint256 r, uint256 i, uint24 x) public returns (uint24) {
        rows[r][i] = x;
        return rows[r][i];
    }

    function next() internal returns (uint256) {
        return counter++;
    }

    function indexEffects() public returns (uint256, uint8, uint8, uint8) {
        counter = 0;
        packed[next()] = 10;
        packed[next()] += 3;
        uint8 old = packed[next()]++;
        uint8 stepped = --packed[next()];
        return (counter, old, stepped, packed[0]);
    }

    function assignmentOrder() public returns (uint256) {
        counter = 0;
        packed[next()] = uint8(next() + 10);
        packed[next()] += uint8(next() + 10);
        return counter;
    }

    function nestedIndices() public returns (uint256, uint24) {
        counter = 0;
        rows[next()][next()] = 7;
        return (counter, rows[0][1]);
    }

    function lengthEffect() public returns (uint256) {
        return rows[next()].length;
    }

    function bump(uint256 i) internal returns (uint8) {
        return ++packed[i];
    }

    function acrossCalls(uint256 i) public returns (uint8, uint8) {
        packed[i] = 5;
        uint8 seen = bump(i);
        packed[i] *= 2;
        return (seen, packed[i]);
    }

    function bounds(uint256 i) public returns (uint8) {
        packed[0] = 99;
        return packed[i];
    }

    function nestedBounds(uint256 r, uint256 i) public returns (uint24) {
        rows[0][0] = 99;
        return rows[r][i];
    }

    function overflow() public {
        packed[32] = 255;
        ++packed[32];
    }

    function lengthOrder() public returns (uint256, uint256, uint256, uint256, uint256) {
        uint256 i = 0;
        uint256 sum = i + rows[i++].length;
        i = 0;
        (uint256 first, uint256 size) = (i, rows[i++].length);
        i = 0;
        uint256 combined = combine(i, rows[i++].length);
        return (sum, first, size, combined, i);
    }

    function combine(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * 100 + b;
    }
}
