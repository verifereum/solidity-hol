// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.37;

contract Mappings {
    mapping(uint256 => uint8) private values;
    mapping(int8 => int16) private signedValues;
    mapping(address => bool) private flags;
    mapping(bytes4 => bytes4) private tags;
    mapping(uint256 => mapping(address => uint32)) private nested;
    uint256 private calls;
    mapping(bool => address) private destinations;

    function read(uint256 k) external view returns (uint8) { return values[k]; }
    function set(uint256 k, uint8 v) external returns (uint8) {
        values[k] = v;
        return values[k];
    }
    function distinct(uint256 a, uint256 b) external returns (uint8, uint8) {
        values[a] = 17;
        values[b] = 29;
        return (values[a], values[b]);
    }
    function updates(uint256 k) external returns (uint8, uint8, uint8) {
        values[k] = 5;
        values[k] += 3;
        uint8 old = values[k]++;
        uint8 now = --values[k];
        return (old, now, values[k]);
    }
    function signedKey(int8 k, int16 v) external returns (int16) {
        signedValues[k] = v;
        return signedValues[k];
    }
    function addressKey(address k, bool v) external returns (bool) {
        flags[k] = v;
        return flags[k];
    }
    function bytesKey(bytes4 k, bytes4 v) external returns (bytes4) {
        tags[k] = v;
        return tags[k];
    }
    function nestedKey(uint256 k, address a, uint32 v) external returns (uint32) {
        nested[k][a] = v;
        nested[k][a] += 2;
        return nested[k][a];
    }
    function nextKey() internal returns (uint256) { return calls++; }
    function keyOnce() external returns (uint8, uint8, uint256) {
        values[nextKey()] += 3;
        uint8 old = values[nextKey()]++;
        return (values[0], old, calls);
    }
    function assignmentOrder() external returns (uint8, uint256) {
        values[nextKey()] = uint8(nextKey() + 10);
        return (values[1], calls);
    }
    function compoundOrder() external returns (uint8, uint256) {
        values[nextKey()] += uint8(nextKey() + 3);
        return (values[1], calls);
    }
    function nestedOnce() external returns (uint32, uint256) {
        nested[nextKey()][address(uint160(nextKey()))] += 1;
        return (nested[0][address(uint160(1))], calls);
    }
    function boolKey(bool k, address v) external returns (address) {
        destinations[k] = v;
        return destinations[k];
    }
    function writeInternal(uint256 k, uint8 v) internal { values[k] = v; }
    function internalVisibility(uint256 k) external returns (uint8) {
        values[k] = 7;
        writeInternal(k, values[k] + 4);
        return values[k];
    }
    function replaceAndReturn(uint256 k) internal returns (uint8) {
        values[k] = 9;
        return 2;
    }
    function compoundSeesRhs(uint256 k) external returns (uint8) {
        values[k] = 4;
        values[k] += replaceAndReturn(k);
        return values[k];
    }
    function rollback(uint256 k, uint8 v) external returns (uint8) {
        writeInternal(k, 42);
        return v + 1;
    }
}
