// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract DynamicStorageArrays {
    uint8[] packed;
    int16[] signedValues;
    bytes3[] tags;
    bool[] flags;
    address[] owners;
    uint256[] wide;
    mapping(uint256 => uint8[]) groups;
    uint256 counter;

    function length() public view returns (uint256) { return packed.length; }
    function get(uint256 i) public view returns (uint8) { return packed[i]; }
    function put(uint256 i, uint8 x) public returns (uint8) {
        packed[i] = x;
        return packed[i];
    }
    function update(uint256 i) public returns (uint8, uint8) {
        uint8 old = packed[i]++;
        packed[i] += 2;
        return (old, packed[i]);
    }
    function append(uint8 x) public returns (uint256, uint8) {
        packed.push(x);
        return (packed.length, packed[packed.length - 1]);
    }
    function appendDefault() public returns (uint256, uint8) {
        packed.push();
        return (packed.length, packed[packed.length - 1]);
    }
    function appendLvalue(uint8 x) public returns (uint256, uint8) {
        packed.push() = x;
        return (packed.length, packed[packed.length - 1]);
    }
    function appendUpdate() public returns (uint8, uint256) {
        uint8 old = packed.push()++;
        return (old, packed.length);
    }
    function remove() public returns (uint256) {
        packed.pop();
        return packed.length;
    }
    function regrow() public returns (uint8, uint8, uint256) {
        packed.push(17);
        packed.push(29);
        packed.pop();
        uint8 x = packed.push();
        return (packed[0], x, packed.length);
    }
    function signedAppend(int16 x) public returns (int16, uint256) {
        signedValues.push(x);
        return (signedValues[signedValues.length - 1], signedValues.length);
    }
    function signedRemove() public returns (uint256) {
        signedValues.pop();
        return signedValues.length;
    }
    function tagAppend(bytes3 x) public returns (bytes3, uint256) {
        tags.push(x);
        return (tags[tags.length - 1], tags.length);
    }
    function tagRemove() public returns (uint256) {
        tags.pop();
        return tags.length;
    }
    function flagAppend(bool x) public returns (bool, uint256) {
        flags.push(x);
        return (flags[flags.length - 1], flags.length);
    }
    function ownerAppend(address x) public returns (address, uint256) {
        owners.push(x);
        return (owners[owners.length - 1], owners.length);
    }
    function wideAppend(uint256 x) public returns (uint256, uint256) {
        wide.push(x);
        return (wide[wide.length - 1], wide.length);
    }
    function next() internal returns (uint256) { return counter++; }
    function sideEffects() public returns (uint256, uint8, uint8) {
        groups[next()].push(uint8(next() + 10));
        groups[next()].push() = uint8(next() + 20);
        return (counter, groups[0][0], groups[3][0]);
    }
    function indexEffects() public returns (uint256, uint8, uint8) {
        packed.push(4);
        packed.push(8);
        packed[next()] += uint8(next() + 10);
        return (counter, packed[0], packed[1]);
    }
    function lengthOrder() public returns (uint256, uint256, uint256) {
        uint256 i;
        groups[0].push(7);
        uint256 result = i + groups[i++].length;
        return (result, i, counter);
    }
    function mutationOrder() public returns (uint256, uint256, uint256) {
        uint256 i;
        uint256 result = i + groups[i++].push();
        return (result, i, groups[0].length);
    }
    function argumentMutatesArray() public returns (uint256, uint8, uint8) {
        packed.push(nestedAppend(9));
        return (packed.length, packed[0], packed[1]);
    }
    function popBaseOnce() public returns (uint256, uint256) {
        groups[0].push(7);
        groups[next()].pop();
        return (counter, groups[0].length);
    }
    function nestedAppend(uint8 x) internal returns (uint8) {
        packed.push(x);
        return packed[packed.length - 1];
    }
    function internalVisibility() public returns (uint8, uint256) {
        uint8 x = nestedAppend(41);
        packed[packed.length - 1] += 1;
        return (x, packed.length);
    }
    function rollbackBounds() public returns (uint8) {
        packed.push(55);
        counter = 9;
        return packed[packed.length];
    }
    function rollbackEmptyPop() public {
        packed.push(55);
        counter = 9;
        signedValues.pop();
    }
    function rollbackOverflow() public {
        packed.push(255);
        ++packed[0];
    }
}
