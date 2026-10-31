// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract StorageStructs {
    struct Packed {
        uint8 small;
        int16 signedValue;
        bytes3 tag;
        bool flag;
    }
    struct Nested {
        uint8 head;
        Packed inner;
        uint8 tail;
    }
    struct Containers {
        uint8 head;
        mapping(uint256 => Packed) mapped;
        Packed[2] fixedItems;
        Packed[] dynamicItems;
        uint8[35] numbers;
        uint8[] dynamicNumbers;
        mapping(uint256 => uint8) values;
        uint8 tail;
    }
    uint8 beforeStruct;
    Packed item;
    uint8 afterStruct;
    Nested nested;
    mapping(uint256 => Packed) mapped;
    Packed[2] fixedItems;
    Packed[] dynamicItems;
    Containers containers;
    uint256 counter;
    Nested[2] nestedItems;
    mapping(uint256 => Nested) nestedMapped;
    Containers[2] containerItems;

    function put(uint8 x, int16 y, bytes3 z, bool b)
        public returns (uint8, int16, bytes3, bool)
    {
        item.small = x;
        item.signedValue = y;
        item.tag = z;
        item.flag = b;
        return (item.small, item.signedValue, item.tag, item.flag);
    }

    function smallPut(uint8 x) public returns (uint8) {
        item.small = x;
        return item.small;
    }

    function nestedPut(uint8 x) public returns (uint8, uint8, uint8) {
        nested.head = 9;
        nested.inner.small = x;
        nested.tail = 11;
        return (nested.head, nested.inner.small, nested.tail);
    }

    function mappedPut(uint256 key, int16 x) public returns (int16) {
        mapped[key].signedValue = x;
        return mapped[key].signedValue;
    }

    function fixedPut(uint256 i, bytes3 x) public returns (bytes3) {
        fixedItems[i].tag = x;
        return fixedItems[i].tag;
    }

    function dynamicPut(uint256 i, uint8 x) public returns (uint8) {
        dynamicItems[i].small = x;
        return dynamicItems[i].small;
    }

    function containerPut(uint256 key, uint256 i, uint8 x)
        public returns (uint8, uint8, uint8, uint8, uint8, uint8)
    {
        containers.mapped[key].small = x;
        containers.fixedItems[1].small = x;
        containers.dynamicItems[i].small = x;
        containers.numbers[34] = x;
        containers.dynamicNumbers[i] = x;
        containers.values[key] = x;
        return (containers.mapped[key].small, containers.fixedItems[1].small,
                containers.dynamicItems[i].small, containers.numbers[34],
                containers.dynamicNumbers[i], containers.values[key]);
    }

    function nestedArrayPut(uint256 i, uint8 x) public returns (uint8) {
        nestedItems[i].inner.small = x;
        return nestedItems[i].inner.small;
    }

    function nestedMappedPut(uint256 key, bytes3 x) public returns (bytes3) {
        nestedMapped[key].inner.tag = x;
        return nestedMapped[key].inner.tag;
    }

    function arrayMappingPut(uint256 key, uint8 x) public returns (uint8) {
        containerItems[1].mapped[key].small = x;
        return containerItems[1].mapped[key].small;
    }

    function next() internal returns (uint256) {
        return counter++;
    }

    function captureOnce() public returns (uint256, uint8, uint8) {
        counter = 0;
        fixedItems[next()].small += 3;
        uint8 old = fixedItems[next()].small++;
        return (counter, fixedItems[0].small, old);
    }

    function assignmentOrder() public returns (uint256) {
        counter = 0;
        fixedItems[next()].small = uint8(next() + 10);
        return counter;
    }

    function bump(uint256 key) internal returns (uint8) {
        return ++mapped[key].small;
    }

    function acrossCalls(uint256 key) public returns (uint8, uint8) {
        mapped[key].small = 5;
        uint8 seen = bump(key);
        mapped[key].small *= 2;
        return (seen, mapped[key].small);
    }

    function overflow() public {
        item.small = 255;
        ++item.small;
    }

    function bounds(uint256 i) public returns (uint8) {
        item.small = 99;
        return fixedItems[i].small;
    }

    function dynamicBounds(uint256 i) public returns (uint8) {
        item.small = 99;
        return dynamicItems[i].small;
    }

    function lengths() public view returns (uint256, uint256, uint256) {
        return (containers.fixedItems.length, containers.dynamicItems.length,
                containers.dynamicNumbers.length);
    }
}
