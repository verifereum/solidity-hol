// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

struct Leaf_$12_storage {
    uint8 value;
}

contract TopLevelStructs {
    struct Unused {
        uint8 spare;
    }

    Leaf_$12_storage item;
    Leaf_$12_storage[2] items;

    function put(uint256 i, uint8 x) public returns (uint8, uint8) {
        item.value = x;
        items[i].value = x + 1;
        return (item.value, items[i].value);
    }
}
