// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract StorageReferences {
    struct Item {
        uint128 a;
        uint128 b;
    }

    Item[] public items;
    mapping(address => Item) public byOwner;

    function push(uint128 a, uint128 b) external {
        items.push(Item(a, b));
    }

    function capturedThenPop(uint256 i) external returns (uint128) {
        Item storage p = items[i];
        items.pop();
        return p.a;
    }

    function updateOwner(address owner, uint128 a, uint128 b) external {
        Item storage p = byOwner[owner];
        p.a = a;
        p.b = b;
    }
}
