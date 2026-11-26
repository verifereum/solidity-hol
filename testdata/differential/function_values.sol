// SPDX-License-Identifier: MIT
pragma solidity >=0.8.0;

library FunctionValueLibrary {
    function twice(uint256 value) internal pure returns (uint256) {
        return value * 2;
    }
}

contract FunctionValues {
    using FunctionValueLibrary for uint256;

    struct Entry {
        uint8 tag;
        function(uint256) internal pure returns (uint256) operation;
    }

    uint8 private low;
    function(uint256) internal pure returns (uint256) private current;
    uint8 private high;
    function(uint256) internal pure returns (uint256) private unset;
    Entry private entry;
    function(uint256) internal pure returns (uint256)[] private operations;
    mapping(uint256 => function(uint256) internal pure returns (uint256)) private byKey;
    function(uint256) internal pure returns (uint256) private transient temporary;

    constructor() {
        low = 7;
        current = increment;
        high = 9;
    }

    function increment(uint256 value) internal pure returns (uint256) {
        return value + 1;
    }

    function double(uint256 value) internal pure returns (uint256) {
        return value * 2;
    }

    function readPacked(uint256 value) external view returns (uint8, uint256, uint8) {
        return (low, current(value), high);
    }

    function readUnset(uint256 value) external view returns (uint256) {
        return unset(value);
    }

    function clear() external returns (uint8, bool, uint8) {
        delete current;
        return (low, current != increment, high);
    }

    function writeAggregates(uint256 value) external returns (uint256, uint256, uint256) {
        entry = Entry(3, increment);
        operations.push(double);
        byKey[3] = increment;
        return (entry.operation(value), operations[0](value), byKey[3](value));
    }

    function memoryAggregates(uint256 value) external pure returns (uint256, uint256) {
        function(uint256) internal pure returns (uint256)[] memory items =
            new function(uint256) internal pure returns (uint256)[](1);
        items[0] = double;
        Entry memory local = Entry(3, increment);
        return (items[0](value), local.operation(value));
    }

    function transientValue(uint256 value) external returns (uint256) {
        temporary = double;
        return temporary(value);
    }

    function select(bool first) internal pure returns (
        function(uint256) internal pure returns (uint256)
    ) {
        return first ? increment : double;
    }

    function invoke(function(uint256) internal pure returns (uint256) operation, uint256 value)
        internal pure returns (uint256)
    {
        return operation(value);
    }

    function higherOrder(uint256 value) external pure returns (bool, bool, uint256) {
        function(bool) internal pure returns (
            function(uint256) internal pure returns (uint256)
        ) choose = select;
        function(function(uint256) internal pure returns (uint256), uint256)
            internal pure returns (uint256) execute = invoke;
        return (choose(true) == increment, choose(true) != choose(false), execute(choose(false), value));
    }

    function assemblyValue(uint256 value, bool invalidate) external pure returns (uint256) {
        function(uint256) internal pure returns (uint256) first = increment;
        function(uint256) internal pure returns (uint256) second = double;
        assembly {
            second := first
            if invalidate { second := or(shl(255, 1), first) }
        }
        return second(value);
    }

    function attached(uint256 value) external pure returns (uint256) {
        return (value.twice)();
    }
}
