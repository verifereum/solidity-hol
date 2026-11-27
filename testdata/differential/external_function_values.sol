// SPDX-License-Identifier: MIT
pragma solidity >=0.8.0;

interface ExternalFunctionTarget {
    function quote(uint256 x) external view returns (uint256);
    function mutate() external view returns (uint256);
    function ping() external;
}

contract ExternalFunctionValues {
    struct Entry {
        function(uint256) external view returns (uint256) operation;
    }

    uint8 private low;
    function(uint256) external view returns (uint256) public current;
    uint8 private high;
    Entry private entry;
    function(uint256) external view returns (uint256)[] private operations;

    event Callback(
        function(uint256) external view returns (uint256) indexed indexedOperation,
        function(uint256) external view returns (uint256) operation
    );

    constructor(function(uint256) external view returns (uint256) initial) {
        current = initial;
    }

    function quote(uint256 x) external pure returns (uint256) {
        return x + 1;
    }

    function paid(uint256 x) external payable returns (uint256) {
        return x + msg.value;
    }

    function storeAndCall(address target, uint256 x)
        external returns (uint8, address, bytes4, uint256, uint8)
    {
        low = 7;
        current = ExternalFunctionTarget(target).quote;
        high = 9;
        return (low, current.address, current.selector, current(x), high);
    }

    function callLocalPayable(uint256 x) external payable returns (uint256) {
        function(uint256) external payable returns (uint256) operation = this.paid;
        return operation{value: msg.value, gas: 100000}(x);
    }

    function callLocalView(address target) external view returns (uint256) {
        function() external view returns (uint256) operation = ExternalFunctionTarget(target).mutate;
        return operation();
    }

    function callNoReturn(address target) external {
        function() external operation = ExternalFunctionTarget(target).ping;
        operation();
    }

    function compare() external view returns (bool, bool, bool) {
        function(uint256) external view returns (uint256) a = this.quote;
        function(uint256) external view returns (uint256) b = ExternalFunctionTarget(address(this)).quote;
        function(uint256) external pure returns (uint256) unset;
        return (a == b, a != b, this.quote != unset);
    }

    function aggregates(uint256 x) external returns (uint256, address, bytes4) {
        Entry memory item = Entry(this.quote);
        entry = item;
        operations.push(entry.operation);
        return (operations[0](x), operations[0].address, operations[0].selector);
    }

    function echo(function(uint256) external view returns (uint256) operation)
        external returns (function(uint256) external view returns (uint256))
    {
        emit Callback(operation, operation);
        return operation;
    }

    function encode(function(uint256) external view returns (uint256) operation)
        external pure returns (bytes memory, bytes memory)
    {
        return (abi.encode(operation), abi.encodePacked(operation, bytes1(0xab)));
    }

    function encodePackedArray(address target) external view returns (bytes memory) {
        function(uint256) external view returns (uint256)[2][2] memory values;
        values[0][0] = this.quote;
        values[1][1] = ExternalFunctionTarget(target).quote;
        return abi.encodePacked(values);
    }

    function assemble(address target, uint32 selector)
        external view returns (uint256, uint256, address, bytes4)
    {
        function(uint256) external view returns (uint256) operation = this.quote;
        uint256 oldAddress;
        uint256 oldSelector;
        assembly {
            oldAddress := operation.address
            oldSelector := operation.selector
            operation.address := target
            operation.selector := selector
        }
        return (oldAddress, oldSelector, operation.address, operation.selector);
    }
}
