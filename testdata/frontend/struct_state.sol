// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// A stored struct can contain a function value beside another scalar.
library Keys {
    struct Named {
        function () external f;
        uint8 n;
    }
}

contract StructState {
    Keys.Named named;

    function count() external view returns (uint8) {
        return named.n;
    }
}
