// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// The creation code's internal dispatch holds only the functions creation
// code names as values: here increment (in the constructor), viaHelper (in a
// function the constructor calls), discarded (a bare expression statement)
// and holed (a discarded tuple component). runtimeOnly is named only by
// deployed code. The constructor overwrites op's reserved memory word with
// the given number and calls through it: the number of a function outside
// the creation dispatch panics with 0x51, as one no function has does. With
// keep set it instead copies that word to a local and back without calling
// it and dumps memory, so a word outside the creation dispatch is still read
// and written as the function it numbers.
contract CreationDispatch {
    function(uint256) internal pure returns (uint256) immutable op;
    uint256 public result;

    constructor(uint256 word, bool keep) {
        op = increment;
        helper();
        discarded;
        (uint256 a, ) = (1, holed);
        assembly { mstore(0x80, word) }
        if (keep) {
            function(uint256) internal pure returns (uint256) kept = op;
            assembly { mstore(0x80, 0) }
            op = kept;
            assembly { revert(0, add(mload(0x40), 0x100)) }
        }
        result = op(a + 4);
    }

    function helper() internal pure returns (function(uint256) internal pure returns (uint256)) {
        return viaHelper;
    }

    function increment(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }

    function viaHelper(uint256 x) internal pure returns (uint256) {
        return 2 * x;
    }

    function discarded(uint256 x) internal pure returns (uint256) {
        return 3 * x;
    }

    function holed(uint256 x) internal pure returns (uint256) {
        return 4 * x;
    }

    function runtimeOnly(uint256 x) internal pure returns (uint256) {
        return 5 * x;
    }

    function useRuntime(uint256 x) external pure returns (uint256) {
        function(uint256) internal pure returns (uint256) f = runtimeOnly;
        return f(x);
    }
}
