// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Where each revert writes its payload: solc's revertWithError writes a
// custom error whose parameters are all value types, and whose encoding fits
// below 0x80 with the selector, at scratch 0, and every other error at the
// free memory pointer; a panic writes its selector and code at scratch 0.
contract RevertPayloads {
    error None();
    error Three(uint256 a, uint256 b, uint256 c);
    error Values(bytes32 a, bool b, int8 c);
    error Four(uint256 a, uint256 b, uint256 c, uint256 d);
    error Text(string s);
    error Pair(uint256[2] a);

    function none() external pure {
        revert None();
    }

    function three(uint256 x) external pure {
        revert Three(x, 2, 3);
    }

    function values() external pure {
        revert Values(bytes32(uint256(0xab)), true, -1);
    }

    function four(uint256 x) external pure {
        revert Four(x, 2, 3, 4);
    }

    function text(string memory s) external pure {
        revert Text(s);
    }

    function pair() external pure {
        uint256[2] memory a = [uint256(5), 6];
        revert Pair(a);
    }

    function message() external pure {
        revert("hello");
    }

    function requireMessage(bool c) external pure {
        require(c, "nope");
    }

    function requireThree(bool c) external pure {
        require(c, Three(1, 2, 3));
    }

    function requireFour(bool c) external pure {
        require(c, Four(1, 2, 3, 4));
    }

    function requireText(bool c, string memory s) external pure {
        require(c, Text(s));
    }

    function empty() external pure {
        revert();
    }

    function asserted(uint256 x) external pure {
        assert(x == 0);
    }

    function increment(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }

    // The panic happens in an internal function, after an allocation.
    function overflow(uint256 x) external pure returns (uint256) {
        bytes memory b = new bytes(3);
        return increment(x) + b.length;
    }
}
