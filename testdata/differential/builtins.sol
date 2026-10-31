// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract Builtins {
    uint256 counter;
    uint256 marker;

    function requirePlain(bool ok) public returns (uint256) {
        marker = 22;
        require(ok);
        return marker;
    }

    function requireMessage(bool ok) public returns (uint256) {
        require(condition(ok), "literal message");
        return counter;
    }

    function requireEmpty(bool ok) public pure {
        require(ok, "");
    }

    function requireUnicode(bool ok) public pure {
        require(ok, unicode"é🙂");
    }

    function requireLong(bool ok) public pure {
        require(ok, "01234567890123456789012345678901234567890123456789012345678901234");
    }

    function assertion(bool ok) public returns (uint256) {
        marker = 33;
        assert(condition(ok));
        return counter;
    }

    function bareRevert() public {
        counter = 44;
        revert();
    }

    function emptyRevert() public pure { revert(""); }
    function messageRevert() public pure { revert("literal message"); }
    function unicodeRevert() public pure { revert(unicode"é🙂"); }
    function boundaryRevert() public pure { revert("01234567890123456789012345678901"); }
    function longRevert() public pure {
        revert("01234567890123456789012345678901234567890123456789012345678901234");
    }
    function nulRevert() public pure { revert("a\x00b"); }
    function hexRevert() public pure { revert(hex"c3a90061"); }

    function condition(bool ok) internal returns (bool) {
        counter++;
        return ok;
    }

    function internalRequire(bool ok) internal {
        counter = 55;
        require(ok, "inner");
        counter++;
    }

    function propagation(bool ok) public returns (uint256, uint256) {
        marker = 66;
        internalRequire(ok);
        marker++;
        return (counter, marker);
    }

    function internalAssert() internal { assert(false); }
    function assertPropagation() public { marker = 77; internalAssert(); }
    function internalRevert() internal { revert("inner revert"); }
    function revertPropagation() public { marker = 88; internalRevert(); }

    function conditionPanic(uint256 divisor) public {
        marker = 99;
        require(1 / divisor == 0, "condition false");
    }

    function localCondition() public pure returns (uint256) {
        uint256 i = 0;
        require(i++ == 0, "local");
        assert(i++ == 1);
        return i;
    }
}
