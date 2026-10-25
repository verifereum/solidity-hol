// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Integer boundaries, signed arithmetic, bitwise operators and explicit
// conversions, checked and unchecked.
contract Scalars {
    function increment(uint256 x) public pure returns (uint256) {
        return x + 1;
    }

    function subtract(uint8 x, uint8 y) public pure returns (uint8) {
        return x - y;
    }

    function wrappingSubtract(uint8 x, uint8 y) public pure returns (uint8) {
        unchecked {
            return x - y;
        }
    }

    function multiply(int8 x, int8 y) public pure returns (int8) {
        return x * y;
    }

    function wrappingMultiply(int8 x, int8 y) public pure returns (int8) {
        unchecked {
            return x * y;
        }
    }

    function divide(int8 x, int8 y) public pure returns (int8) {
        return x / y;
    }

    function wrappingDivide(int8 x, int8 y) public pure returns (int8) {
        unchecked {
            return x / y;
        }
    }

    function remainder(int8 x, int8 y) public pure returns (int8) {
        return x % y;
    }

    function power(uint8 x, uint8 e) public pure returns (uint8) {
        return x ** e;
    }

    function wrappingPower(uint8 x, uint8 e) public pure returns (uint8) {
        unchecked {
            return x ** e;
        }
    }

    function signedPower(int8 x, uint8 e) public pure returns (int8) {
        return x ** e;
    }

    function shifts(uint8 x, uint256 s) public pure returns (uint8, uint8) {
        return (x << s, x >> s);
    }

    function signedShift(int8 x, uint256 s) public pure returns (int8) {
        return x >> s;
    }

    function bitwise(uint8 x, uint8 y) public pure returns (uint8, uint8, uint8, uint8) {
        return (x & y, x | y, x ^ y, ~x);
    }

    function signedNot(int8 x) public pure returns (int8) {
        return ~x;
    }

    function signedLess(int8 x, int8 y) public pure returns (bool, bool, bool) {
        return (x < y, x <= y, x >= y);
    }

    function widen(int8 x, uint8 y) public pure returns (int16, uint16, int256) {
        return (int16(x), uint16(y), int256(x));
    }

    function reinterpret(int8 x, uint8 y) public pure returns (uint8, int8) {
        return (uint8(x), int8(y));
    }

    function truncate(uint256 x, int256 y) public pure returns (uint16, int16) {
        return (uint16(x), int16(y));
    }

    function signedToUnsigned(int256 x) public pure returns (uint256) {
        return uint256(x);
    }

    function implicitWidening(uint8 x) public pure returns (uint256) {
        uint16 y = x;
        return y * 1000;
    }

    function boolLogic(bool a, bool b) public pure returns (bool, bool, bool) {
        return (a && b, a || b, a != b);
    }
}
