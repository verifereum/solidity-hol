// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Internal calls, recursion, multiple returns, tuples and the order of
// arguments, operands and assignments.
contract Calls {
    function isEven(uint256 n) public pure returns (bool) {
        if (n == 0) return true;
        return isOdd(n - 1);
    }

    function isOdd(uint256 n) public pure returns (bool) {
        if (n == 0) return false;
        return isEven(n - 1);
    }

    function fib(uint256 n) public pure returns (uint256) {
        if (n < 2) return n;
        return fib(n - 1) + fib(n - 2);
    }

    function ackermann(uint256 m, uint256 n) public pure returns (uint256) {
        if (m == 0) return n + 1;
        if (n == 0) return ackermann(m - 1, 1);
        return ackermann(m - 1, ackermann(m, n - 1));
    }

    function pair(uint256 x, uint256 y) public pure returns (uint256, uint256) {
        return (x, y);
    }

    function minMax(uint256 x, uint256 y) public pure returns (uint256 lo, uint256 hi) {
        if (x < y) {
            (lo, hi) = pair(x, y);
        } else {
            (lo, hi) = pair(y, x);
        }
    }

    function narrowSum(uint8 x, uint8 y) public pure returns (uint8) {
        return x + y;
    }

    // Arguments are evaluated left to right.
    function argumentEffects(uint256 i) public pure returns (uint256, uint256) {
        return pair(i++, i++);
    }

    // Operands are evaluated left to right: at 200 the left call overflows
    // (0x11) before the right operand divides by zero (0x12).
    function operandPanics(uint8 x) public pure returns (uint8) {
        return narrowSum(x, x) + uint8(100 / (x - 200));
    }

    // Writes go right to left, so the leftmost target is written last.
    function sameTarget(uint256 a, uint256 b) public pure returns (uint256 x) {
        (x, x) = (a, b);
    }

    function rotate(uint256 a, uint256 b, uint256 c) public pure returns (uint256, uint256, uint256) {
        (a, b, c) = (b, c, a);
        return (a, b, c);
    }

    // The right-hand side is evaluated into fresh values before any write.
    function swapThroughCall(uint256 a, uint256 b) public pure returns (uint256, uint256) {
        (a, b) = pair(b, a);
        return (a, b);
    }

    function holes(uint256 x) public pure returns (uint256) {
        (, uint256 b) = pair(x, x + 1);
        (uint256 c, ) = pair(b * 2, 0);
        return c;
    }

    // The return value is converted to the declared return type.
    function widenResult(uint8 x) public pure returns (uint256) {
        return narrowSum(x, x);
    }

    function prefixPostfix(uint256 x) public pure returns (uint256, uint256, uint256) {
        uint256 a = x++;
        uint256 b = ++x;
        uint256 c = x--;
        return (a, b, c + x);
    }

    function decrementUnderflow(uint256 x) public pure returns (uint256) {
        x--;
        return x;
    }

    function wrappingDecrement(uint256 x) public pure returns (uint256) {
        unchecked {
            x--;
        }
        return x;
    }
}
