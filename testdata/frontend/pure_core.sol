// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Pure-subset constructs for the importer and elaborator: locals, internal
// calls, multiple returns, tuples, conversions and every loop form.
contract PureCore {
    function add(uint8 x, uint8 y) public pure returns (uint8) {
        return x + y;
    }

    function wrappingAdd(uint8 x, uint8 y) public pure returns (uint8) {
        unchecked {
            return x + y;
        }
    }

    function count(uint256 n) public pure returns (uint256 c, uint256 i) {
        while (++i < n) {
            if (i % 2 == 1) continue;
            c += 1;
            if (c == 3) break;
        }
    }

    function sum(uint256 n) public pure returns (uint256 s) {
        for (uint256 i = 0; i < n; i++) {
            if (i == 2) continue;
            s += i;
        }
    }

    function doubleUntil(uint256 n) public pure returns (uint256 k) {
        do {
            k += 2;
        } while (k < n);
    }

    function fact(uint256 n) public pure returns (uint256) {
        if (n == 0) return 1;
        return n * fact(n - 1);
    }

    function divmod(uint256 x, uint256 y) public pure returns (uint256, uint256) {
        return (x / y, x % y);
    }

    function swap() public pure returns (uint256 a, uint256 b) {
        (a, b) = divmod(17, 5);
        (a, b) = (b, a);
    }

    function locals(uint256 x) public pure returns (uint256) {
        uint256 doubled = x * 2;
        (uint256 q, uint256 r) = divmod(doubled, 7);
        (, uint256 s) = divmod(q, 3);
        bool keep = q > 0 && r < 7 || s == 0;
        if (!keep) {
            return 0;
        } else {
            return q + r + s;
        }
    }

    function narrow(uint256 x) public pure returns (uint8 r, bool small) {
        small = x < 256;
        r = uint8(x);
    }

    function negate(int8 x) public pure returns (int8) {
        return -x;
    }

    function identity(address a, bytes4 b) public pure returns (address, bytes4) {
        return (a, ~b);
    }
}
