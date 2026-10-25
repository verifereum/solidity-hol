// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Nested loops and the distinct edges of break, continue and return.
contract Control {
    // Inner break leaves only the inner loop; outer continue skips odd rows.
    function pairs(uint256 n) public pure returns (uint256 count) {
        for (uint256 i = 0; i < n; i++) {
            if (i % 2 == 1) continue;
            for (uint256 j = 0; j < n; j++) {
                if (j > i) break;
                count += 1;
            }
        }
    }

    // Inner continue skips to the inner increment; outer break stops at a
    // threshold.
    function threshold(uint256 n, uint256 limit) public pure returns (uint256 total, uint256 rows) {
        for (uint256 i = 1; i <= n; i++) {
            for (uint256 j = 1; j <= i; j++) {
                if (j == 2) continue;
                total += j;
            }
            rows++;
            if (total >= limit) break;
        }
    }

    // A return from inside two loops leaves the function.
    function find(uint256 n, uint256 target) public pure returns (uint256, uint256) {
        for (uint256 i = 0; i < n; i++) {
            uint256 j = 0;
            while (j < n) {
                if (i * j == target) return (i, j);
                j++;
            }
        }
        return (n, n);
    }

    // continue in a do-while goes to the condition, not to the body.
    function doContinue(uint256 n) public pure returns (uint256 i, uint256 odd) {
        do {
            i++;
            if (i % 2 == 0) continue;
            odd++;
        } while (i < n);
    }

    // break in a do-while nested in a while.
    function nestedDo(uint256 n) public pure returns (uint256 outer, uint256 inner) {
        while (outer < n) {
            outer++;
            uint256 k = 0;
            do {
                k++;
                if (k > outer) break;
                inner++;
            } while (true);
        }
    }

    // A for loop with neither condition nor increment, left by break.
    function forever(uint256 n) public pure returns (uint256 i) {
        for (;;) {
            if (i >= n) break;
            i += 3;
        }
    }

    function classify(int256 x) public pure returns (uint8) {
        if (x < 0) {
            return 0;
        } else if (x == 0) {
            return 1;
        } else if (x < 100) {
            return 2;
        }
        return 3;
    }

    // Checked arithmetic in a loop panics at the first overflowing iteration.
    function overflowInLoop(uint8 start) public pure returns (uint8 x) {
        x = start;
        for (uint256 i = 0; i < 10; i++) {
            x *= 2;
        }
    }
}
