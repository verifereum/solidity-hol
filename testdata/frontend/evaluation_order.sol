// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

contract EvaluationOrder {
    uint256 public counter;
    event Seen(uint256 first, uint256 second);

    function next() internal returns (uint256) {
        counter += 1;
        return counter;
    }

    function binary() external returns (uint256) {
        return next() * 10 + next();
    }

    function arguments() external returns (uint256) {
        return combine(next(), next());
    }

    function emitArguments() external {
        emit Seen(next(), next());
    }

    function combine(uint256 x, uint256 y) internal pure returns (uint256) {
        return x * 10 + y;
    }
}
