// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.37;

// Inheritance and virtual dispatch: an interface base declares the event and
// the external function, an abstract base calls virtual hooks that the
// derived contract implements or overrides, and the derived contract
// overrides a public function, which the dispatcher must reach instead of the
// base's.
interface ICounter {
    event Bumped(address indexed by, uint256 total);

    function bump(uint256 amount) external returns (uint256);
}

abstract contract Context {
    function _sender() internal view virtual returns (address) {
        return msg.sender;
    }

    // Names Context._sender, which runs the most derived override.
    function _who() internal view returns (address) {
        return _sender();
    }
}

abstract contract Counter is Context, ICounter {
    uint256 internal total;
    mapping(address => uint256) internal counts;

    function bump(uint256 amount) public virtual returns (uint256) {
        _update(_who(), _scale(amount));
        return total;
    }

    function peek(address account) public view virtual returns (uint256) {
        return counts[account];
    }

    function _scale(uint256 amount) internal virtual returns (uint256);

    function _sender() internal view virtual override returns (address) {
        return address(0);
    }

    function _update(address by, uint256 amount) internal virtual {
        total += amount;
        counts[by] += amount;
        emit Bumped(by, total);
    }
}

contract Doubling is Counter {
    uint256 private calls;

    function peek(address account) public view override returns (uint256) {
        return counts[account] + calls;
    }

    function _scale(uint256 amount) internal override returns (uint256) {
        calls += 1;
        return 2 * amount;
    }

    function _sender() internal view override returns (address) {
        return address(uint160(msg.sender) + 1);
    }
}
