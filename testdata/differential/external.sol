// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

interface IToken {
    function balanceOf(address account) external view returns (uint256);
    function mint(address to, uint256 value) external;
    function transfer(address to, uint256 value) external returns (bool);
}

interface ISelf {
    function bump(uint256 by) external returns (uint256);
    function echoValue() external payable returns (uint256);
}

// Declares this contract's bump as view, so a call through it is a STATICCALL.
interface IView {
    function bump(uint256 by) external view returns (uint256);
}

// High-level calls: to a token at a given address, and back into this
// contract, whose code then runs as bytecode.
contract Caller {
    event Paid(address indexed to, uint256 balance);

    uint256 private calls;

    function pay(address token, address to, uint256 value) external returns (uint256) {
        bool ok = IToken(token).transfer(to, value);
        require(ok, "transfer failed");
        calls += 1;
        uint256 balance = IToken(token).balanceOf(to);
        emit Paid(to, balance);
        return balance;
    }

    function mintVia(address token, address to, uint256 value) external {
        IToken(token).mint(to, value);
        calls += 1;
    }

    function balanceVia(address token, address account) external view returns (uint256) {
        return IToken(token).balanceOf(account);
    }

    function bump(uint256 by) external returns (uint256) {
        calls += by;
        return calls;
    }

    // The call's storage write is seen after it returns.
    function bumpSelf(uint256 by) external returns (uint256) {
        uint256 seen = ISelf(address(this)).bump(by);
        return seen + calls;
    }

    // The static call's storage write halts the callee, so this reverts.
    function bumpStatic(uint256 by) external view returns (uint256) {
        return IView(address(this)).bump(by);
    }

    function echoValue() external payable returns (uint256) {
        return msg.value;
    }

    function forward(uint256 amount) external payable returns (uint256) {
        return ISelf(address(this)).echoValue{value: amount}();
    }
}
