// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// An ERC20-shaped token: balances and allowances keyed by msg.sender, with
// Transfer and Approval events.
contract Token {
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    mapping(address => uint256) private balances;
    mapping(address => mapping(address => uint256)) private allowances;
    uint256 private supply;

    function totalSupply() external view returns (uint256) {
        return supply;
    }

    function balanceOf(address account) external view returns (uint256) {
        return balances[account];
    }

    function allowance(address owner, address spender) external view returns (uint256) {
        return allowances[owner][spender];
    }

    function mint(address to, uint256 value) external {
        require(to != address(0), "mint to zero");
        supply += value;
        balances[to] += value;
        emit Transfer(address(0), to, value);
    }

    function transfer(address to, uint256 value) external returns (bool) {
        move(msg.sender, to, value);
        return true;
    }

    function approve(address spender, uint256 value) external returns (bool) {
        allowances[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }

    function transferFrom(address from, address to, uint256 value) external returns (bool) {
        uint256 current = allowances[from][msg.sender];
        require(current >= value, "insufficient allowance");
        allowances[from][msg.sender] = current - value;
        move(from, to, value);
        return true;
    }

    function move(address from, address to, uint256 value) private {
        require(to != address(0), "transfer to zero");
        uint256 balance = balances[from];
        require(balance >= value, "insufficient balance");
        balances[from] = balance - value;
        balances[to] += value;
        emit Transfer(from, to, value);
    }
}
