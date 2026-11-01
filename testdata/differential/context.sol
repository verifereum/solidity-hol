// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

// Dispatch (payable, nonpayable, receive, fallback) and the call context.
contract Context {
    event Received(address indexed sender, uint256 value);
    event Fallback(uint256 value) anonymous;
    event Noted(uint8 indexed tag, bool flag, bytes32 data);

    uint256 private deposits;
    address private last;

    receive() external payable {
        deposits += msg.value;
        emit Received(msg.sender, msg.value);
    }

    fallback() external payable {
        emit Fallback(msg.value);
    }

    function deposit() external payable returns (uint256) {
        deposits += msg.value;
        last = msg.sender;
        return deposits;
    }

    function self() external view returns (address) {
        return address(this);
    }

    function sender() external view returns (address) {
        return msg.sender;
    }

    function origin() external view returns (address) {
        return tx.origin;
    }

    function blockInfo() external view returns (uint256, uint256, uint256, address) {
        return (block.number, block.timestamp, block.chainid, block.coinbase);
    }

    function note(uint8 tag, bool flag, bytes32 data) external {
        emit Noted(tag, flag, data);
    }

    function narrow(uint8 a, int16 b, bytes2 c, bool d) external pure returns (uint8, int16, bytes2, bool) {
        return (a, b, c, d);
    }
}
