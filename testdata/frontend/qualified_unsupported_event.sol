// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.37;

library UnsupportedEvents {
    event Payload(function () external pure returns (uint256) item);
}

contract QualifiedUnsupportedEvent {
    function supported() external pure returns (uint256) {
        return 7;
    }

    function emitsUnsupported() external {
        emit UnsupportedEvents.Payload(this.supported);
    }
}
