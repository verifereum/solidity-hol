// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

contract SelfDestructSource {
    event Halted(uint256 marker);

    uint256 public x;

    constructor(uint8 mode) payable {
        x = 1;
        if (mode == 1) {
            selfdestruct(payable(msg.sender));
            emit Halted(1);
        }
        if (mode == 2) {
            assembly { selfdestruct(caller()) }
            emit Halted(2);
        }
    }

    function sourceDestroy() external payable {
        x = 2;
        selfdestruct(payable(msg.sender));
        emit Halted(3);
    }

    function assemblyDestroy() external payable {
        x = 3;
        assembly { selfdestruct(caller()) }
        emit Halted(4);
    }
}
